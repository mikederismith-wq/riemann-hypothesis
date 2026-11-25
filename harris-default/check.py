"""Run the stock default build of the existing Harris–Taylor change merged onto batch 14."""

from collections import Counter
import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import tomllib
import traceback
from types import SimpleNamespace


TEMP = Path(os.environ["RUNNER_TEMP"]).resolve()
OUT = TEMP / "rh-proof-results"
FORK = "https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis"
FORK_GIT = "https://github.com/mikederismith-wq/riemann-hypothesis.git"
BASE = "a18a350c3e5aad997766cff2670b292313e46574"
ORIGINAL_BASE = "27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59"
PRODUCTION = "14c585298be9468fb0c37d00fc5de2165f5daca0"
PRODUCTION_TREE = "4c8a03d31e9d9069e832cb51645aab72be950478"
TREE = "40b317ce0cfc2f0bbafecbd15c0f9b65addfb060"
HARRIS_CHECK = "c61a2dcaf85e1ad4253c0a99362952a1157082d2"
DEFAULT_CHECK = "38e7218a5e0c84d462e5731c06511b5d0be2a421"


def frozen(commit, path, digest):
    f = TEMP / "harris-vetted" / path
    f.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["curl", "-fsSL", "--retry", "2", "--max-time", "60", "-o", f,
                    f"{FORK}/{commit}/{path}"], check=True)
    if hashlib.sha256(f.read_bytes()).hexdigest() != digest:
        raise ValueError(f"frozen harness input differs: {path}")
    return f


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    lib = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(lib)
    return lib


def exact_tree(src, project, work, ks, case):
    # Regenerate the complete tracked tree from upstream's index, including every
    # path outside src. The Lean inputs are the same files whose blobs we hash here.
    subprocess.run(["git", "fetch", "-q", "--depth=1", "--filter=tree:0", "--no-tags",
                    FORK_GIT, PRODUCTION], cwd=src, check=True)
    def git(*args, env=None):
        return subprocess.check_output(["git", *args], cwd=src, env=env, text=True).strip()
    commit = git("cat-file", "-p", PRODUCTION).split("\n\n", 1)[0].splitlines()
    if f"tree {PRODUCTION_TREE}" not in commit or [x for x in commit if x.startswith("parent ")] != ["parent " + ORIGINAL_BASE]:
        raise ValueError("wrong production commit or parent")
    index = {**os.environ, "GIT_INDEX_FILE": str(work / "production.index")}
    git("read-tree", BASE, env=index)
    for n in case["removed"]:
        path = Path("src") / ks.rel(n)
        if (project / path).exists():
            raise ValueError(f"removed source still exists: {n}")
        git("update-index", "--force-remove", "--", str(path), env=index)
    path = Path("src") / ks.rel(case["survivor"])
    blob = git("hash-object", "-w", str(project / path))
    git("update-index", "--add", "--cacheinfo", f"100644,{blob},{path}", env=index)
    # Unchanged blobs outside the verified sparse checkout may be lazily fetched.
    # The index already carries their exact base object IDs.
    if git("write-tree", "--missing-ok", env=index) != TREE:
        raise ValueError("candidate files do not reconstruct the verified batch-14 merge tree")


def main():
    OUT.mkdir(exist_ok=True)
    stage = module("harris_downstream", frozen(HARRIS_CHECK, "ks-downstream/check.py",
                   "9d2880e4d6dd4313ab32d1bf3f3e7aa4464818b61fe80cf1e0e2d3320f873016"))
    for name, digest in stage.LOCAL_ASSETS.items():
        frozen(HARRIS_CHECK, "ks-downstream/" + name, digest)
    full = module("stock_default", frozen(DEFAULT_CHECK, "tieops-default/check.py",
                  "03391e75074066cb9e45d3eb249043a1112d95521a6aa15afa74693cc2a93de7"))
    worker = frozen(DEFAULT_CHECK, "tieops-default/worker.py",
                    "2cd2980eea1e49621e28a2d6c7651c6aebcc3074293caa83e399bedce7158f18")
    ks = stage.setup()
    ks.ROOT.mkdir()
    support = ks.module("harris_support", ks.checked_file(ks.PROOF_COMMIT, "proof-bench/proof.py", ks.PROOF_HASH))
    host = ks.module("harris_host", ks.checked_file(ks.SUPPORT_COMMIT, "bench/quick-cache.py", ks.SUPPORT_HASH))
    timer = ks.checked_file(ks.PROOF_COMMIT, "proof-bench/lean-timer.py", ks.TIMER_HASH)
    host.STATE, host.REPORT = ks.ROOT, OUT
    case = json.loads((stage.META / "case.json").read_text())
    if case["revision"] != ORIGINAL_BASE or len(case["descendants"]) != 15 or len(case["removed"]) != 2:
        raise ValueError("incorrect frozen Harris–Taylor case")
    src = ks.ROOT / "main"
    stage.vm("initial")
    toolchain = host.toolchain()
    host.checkout(src, BASE, ["src", "scripts", *support.CFG], 1)
    ci = host.load("harris_ci", src / "scripts/ci-build.py")
    prepare = host.load("harris_prepare", src / "scripts/ci-prepare.py")
    ci.validate_inputs(src, ci.DEPENDENCIES)
    mp, mf, rec = support.inputs(src, ci, prepare, BASE)
    if (rec["build_exit_code"] != 0 or rec["candidate_tree"] != "8a364f3f3bcdae0cb0e0c11daa2cf03a01462811" or
            rec["source_tree"] != "cd27ae6abae1e26741a3b6fcf20f233f0a6c0789" or
            rec["module_manifest_sha256"] != "d97ee858aae28eff224e33386529a02b300d544878ec91046a698278fe19daa2" or
            rec["map_sha256"] != "3d42b2e4c52993c56d04346d12f8cc4d7628f54b4251d98cfa6b1323df6d20ea"):
        raise ValueError("incorrect successful main build or verified artifact manifest")
    packages = support.packages(host, src, ci, toolchain)
    empty = io.BytesIO()
    with tarfile.open(fileobj=empty, mode="w"):
        pass
    ks.run("docker", "import", "-", "rh-bench-empty:local", input=empty.getvalue())
    lean = toolchain / "bin/lean"
    lean.rename(toolchain / "bin/lean-real")
    shutil.copyfile(timer, toolchain / "bin/lean-timed")
    (toolchain / "bin/lean-timed").chmod(0o755)
    shutil.copyfile(worker, lean)
    lean.chmod(0o755)
    with tempfile.TemporaryDirectory(prefix="harris-default-", dir=ks.ROOT) as tmp:
        work = Path(tmp)
        project = ks.variant(support, "new", work, src, case)
        exact_tree(src, project, work, ks, case)
        graph = stage.source_graph(project / "src")
        defaults = full.default_modules(tomllib.loads((project / "lakefile.toml").read_text()), graph, support.cone)
        retired = set(case["removed"])
        root = case["survivor"]
        reverse = ks.incoming(graph)
        cold = support.cone(reverse, [root])
        rows = {row[0]: row for line in gzip.decompress(mf).splitlines()[1:] if (row := json.loads(line))}
        if (set(rows) - retired != defaults or len(rows) != 59534 or len(defaults) != 59532 or
                set(graph) - defaults != {"Challenge"} or cold != {root, *case["descendants"]} or
                sorted(reverse[root]) != case["direct"] or not cold <= defaults):
            raise ValueError("default target or downstream proof coverage changed")
        warm = defaults - cold
        entries, hashes = prepare.manifest_artifacts(mf, mp, rec, modules=warm)
        if len(entries) != len(warm) or any(entries[rows[n][1]] != rows[n][2] or
                                            hashes[rows[n][2]] != rows[n][3] for n in warm):
            raise ValueError("unverified warm inputs")
        stage.write("expected", dict(base=BASE, production=PRODUCTION, tree=TREE, default_count=len(defaults),
                    unaffected_warm=len(warm), affected_cold=sorted(cold), direct=case["direct"],
                    retired=sorted(retired), production_tree=PRODUCTION_TREE))
        cache, shared, result, control = [work / n for n in ("cache", "downloads", "result", "control")]
        for path in [cache / "artifacts", shared, result, control, project / ".lake/packages"]:
            path.mkdir(parents=True)
        # With just 16 cold proofs, serialize compilers so large importers have the full runner.
        (result / "large-modules.txt").write_text("\n".join(sorted(cold)) + "\n")
        options = SimpleNamespace(baseline_manifest=ks.ROOT / "modules.gz",
                                  baseline_map=ks.ROOT / "outputs.jsonl",
                                  baseline_manifest_sha256=rec["module_manifest_sha256"], baseline_cache=shared)
        overrides = ci.package_overrides(project, control)
        cmd = ks.offline_sandbox(host, toolchain, project, packages, cache, result, control)
        cmd[2:2] = ["--memory=14g", "--memory-swap=16g"]
        stage.vm("before-restore", cmd)
        stage.phase("restore", unaffected=len(warm))
        stage.restore("full", warm, rows, prepare, ci, options, project, cache, shared, cmd)
        lib = project / ".lake/build/lib/lean"
        def public_olean(n):
            return lib / ks.rel(n).with_suffix(".olean")
        if any(public_olean(n).exists() for n in cold | retired):
            raise ValueError("affected or retired outputs were prewarmed")
        stage.vm("after-restore", cmd)
        stage.phase("stock-default-build", cold=len(cold))
        record = full.invoke("harris-default", cmd, result, overrides, limit="90m")
        compilers = record.pop("compilers")
        counts = Counter(r["module"] for r in compilers if r["project"] and r["exit_code"] == 0)
        outputs = {n: stage.digest(public_olean(n)) for n in sorted(cold) if public_olean(n).is_file()}
        interface_digest = hashlib.sha256(json.dumps(outputs, separators=(",", ":"), sort_keys=True).encode()).hexdigest()
        missing_outputs = sorted(n for n in defaults if not public_olean(n).is_file())
        retired_outputs = sorted(n for n in retired if public_olean(n).exists())
        ok = (record["exit_code"] == 0 and record["disk_stop"] is None and record["bounded_workers"] and
              record["compiler_concurrency_peak"] == 1 and len(compilers) == len(cold) and
              counts == Counter({n: 1 for n in cold}) and not missing_outputs and not retired_outputs)
        record.update(matched_default_check=ok, compiler_count=len(compilers), successful=dict(sorted(counts.items())),
                      failed=[r["module"] for r in compilers if r["exit_code"]],
                      external=[r["module"] for r in compilers if not r["project"]],
                      missing_outputs=missing_outputs, retired_outputs=retired_outputs, default_public_outputs=len(defaults)-len(missing_outputs),
                      affected_module_cpu_s=sum(r["cpu_s"] for r in compilers if r["project"] and r["exit_code"] == 0),
                      public_olean_sha256=outputs, public_interface_digest=interface_digest)
        stage.write("default-verdict", record)
        stage.vm("after-default", cmd)
        if not ok:
            raise RuntimeError("stock default build failed the compiler or output checks")
        arm = (project, cmd, result, overrides, sorted(cold))
        stage.compare_interfaces(ks, prepare, cold, rows, arm, cache, case)
        comparison = json.loads((OUT / "importer-interface.json").read_text())
        if len(comparison["removed"]) != 67 or any(
                not comparison["modules"][m]["same_olean"] for m in case["descendants"]):
            raise RuntimeError("unexpected public interface difference against the promoted batch-14 build")
        witness = result / "CheckExports.lean"
        witness.write_text("module\npublic import " + root + "\n#check @GlobalTheory.UPel.HT.realise_isKS\n")
        with (OUT / "public-scalar.log").open("w") as log:
            ks.run(*cmd, "/opt/lean/bin/lake", "--packages", overrides, "env", "/opt/lean/bin/lean", "-R",
                   "/work/result", "/work/result/CheckExports.lean", stdout=log, stderr=subprocess.STDOUT)
        stage.phase("complete", default_public_outputs=len(defaults), cold_checked=len(cold), warm=len(warm),
                    public_scalar=True, aggregate_affected_module_cpu_s=record["affected_module_cpu_s"],
                    default_wall_s=record["elapsed_wall_s"])


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        OUT.mkdir(exist_ok=True)
        (OUT / "error.json").write_text(json.dumps(dict(error=str(exc), traceback=traceback.format_exc()), indent=2))
        raise
