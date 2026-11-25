"""Kernel-check the unrestricted scalar-realisation API on official batch-13 artifacts."""
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import time
import tomllib
import traceback
from types import SimpleNamespace


HERE = Path(__file__).resolve().parent
TEMP = Path(os.environ["RUNNER_TEMP"]).resolve()
OUT = TEMP / "rh-strong-core-result"
PIN = "27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59"
TARGET = "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFaStatement"
TARGET_BLOB = "931a7dc89aad88d943b931230c430e903d01c055"
TARGET_OLEAN = "9cdedada2d28f8f9c6878e00e2ab6d889f46ea99b910caa625bc32a6a7f4e9cc"
PROBE_HASH = "e21fd813fc213bcb489763f3c61acf9c3a35a3a00170963dfe90d66521759d16"
FORK = "https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis"
DRIVER = "79e6b8f8c8442f79968ff5e5dfc3bf4fc3daecdc"
DRIVER_HASH = "74bb741fefdebe233a5b3494ed46150a14bc104cb95d53ff75adab63225dd26d"
EXPECTED_RECEIPT = {
    "candidate_head": PIN,
    "candidate_tree": "7a78580d283e03a0bcdbff1e72e709d2157e389a",
    "source_tree": "a31c35b83301bc718b77810110f0289778d51b41",
    "build_receipt_sha256": "01555890ee46122d1df26e8dbdc55f49561973733bcfe3c8ffa4069d5b2b5930",
    "map_sha256": "dfbad839a5423dcffc9b36826d34e54cf26b5b7177b3d9bf7ae4880bb6023c11",
    "module_manifest_sha256": "db39a50d765652f9d55f1eefc711a31b9552ad17704c332c6f099d2f36196ad6",
    "toolchain": "leanprover/lean4:v4.37.0-rc1",
    "build_exit_code": 0,
}


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def write(name, obj):
    (OUT / name).write_text(json.dumps(obj, indent=2) + "\n")


def driver():
    path = TEMP / "verified-scalar-driver.py"
    subprocess.run(["curl", "-fsSL", "--retry", "2", "--max-time", "50", "-o", str(path),
                    f"{FORK}/{DRIVER}/ks-bench/measure.py"], check=True)
    if digest(path) != DRIVER_HASH:
        raise ValueError("unexpected cache preparation driver")
    spec = importlib.util.spec_from_file_location("scalar_boot", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main():
    probe = HERE / "StrongScalarProbe.lean"
    if digest(probe) != PROBE_HASH:
        raise ValueError("unexpected Lean example")
    shutil.copyfile(probe, OUT / probe.name)
    ks = driver()
    ks.ROOT.mkdir()
    ks.RESULTS.mkdir(exist_ok=True)
    sup = ks.module("scalar_support", ks.checked_file(ks.PROOF_COMMIT, "proof-bench/proof.py", ks.PROOF_HASH))
    host = ks.module("scalar_host", ks.checked_file(ks.SUPPORT_COMMIT, "bench/quick-cache.py", ks.SUPPORT_HASH))
    host.STATE, host.REPORT = ks.ROOT, OUT
    sup.OUT = OUT
    sup.disk("stock compiler", 32)
    tc = host.toolchain()
    project = ks.ROOT / "main"
    host.checkout(project, PIN, ["src", "scripts", *sup.CFG], 1)
    ci = host.load("scalar_ci", project / "scripts/ci-build.py")
    prep = host.load("scalar_prepare", project / "scripts/ci-prepare.py")
    quick = host.load("scalar_quick", project / "scripts/quick-check.py")
    ci.validate_inputs(project, ci.DEPENDENCIES)
    modpath = Path(*TARGET.split("."))
    if ci.git(project, "rev-parse", f"HEAD:src/{modpath}.lean") != TARGET_BLOB:
        raise ValueError("the source of the imported universal module has changed")
    manifest = HERE / "inputs-pinned.json"
    if digest(manifest) != "3577a8dc5fa2f9d81ca48b6d3ea30a48af0bb4529cc1e594aaaad8f62433e235":
        raise ValueError("input list differs from the verified source scan")
    frozen = json.loads(manifest.read_text())
    sources = frozen["project_import_blob_sha1"]
    if set(quick.imports(probe)) != set(sources) | set(frozen["package_imports"]):
        raise ValueError("Lean input import list changed")
    for mod, source_hash in sources.items():
        if ci.git(project, "rev-parse", "HEAD:src/" + mod.replace(".", "/") + ".lean") != source_hash:
            raise ValueError("unrecognized project source for " + mod)
    shutil.copyfile(manifest, OUT / manifest.name)
    mp, mf, record = sup.inputs(project, ci, prep, PIN)
    if any(record.get(k) != v for k, v in EXPECTED_RECEIPT.items()):
        raise ValueError("unexpected official main receipt")
    wanted = set(quick.dependency_closure(project, [TARGET], maximum=6120))
    entries, hashes = prep.manifest_artifacts(mf, mp, record, modules=wanted)
    if not set(sources) <= wanted or len(wanted) != frozen["expected_closure_count"] or len(entries) != len(wanted):
        raise ValueError("incomplete published import closure")
    write("inputs.json", dict(revision=PIN, source_sha256=PROBE_HASH, imported=TARGET,
                              modules=len(wanted), published_olean_sha256=TARGET_OLEAN))
    print(f"Restoring the {len(wanted)} published project modules imported by the example", flush=True)
    packages = sup.packages(host, project, ci, tc)
    result = ks.ROOT / "result"
    cache = ks.ROOT / "cache"
    shared = ks.ROOT / "compressed"
    control = ks.ROOT / "control"
    for path in [result, cache / "artifacts", shared, control, project / ".lake/packages"]:
        path.mkdir(parents=True, exist_ok=True)
    prep.downloads(shared, entries, hashes)
    overrides = ci.package_overrides(project, control)
    opts = SimpleNamespace(baseline_manifest=ks.ROOT / "modules.gz", baseline_map=ks.ROOT / "outputs.jsonl",
                           baseline_manifest_sha256=record["module_manifest_sha256"], baseline_cache=shared)
    _, jobs, _ = ci.baseline(opts, project, cache, modules=wanted)
    if len(jobs) != len(wanted):
        raise ValueError("incomplete native cache restoration plan")
    layer = io.BytesIO()
    with tarfile.open(fileobj=layer, mode="w"):
        pass
    ks.run("docker", "import", "-", "rh-bench-empty:local", input=layer.getvalue())
    cmd = ks.offline_sandbox(host, tc, project, packages, cache, result, control)
    ks.run(*cmd, "/opt/lean/bin/leantar", "--jobs", "4", "-f", "-x", "-j", "-", input=json.dumps(jobs), text=True)
    root_olean = project / ".lake/build/lib/lean" / modpath.with_suffix(".olean")
    if digest(root_olean) != TARGET_OLEAN:
        raise ValueError("restored universal module differs from the published main output")
    shutil.copyfile(probe, result / probe.name)
    with (project / "lakefile.toml").open("rb") as stream:
        cfg = tomllib.load(stream)
    lean_options = cfg["leanOptions"]
    project_flags = cfg["moreLeanArgs"]
    dev = next(lib for lib in cfg["lean_lib"] if lib["name"] == "Development")
    if (lean_options != {"autoImplicit": False, "relaxedAutoImplicit": False, "maxSynthPendingDepth": 3,
                         "pp": {"unicode": {"fun": True}}, "maxHeartbeats": 4000000}
            or project_flags != ["--tstack=400000"] or dev.get("leanOptions")):
        raise ValueError("effective official Development Lean settings have drifted")
    def flags(opts, prefix=""):
        for key, val in opts.items():
            name = prefix + key
            if isinstance(val, dict):
                yield from flags(val, name + ".")
            else:
                arg = str(val).lower() if isinstance(val, bool) else str(val)
                yield "-D" + name + "=" + arg
    lean_flags = [*project_flags, *flags(lean_options)]
    write("lean-settings.json", {"toolchain": record["toolchain"], "args": lean_flags,
                                 "source": "lakefile.toml", "library": "Development"})
    started = time.monotonic()
    with (OUT / "lean-diagnostics.log").open("w") as log:
        ret = subprocess.run([*cmd, "/opt/lean/bin/lake", "--packages", overrides, "env", "/opt/lean/bin/lean",
                              *lean_flags, "-R", "/work/result", f"/work/result/{probe.name}"], stdout=log, stderr=subprocess.STDOUT)
    write("result.json", dict(revision=PIN, source_sha256=PROBE_HASH, modules_restored=len(wanted),
                              imported_olean_sha256=TARGET_OLEAN, lean_exit_code=ret.returncode,
                              probe_wall_seconds=time.monotonic() - started))
    print((OUT / "lean-diagnostics.log").read_text(), flush=True)
    ret.check_returncode()
    diagnostic = (OUT / "lean-diagnostics.log").read_text()
    success = [line for line in diagnostic.splitlines() if "SCALAR_AUDIT_OK" in line]
    if len(success) != 1 or any("uses 'sorry'" in line for line in diagnostic.splitlines()):
        raise ValueError("the stricter scalar independence/type/axiom audit did not pass")
    write("proof-audit.json", dict(input_sha256=PROBE_HASH, summary=success[0],
                                   direct_entries=diagnostic.count("SCALAR_DIRECT")))


if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    try:
        main()
    except Exception as err:
        write("error.json", dict(error=str(err), traceback=traceback.format_exc()))
        raise
