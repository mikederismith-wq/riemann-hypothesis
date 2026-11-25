"""Fork-only check of removed proof modules, their replacement and its direct importer."""
from collections import defaultdict
import base64
import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import shutil
import statistics
import subprocess
import tarfile
import tempfile
import traceback

HERE = Path(__file__).resolve().parent
TEMP = Path(os.environ["RUNNER_TEMP"]).resolve()
ROOT = TEMP / "rh-proof"
RESULTS = TEMP / "rh-proof-results"
FORK = "https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis"
PROOF_COMMIT = "1e6be6d46906f4b4f891a68a7d493782003c8bab"
PROOF_HASH = "2ab4a3a0bc574bf69e3d41cd5d38395d0f2e1f058b44c46c30677aceefdf804d"
SUPPORT_COMMIT = "c5b7dc99d50b61f102c619ba5634dde9465bf9d6"
SUPPORT_HASH = "dea75b622f5fe5198f9c9141515d93654f2e267329769eb42e020c4ca37b15e6"
TIMER_HASH = "4e6ee472c842640d3611b55ec2f90c0f5f92de992cd0e188d40644d20e4a62c4"
PUBLIC_IMPORTS = re.compile(rb"(?m)^\s*public\s+(?:meta\s+)?import\s+(?:all\s+)?([\w.\x80-\xff]+)")

def run(*args, **kwargs):
    return subprocess.run(list(map(str, args)), check=True, **kwargs)

def digest(path):
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()

def checked_file(commit, name, expected):
    target = ROOT / Path(name).name
    run("curl", "-fsSL", "--retry", "2", "--max-time", "50", "-o", target,
        f"{FORK}/{commit}/{name}")
    if digest(target) != expected:
        raise ValueError(f"unexpected content for {name} at {commit}")
    return target

def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

def write(name, data):
    (RESULTS / name).write_text(json.dumps(data, indent=2) + "\n")

def rel(name):
    return Path(*name.split(".")).with_suffix(".lean")

def public_graph(src):
    return {".".join(p.relative_to(src).with_suffix("").parts):
            [b.decode() for b in PUBLIC_IMPORTS.findall(p.read_bytes())]
            for p in src.rglob("*.lean")}

def incoming(graph):
    edges = {n: [] for n in graph}
    for name, imports in graph.items():
        for dep in imports:
            if dep in edges:
                edges[dep].append(name)
    return edges

def variant(sup, side, work, main, case):
    project = work / side
    project.mkdir()
    for n in sup.CFG:
        shutil.copyfile(main / n, project / n)
    shutil.copytree(main / "src", project / "src", copy_function=os.link)
    early, late = case["split_modules"]
    early_path = project / "src" / rel(early)
    late_path = project / "src" / rel(late)
    if early_path.exists() or digest(late_path) != case["base_survivor_sha256"]:
        raise ValueError("published source differs from the expected split base")
    split_sources = json.loads((HERE / "split-source.json").read_text())
    late_path.unlink()
    for name in case["split_modules"]:
        data = gzip.decompress(base64.b64decode(split_sources[name]))
        if hashlib.sha256(data).hexdigest() != case["split_sha256"][name]:
            raise ValueError(f"wrong source for pending module {name}")
        (project / "src" / rel(name)).write_bytes(data)
    if side == "new":
        data = gzip.decompress(base64.b64decode((HERE / "candidate.patch.b64").read_bytes()))
        if hashlib.sha256(data).hexdigest() != case["patch_sha256"]:
            raise ValueError("unexpected candidate patch digest")
        patch = work / "candidate.patch"
        patch.write_bytes(data)
        run("git", "apply", "--check", patch, cwd=project)
        run("git", "apply", patch, cwd=project)
        for name, expected in case["candidate_sha256"].items():
            if digest(project / "src" / rel(name)) != expected:
                raise ValueError(f"candidate differs in {name}")
        if any((project / "src" / rel(n)).exists() for n in case["removed"]):
            raise ValueError("a retired module survived")
    return project

def offline_sandbox(h, tc, project, packages, cache, results, control):
    cmd = h.sandbox(tc, project, packages, cache, results, control)
    mount = f"{packages}:/work/project/.lake/packages:rw"
    if cmd.count(mount) != 1 or "--network=none" not in cmd or "--interactive" not in cmd:
        raise ValueError("pinned compiler sandbox changed")
    # Leave dependency sources read-only. Allow stock Lake to build or refresh
    # package configuration and build artifacts under their .lake subdirectories.
    cmd[cmd.index(mount)] = f"{packages}:/work/project/.lake/packages:ro"
    for package in sorted(packages.iterdir()):
        hidden = package / ".lake"
        hidden.mkdir(exist_ok=True)
        cmd[2:2] = ["--volume", f"{hidden}:/work/project/.lake/packages/{package.name}/.lake:rw"]
    # ProofWidgets asks Lake to refresh package-lock.json.hash beside its
    # tracked lock file. Give each arm private sidecars and mount its real
    # JS, TypeScript, and package configuration inputs individually read-only.
    widget = packages / "proofwidgets/widget"
    sidecars = results.parent / "widget-sidecars"
    shutil.copytree(widget, sidecars, ignore=shutil.ignore_patterns("node_modules"))
    target = "/work/project/.lake/packages/proofwidgets/widget"
    mounts = ["--volume", f"{sidecars}:{target}:rw"]
    for item in sorted(sidecars.rglob("*")):
        if item.is_file() and item.suffix not in {".hash", ".trace"}:
            relpath = item.relative_to(sidecars)
            mounts.extend(["--volume", f"{widget/relpath}:{target}/{relpath}:ro"])
    if (widget/"node_modules").exists():
        (sidecars/"node_modules").mkdir()
        mounts.extend(["--volume", f"{widget/'node_modules'}:{target}/node_modules:ro"])
    cmd[2:2] = mounts
    return cmd

def measured(sup, arm, roots, label, check_extra=False):
    try:
        return sup.build(arm, roots, RESULTS, label, check_extra=check_extra)
    except Exception:
        log = RESULTS/(label+".log")
        if log.is_file():
            print("\n".join(log.read_text(errors="replace").splitlines()[-60:])[-12000:], flush=True)
        raise

def prepare_arm(side, work, case, base_graph, project, published, sup, h, ci, prep, tc, packages):
    graph = base_graph.copy()
    for n in case["split_modules"]:
        graph[n] = [b.decode() for b in sup.IMPORT.findall((project / "src" / rel(n)).read_bytes())]
    if side == "new":
        for n in case["removed"]:
            del graph[n]
        for n, imports in graph.items():
            if set(case["removed"]).intersection(imports):
                raise ValueError(f"{n} still imports a deleted module")
    rev = incoming(graph)
    if sorted(set(rev[case["survivor"]])) != case["direct"]:
        raise ValueError("direct importers changed")
    if sorted(sup.cone(rev, [case["survivor"]]) - {case["survivor"]}) != case["descendants"]:
        raise ValueError("transitive importers changed")
    spec = case["sides"][side]
    roots = set(spec["roots"])
    deps = sup.cone(graph, roots)
    cold = sup.cone(rev, roots) & deps
    if len(deps) != spec["closure"] or cold != roots:
        raise ValueError(f"unexpected {side} dependency graph: {len(deps)}, {sorted(cold^roots)}")
    warm = deps - cold
    mp, mf, rec = published
    entries, hashes = prep.manifest_artifacts(mf, mp, rec, modules=warm)
    if len(entries) != len(warm):
        raise ValueError(f"cache misses a required committed dependency in {side}")
    shared = ROOT/"compressed"
    prep.downloads(shared, entries, hashes)
    w = work/(side+"-work")
    for p in ["cache/artifacts", "result", "control"]:
        (w/p).mkdir(parents=True)
    (project/".lake/packages").mkdir(parents=True)
    overrides = ci.package_overrides(project, w/"control")
    from types import SimpleNamespace
    opts = SimpleNamespace(baseline_manifest=ROOT/"modules.gz",baseline_map=ROOT/"outputs.jsonl",
                           baseline_manifest_sha256=rec["module_manifest_sha256"],baseline_cache=shared)
    _, jobs, _ = ci.baseline(opts, project, w/"cache", modules=warm)
    if len(jobs) != len(warm):
        raise ValueError("private staging omitted warm archives")
    cmd = offline_sandbox(h, tc, project, packages, w/"cache", w/"result", w/"control")
    run(*cmd, "/opt/lean/bin/leantar", "--jobs", "4", "-f", "-x", "-j", "-",
        text=True, input=json.dumps(jobs))
    write(side+"-graph.json", dict(targets=spec["roots"], warm=sorted(warm),
                                    direct=case["direct"], descendants=case["descendants"]))
    return (project, cmd, w/"result", overrides, sorted(cold)), graph

def public_tables(sup, case, arms, pgraphs):
    # Compare RH declarations supplied by the old/new public import paths. The
    # unchanged intersection comes from identical source and the same archives.
    roots = [case["survivor"], *case["direct"]]
    pub = {side: sup.cone(graph, roots) for side, graph in pgraphs.items()}
    tables = {}
    for side in ("old", "new"):
        other = "new" if side=="old" else "old"
        # Include explicitly touched modules even when their imports are private.
        scanned = sorted((pub[side] - pub[other]) | set(case["sides"][side]["roots"]))
        project, cmd, result, overrides, _ = arms[side]
        (result/"inspect.list").write_text("\n".join(scanned)+"\n")
        shutil.copyfile(HERE/"Public.lean", result/"Public.lean")
        (result/"CheckExports.lean").write_text(
            "module\npublic import "+case["survivor"]+"\n#check @GlobalTheory.UPel.HT.realise_isKS\n")
        witness = RESULTS/(side+"-export-witness.log")
        with witness.open("w") as out:
            run(*cmd, "/opt/lean/bin/lake", "--packages", overrides, "env", "/opt/lean/bin/lean", "-R",
                "/work/result", "/work/result/CheckExports.lean", stdout=out, stderr=subprocess.STDOUT)
        path = RESULTS/(side+"-declarations.jsonl")
        with path.open("w") as out, (RESULTS/(side+"-signatures.stderr")).open("w") as err:
            run(*cmd, "/opt/lean/bin/lean", "--run", "/work/result/Public.lean", "/work/result/inspect.list",
                stdout=out, stderr=err, text=True)
        data = {}
        for line in path.read_text().splitlines():
            record = json.loads(line)
            data[record["name"]] = record
        if not data:
            raise ValueError("no public declarations inspected")
        tables[side] = data
    a, b = tables["old"], tables["new"]
    altered = sorted(n for n in a.keys() & b.keys()
                     if any(a[n][k] != b[n][k] for k in ("typeHash","universeParameters")))
    print("Changed public declaration types", altered, flush=True)
    write("public-interface.json", dict(
        public_project_modules_removed=sorted(pub["old"]-pub["new"]),
        public_project_modules_added=sorted(pub["new"]-pub["old"]),
        declarations_only_in_old_sample=sorted(a.keys()-b.keys()),
        declarations_only_in_new_sample=sorted(b.keys()-a.keys()), changed_types=altered))

def main():
    case = json.loads((HERE/"case.json").read_text())
    ROOT.mkdir()
    RESULTS.mkdir(exist_ok=True)
    sup = module("bench", checked_file(PROOF_COMMIT, "proof-bench/proof.py", PROOF_HASH))
    h = module("host", checked_file(SUPPORT_COMMIT, "bench/quick-cache.py", SUPPORT_HASH))
    timer = checked_file(PROOF_COMMIT, "proof-bench/lean-timer.py", TIMER_HASH)
    h.STATE, h.REPORT = ROOT, RESULTS
    sup.disk("stock toolchain and sources", 32)
    tc = h.toolchain()
    main_project = ROOT/"main"
    h.checkout(main_project, case["revision"], ["src", "scripts", *sup.CFG], 1)
    ci = h.load("ci_build", main_project/"scripts/ci-build.py")
    prep = h.load("ci_prepare", main_project/"scripts/ci-prepare.py")
    ci.validate_inputs(main_project, ci.DEPENDENCIES)
    published = sup.inputs(main_project, ci, prep, case["revision"])
    sup.disk("Mathlib preparation", 22)
    pkgs = sup.packages(h, main_project, ci, tc)
    graph = sup.source_graph(main_project/"src")
    pbase = public_graph(main_project/"src")
    (ROOT/"compressed").mkdir()
    stream = io.BytesIO()
    with tarfile.open(fileobj=stream, mode="w"):
        pass
    run("docker","import","-","rh-bench-empty:local",input=stream.getvalue())
    lean = tc/"bin/lean"
    lean.rename(tc/"bin/lean-real")
    shutil.copyfile(timer, lean)
    lean.chmod(0o755)
    arms, pgraphs, graphs = {}, {}, {}
    with tempfile.TemporaryDirectory(dir=ROOT,prefix="ht-") as td:
        work = Path(td)
        # Fail quickly on a bad candidate proof before timing the large old proof.
        for side in ("new", "old"):
            sup.disk("prepare "+side, 12)
            project = variant(sup, side, work, main_project, case)
            arms[side], graphs[side] = prepare_arm(side, work, case, graph, project, published, sup, h, ci, prep, tc, pkgs)
            pg = pbase.copy()
            if side == "new":
                for n in case["removed"]:
                    del pg[n]
            for n in case["split_modules"]:
                pg[n] = [b.decode() for b in PUBLIC_IMPORTS.findall((project / "src" / rel(n)).read_bytes())]
            pgraphs[side] = pg
            measured(sup, arms[side], case["sides"][side]["roots"], "warm-"+side)
        cones = {s:sup.cone(graphs[s],case["sides"][s]["roots"]) for s in arms}
        write("dependency-delta.json",dict(added=sorted(cones["new"]-cones["old"]),removed=sorted(cones["old"]-cones["new"])))
        # Capture interface failures separately; complete the measurements too.
        signature_failure = None
        try:
            public_tables(sup,case,arms,pgraphs)
        except Exception as e:
            signature_failure = str(e)
            write("signature-error.json",dict(error=str(e),traceback=traceback.format_exc()))
        totals = {"old": [], "new": []}
        wall = {"old": [], "new": []}
        for i,side in enumerate(("old","new","new","old","old","new","new","old")):
            sup.disk(f"trial {i} {side}")
            label=f"{i}-{side}"
            values=measured(sup, arms[side], case["sides"][side]["roots"], label, check_extra=True)
            totals[side].append(values)
            wall[side].append(json.loads((RESULTS/(label+".json")).read_text())["wall_s"])
            write("observations.json",dict(cpu_seconds=totals,workflow_step_seconds=wall))
        summary={s:dict(module_cpu={k:statistics.median(row[k] for row in totals[s]) for k in case["sides"][s]["roots"]},
                        total_compiler_cpu=statistics.median(sum(row.values()) for row in totals[s]),
                        timed_workflow_wall=statistics.median(wall[s])) for s in arms}
        write("medians.json",summary)
        print(json.dumps(summary), flush=True)
        if signature_failure:
            raise ValueError("signature verification failed: "+signature_failure)
        write("phase.json",dict(phase="complete"))

if __name__=="__main__":
    RESULTS.mkdir(exist_ok=True)
    try:
        main()
    except Exception as e:
        write("error.json",dict(error=str(e),traceback=traceback.format_exc()))
        raise
