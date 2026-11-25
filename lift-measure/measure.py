"""Measure one reused filtered object lift on the pinned joint-basis baseline."""
import base64
import collections
import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import tarfile
import traceback
from types import SimpleNamespace

import plan


HERE = Path(__file__).resolve().parent
TEMP = Path(os.environ["RUNNER_TEMP"])
OUT = TEMP / "lift-measure-results"
DRIVER = "79e6b8f8c8442f79968ff5e5dfc3bf4fc3daecdc"
DRIVER_SHA = "74bb741fefdebe233a5b3494ed46150a14bc104cb95d53ff75adab63225dd26d"
FORK = "https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis"


def write(name, data):
    (OUT / name).write_text(json.dumps(data, indent=2) + "\n")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def restore_driver():
    path = TEMP / "ks-measure.py"
    subprocess.run(["curl", "-fsSL", "--retry", "2", "--max-time", "45",
                    "-o", str(path), f"{FORK}/{DRIVER}/ks-bench/measure.py"], check=True)
    if sha(path.read_bytes()) != DRIVER_SHA:
        raise ValueError("unexpected stock-cache bootstrap source")
    spec = importlib.util.spec_from_file_location("ks_driver", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    mod.HERE, mod.RESULTS = HERE, OUT
    return mod


def arm_sources(sup, office, project, side, case):
    project.mkdir()
    for name in sup.CFG:
        shutil.copyfile(office / name, project / name)
    shutil.copytree(office / "src", project / "src", copy_function=os.link)
    for name in plan.REMOVED_AT_BASE:
        (project / plan.relative(name)).unlink()
    survivor = project / plan.relative(plan.UNIVERSAL)
    survivor.unlink()
    survivor.write_bytes(gzip.decompress(base64.b64decode((HERE / "base-universal.lean.gz.b64").read_bytes(), validate=True)))
    if side == "new":
        patch = gzip.decompress(base64.b64decode((HERE / "lift.patch.gz.b64").read_bytes(), validate=True))
        if sha(patch) != plan.PATCH_SHA:
            raise ValueError("incorrect scalar proof overlay")
        for n in (plan.SCALAR, plan.JOINT):
            f = project / plan.relative(n)
            data = f.read_bytes()
            f.unlink()
            f.write_bytes(data)
        subprocess.run(["git", "apply", "--check", "-"], input=patch, cwd=project, check=True)
        subprocess.run(["git", "apply", "-"], input=patch, cwd=project, check=True)
    observed = {n: sha(f.read_bytes()) for n in plan.CHANGED
                if (f := project / plan.relative(n)).is_file()}
    if observed != case["source_sha256"][side]:
        raise ValueError(f"incorrect source in {side}")


def stage(ks, sup, host, ci, prep, project, work, tc, packages, receipt, warm):
    mp, mf, record = receipt
    entries, hashes = prep.manifest_artifacts(mf, mp, record, modules=warm)
    if len(entries) != len(warm):
        raise ValueError("a required official cached dependency is missing")
    compressed = ks.ROOT / "compressed"
    prep.downloads(compressed, entries, hashes)
    for name in ("cache/artifacts", "result", "control"):
        (work / name).mkdir(parents=True)
    (project / ".lake/packages").mkdir(parents=True)
    overrides = ci.package_overrides(project, work / "control")
    opts = SimpleNamespace(baseline_manifest=ks.ROOT / "modules.gz",
                           baseline_map=ks.ROOT / "outputs.jsonl",
                           baseline_manifest_sha256=record["module_manifest_sha256"],
                           baseline_cache=compressed)
    _, jobs, _ = ci.baseline(opts, project, work / "cache", modules=warm)
    if len(jobs) != len(warm):
        raise ValueError("incomplete staging plan")
    cmd = ks.offline_sandbox(host, tc, project, packages, work / "cache", work / "result", work / "control")
    ks.run(*cmd, "/opt/lean/bin/leantar", "--jobs", "4", "-f", "-x", "-j", "-",
           input=json.dumps(jobs), text=True)
    return project, cmd, work / "result", overrides, []


def observed_run(ks, sup, arm, row, label):
    project, _, _, _, _ = arm
    # For OrdGen this purposely evicts every unique prerequisite, but Lake is only
    # asked for +OrdGen; its own dependency scheduler chooses the actual builds.
    sup.clear_targets(project, row["cold"])
    ks.measured(sup, arm, row["targets"], label)
    details = json.loads((OUT / (label + ".json")).read_text())
    records = details["actual_compilers"]
    which = collections.Counter(x["module"] for x in records if x["project"] and x["exit_code"] == 0)
    expected = collections.Counter(row["cold"])
    if which != expected or any(not x["project"] or x["exit_code"] for x in records):
        write(label + "-compiler-mismatch.json", {"observed": dict(which), "expected": dict(expected)})
        raise ValueError(f"{label} compiled an unexpected set of modules")
    cpu = {x["module"]: x["cpu_s"] for x in records}
    return {"cpu_s": sum(cpu.values()), "wall_s": details["wall_s"], "module_cpu_s": cpu,
            "output": {n: files[".olean"]["sha256"] for n, files in details["outputs"].items()}}


def summarize(pairs):
    def values(samples):
        old,new=([row[s] for row in samples] for s in ('old','new'))
        savings=[a-b for a,b in zip(old,new)]
        return {'old':old,'new':new,'paired_savings':savings,'old_median':statistics.median(old),
                'new_median':statistics.median(new),'median_paired_saving':statistics.median(savings)}
    return {metric:values([{s:pair[s][metric] for s in ('old','new')} for pair in pairs])
            for metric in ('cpu_s','wall_s')}


def run_all(ks, sup, arms, frozen, pub):
    modes=frozen['workloads'];out={}
    for side in ('old','new'):
        out[side]=observed_run(ks,sup,arms[side],modes['providers'][side],'warm-providers-'+side)
    write('warm-physical-providers.json',out)
    # Both old and new arms have just rebuilt their physical providers in ordinary Lake.
    # Check all immediate project importers once with their own source and verified outputs.
    clients={s:observed_run(ks,sup,arms[s],modes['controls'][s],'verify-clients-'+s) for s in ('new','old')}
    write('direct-clients.json',clients)
    interface_case={'survivor':plan.UNIVERSAL,'direct':[plan.SCALAR,plan.JOINT,plan.SMOOTH,plan.ORDGEN],
      'sides':{s:{'roots':modes['providers'][s]['targets']+modes['controls'][s]['targets']} for s in arms}}
    ks.public_tables(sup,interface_case,arms,pub)
    api=json.loads((OUT/'public-interface.json').read_text())
    if api['changed_types'] or api['declarations_only_in_old_sample'] or api['declarations_only_in_new_sample'] or api['public_project_modules_removed']:
        raise ValueError('the visible declaration set or signature changed: '+str(api))
    if api['public_project_modules_added'] != [plan.COMMON]:
        raise ValueError('unexpected public import change: '+str(api['public_project_modules_added']))
    for side in arms:
        rows=[json.loads(l) for l in (OUT/(side+'-declarations.jsonl')).read_text().splitlines()]
        if not all(any(row['name']==expected for row in rows) for expected in
                  ('GlobalTheory.HTRealise.realise_core','GlobalTheory.UPel.HT.realise_isKS',
                   'GlobalTheory.T.dualNumberGraphFiltration_isotropic_of_skew',
                   'GlobalTheory.T.mem_hodgeFiltration_iff_dualNumberGraph_reduction',
                   'GlobalTheory.UPel.HT.exists_sqZero_lift_of_fil')):
            raise ValueError('required public declaration is missing')
    pairs=[]
    for i in range(4):
        one={};order=('old','new') if i%2==0 else ('new','old')
        for side in order:
            sup.disk(f'pair {i+1} {side}')
            one[side]=observed_run(ks,sup,arms[side],modes['providers'][side],f'pair-{i+1}-'+side)
            write('partial.json',{'complete_pairs':pairs,'current_pair':one})
        pairs.append(one);write('pairs.json',pairs);write('summary.json',summarize(pairs))
    # Separately quantify an ordinary scalar-only consumer workflow; all additional
    # project prerequisites are the one restored clump member, already charged above.
    controlpairs=[]
    for i in range(2):
        row={};order=('old','new') if i%2==0 else ('new','old')
        for side in order:
            cold=[plan.SCALAR,plan.ORDGEN]+([plan.COMMON] if side=='new' else [])
            row[side]=observed_run(ks,sup,arms[side],{'targets':[plan.ORDGEN],'cold':cold},f'ordgen-{i+1}-'+side)
        controlpairs.append(row);write('ordgen-pairs.json',controlpairs)
    write('ordgen-summary.json',summarize(controlpairs))
    return summarize(pairs)


def main():
    case = json.loads((HERE / "case.json").read_text())
    if (case["official"], case["base"], case["base_tree"], case["patch_sha256"]) != (
            plan.OFFICIAL, plan.OFFICIAL, plan.BASE_TREE, plan.PATCH_SHA):
        raise ValueError("unexpected case revision")
    if case["basis_production_head"] != plan.BASE:
        raise ValueError("unexpected incorporated production patch")
    ks = restore_driver()
    ks.ROOT.mkdir()
    sup = ks.module("scalar_proof", ks.checked_file(ks.PROOF_COMMIT, "proof-bench/proof.py", ks.PROOF_HASH))
    host = ks.module("scalar_host", ks.checked_file(ks.SUPPORT_COMMIT, "bench/quick-cache.py", ks.SUPPORT_HASH))
    timer = ks.checked_file(ks.PROOF_COMMIT, "proof-bench/lean-timer.py", ks.TIMER_HASH)
    host.STATE, host.REPORT, sup.OUT = ks.ROOT, OUT, OUT
    sup.disk("stock toolchain and sources", 32)
    tc = host.toolchain()
    official = ks.ROOT / "main"
    host.checkout(official, plan.OFFICIAL, ["src", "scripts", *sup.CFG], 1)
    ci = host.load("scalar_ci", official / "scripts/ci-build.py")
    prep = host.load("scalar_prepare", official / "scripts/ci-prepare.py")
    quick = host.load("scalar_graph", official / "scripts/quick-check.py")
    ci.validate_inputs(official, ci.DEPENDENCIES)
    receipt = sup.inputs(official, ci, prep, plan.OFFICIAL)
    if any(receipt[2].get(k) != v for k, v in plan.RECEIPT.items()):
        raise ValueError("unexpected batch-14 promoted receipt")
    sup.disk("Mathlib preparation", 22)
    packages = sup.packages(host, official, ci, tc)
    (ks.ROOT / "compressed").mkdir()
    projects, graphs, pub, tree_hashes = {}, {}, {}, {}
    source = official / "src"
    base_graph = {".".join(p.relative_to(source).with_suffix("").parts): quick.imports(p)
                  for p in source.rglob("*.lean")}
    for side in ("old", "new"):
        project = projects[side] = ks.ROOT / ("arm-" + side)
        arm_sources(sup, official, project, side, case)
        graph = base_graph.copy()
        for n in plan.REMOVED_AT_BASE | plan.CHANGED:
            p = project / plan.relative(n)
            if p.is_file():
                graph[n] = quick.imports(p)
            else:
                graph.pop(n, None)
        graphs[side] = graph
        pub[side] = ks.public_graph(project / "src")
        tree_hashes[side] = plan.source_tree(official, project)
    if tree_hashes != {"old": plan.BASE_TREE, "new": case["candidate_tree"]}:
        raise ValueError(f"unexpected complete Git trees: {tree_hashes}")
    write("source-trees.json", tree_hashes)
    frozen = plan.make_plan(graphs)
    if plan.summary(frozen) != case["expected"]:
        raise ValueError("actual source graph differs from the frozen experiment")
    write("verified-plan.json", plan.summary(frozen))
    with io.BytesIO() as stream:
        with tarfile.open(fileobj=stream, mode="w"):
            pass
        ks.run("docker", "import", "-", "rh-bench-empty:local", input=stream.getvalue())
    lean = tc / "bin/lean"
    lean.rename(tc / "bin/lean-real")
    shutil.copyfile(timer, lean)
    lean.chmod(0o755)
    arms = {}
    for s in ("new", "old"):
        sup.disk("prepare " + s, 12)
        arms[s] = stage(ks, sup, host, ci, prep, projects[s], ks.ROOT / ("work-" + s),
                        tc, packages, receipt, set(frozen["restore"][s]))
    report = run_all(ks, sup, arms, frozen, pub)
    write("phase.json", {"phase": "complete", "provider_cpu": report["cpu_s"]})


if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    try:
        main()
    except Exception as exc:
        write("error.json", {"error": str(exc), "traceback": traceback.format_exc()})
        raise
