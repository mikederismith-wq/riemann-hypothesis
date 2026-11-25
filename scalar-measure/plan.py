"""Determine the cache boundary and exact expected compiler set for each workload."""
import hashlib
import json
from pathlib import Path
import subprocess


NS = "Development.AbelianVarietyTheory.Proofs.DivisorProofs."
SCALAR = NS + "HarrisTaylorRealiseKodairaSpencerDirectionStatement"
JOINT = NS + "ExistsSqZeroLiftRealisingKs"
UNIVERSAL = NS + "ExistsUniversalTangentHarrisTaylorRepresentingFaStatement"
NAT = NS + "HarrisTaylorHodgeFiltrationNaturality"
ORDGEN = "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OrdGen"
SMOOTH = NS + "SmoothOfRelativeDimensionStatement"
REMOVED_AT_BASE = {NS + "RedPullConstMorVPull", NS + "HarrisTaylorExistsGluedFirstOrderDeformation"}
CHANGED = {SCALAR, JOINT, UNIVERSAL, NAT}
EXPECTED_API_CLIENTS = {ORDGEN, SMOOTH}
OFFICIAL = "27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59"
BASE = "14c585298be9468fb0c37d00fc5de2165f5daca0"
BASE_TREE = "4c8a03d31e9d9069e832cb51645aab72be950478"
PATCH_SHA = "9b8a764f344959d3f4a443a6c2a9e86645cb6100ef409a69aba70525423f9db2"
RECEIPT = {
    "candidate_head": OFFICIAL,
    "candidate_tree": "7a78580d283e03a0bcdbff1e72e709d2157e389a",
    "source_tree": "a31c35b83301bc718b77810110f0289778d51b41",
    "build_receipt_sha256": "01555890ee46122d1df26e8dbdc55f49561973733bcfe3c8ffa4069d5b2b5930",
    "map_sha256": "dfbad839a5423dcffc9b36826d34e54cf26b5b7177b3d9bf7ae4880bb6023c11",
    "module_manifest_sha256": "db39a50d765652f9d55f1eefc711a31b9552ad17704c332c6f099d2f36196ad6",
    "toolchain": "leanprover/lean4:v4.37.0-rc1",
    "build_exit_code": 0,
}


def relative(module):
    return Path("src", *module.split(".")).with_suffix(".lean")


def source_tree(official, project):
    """Hash the complete modified project tree by updating its one changed directory."""
    changes = {relative(n) for n in CHANGED | REMOVED_AT_BASE}
    parents = {p.parent for p in changes}
    if len(parents) != 1:
        raise ValueError("the experimental patch no longer uses one source directory")
    directory = parents.pop()
    replacements = {}
    for path in changes:
        f = project / path
        if f.is_file():
            data = f.read_bytes()
            blob = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
            replacements[path.name.encode()] = b"100644 blob " + blob.encode()
        else:
            replacements[path.name.encode()] = None
    git = ["git", "-C", str(official)]
    while True:
        revision = OFFICIAL if directory == Path(".") else OFFICIAL + ":" + directory.as_posix()
        listing = subprocess.check_output([*git, "ls-tree", "-z", revision])
        entries = {name: value for item in listing.split(b"\0") if item
                   for value, name in [item.split(b"\t", 1)]}
        for name, value in replacements.items():
            if value is None:
                entries.pop(name, None)
            else:
                entries[name] = value
        raw = b"".join(value + b"\t" + name + b"\0" for name, value in entries.items())
        tree = subprocess.check_output([*git, "mktree", "--missing", "-z"], input=raw).strip()
        if directory == Path("."):
            return tree.decode()
        replacements = {directory.name.encode(): b"040000 tree " + tree}
        directory = directory.parent


def closure(graph, seeds):
    result = set()
    todo = [s for s in seeds if s in graph]
    while todo:
        name = todo.pop()
        if name not in result:
            result.add(name)
            todo.extend(d for d in graph[name] if d in graph and d not in result)
    return result


def reverse(graph):
    out = {n: set() for n in graph}
    for n, deps in graph.items():
        for dep in deps:
            if dep in out:
                out[dep].add(n)
    return out


def make_plan(graphs):
    """Preserve every side-exclusive import when finding common warm dependencies."""
    arms = tuple(graphs)
    if set(arms) != {"old", "new"}:
        raise ValueError("both comparison graphs are required")
    rev = {s: reverse(g) for s, g in graphs.items()}
    direct = set()
    for s in arms:
        direct.update(n for root in CHANGED for n in rev[s].get(root, set()) if n not in CHANGED)
    if direct != EXPECTED_API_CLIENTS:
        raise ValueError(f"direct clients changed: {direct ^ EXPECTED_API_CLIENTS}")
    main = {s: closure(g, ["Main"]) for s, g in graphs.items()}
    global_diffs = {s: values - set.intersection(*main.values()) for s, values in main.items()}
    if global_diffs != {"old": set(), "new": {NAT}}:
        raise ValueError(f"unexpected global additions or removals: {global_diffs}")
    affected = {s: closure(rev[s], CHANGED) for s in arms}
    if any(not CHANGED.intersection(graphs[s]) <= main[s] for s in arms):
        raise ValueError("a measured provider is outside the Main proof")
    modes = {}
    for mode in ("aggregate", "ordgen"):
        targets = {
            s: {ORDGEN} if mode == "ordgen" else (CHANGED | direct | global_diffs[s]).intersection(graphs[s])
            for s in arms
        }
        inputs = {s: closure(graphs[s], targets[s]) for s in arms}
        if mode == "ordgen":
            # The ordinary single-target command must rebuild its newly required imports
            # even if an earlier aggregate run or this arm's manifest already provided them.
            warm = set.intersection(*inputs.values()) - set.union(*affected.values())
            cold = {s: inputs[s] - warm for s in arms}
        else:
            # Modules that Main still uses in both arms are normally built once. Time
            # every changed provider, direct consumer and Main-exclusive obligation.
            cold = {s: inputs[s] & (affected[s] | targets[s] | global_diffs[s]) for s in arms}
        modes[mode] = {
            s: {"targets": sorted(targets[s]), "cold": sorted(cold[s]), "inputs": sorted(inputs[s])}
            for s in arms
        }
    # Published artifacts are stock upstream, while the stronger baseline already
    # changed UNIVERSAL. No artifact downstream of a reworked source may be seeded.
    restore = {}
    for s in arms:
        all_inputs = set().union(*(m[s]["inputs"] for m in modes.values()))
        restore[s] = sorted(all_inputs - affected[s] - set(modes["ordgen"][s]["cold"]))
        for n in restore[s]:
            if set(graphs[s][n]) & affected[s]:
                raise ValueError(f"unsafe published artifact {n}")
    return {"workloads": modes, "restore": restore, "direct": sorted(direct),
            "main_counts": {s: len(main[s]) for s in arms},
            "main_changed": {s: sorted(global_diffs[s]) for s in arms}}


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def summary(plan):
    report = {k: plan[k] for k in ("direct", "main_counts", "main_changed")}
    report["restore"] = {s: len(xs) for s, xs in plan["restore"].items()}
    for mode, by_arm in plan["workloads"].items():
        report[mode] = {s: {"targets": w["targets"], "cold": w["cold"], "inputs": len(w["inputs"])}
                        for s, w in by_arm.items()}
    report["plan_sha256"] = digest(plan)
    return report
