"""Determine the cache boundary and exact expected compiler set for each workload."""
import hashlib
import json
from pathlib import Path
import subprocess


NS = "Development.AbelianVarietyTheory.Proofs.DivisorProofs."
SCALAR = NS + "HarrisTaylorRealiseKodairaSpencerDirectionStatement"
JOINT = NS + "ExistsSqZeroLiftRealisingKs"
UNIVERSAL = NS + "ExistsUniversalTangentHarrisTaylorRepresentingFaStatement"
COMMON = NS + "HarrisTaylorExistsSquareZeroLiftOfFiltration"
ORDGEN = "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OrdGen"
SMOOTH = NS + "SmoothOfRelativeDimensionStatement"
REMOVED_AT_BASE = {NS + "RedPullConstMorVPull", NS + "HarrisTaylorExistsGluedFirstOrderDeformation"}
CHANGED = {SCALAR, JOINT, UNIVERSAL, COMMON}
EXPECTED_API_CLIENTS = {ORDGEN, SMOOTH}
OFFICIAL = "a18a350c3e5aad997766cff2670b292313e46574"
BASE = "14c585298be9468fb0c37d00fc5de2165f5daca0"
BASE_TREE = "40b317ce0cfc2f0bbafecbd15c0f9b65addfb060"
PATCH_SHA = "89f8a3dd5162af62fbd27c1e43643e0ae4df2c2980434e33895034c48769e18d"
RECEIPT = {
    "candidate_head": OFFICIAL,
    "candidate_tree": "8a364f3f3bcdae0cb0e0c11daa2cf03a01462811",
    "source_tree": "cd27ae6abae1e26741a3b6fcf20f233f0a6c0789",
    "build_receipt_sha256": "e93a2e1e1e29e60391e03611986839c0fb9c99c82b7334de39491b2a0623fc73",
    "map_sha256": "3d42b2e4c52993c56d04346d12f8cc4d7628f54b4251d98cfa6b1323df6d20ea",
    "module_manifest_sha256": "d97ee858aae28eff224e33386529a02b300d544878ec91046a698278fe19daa2",
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
    sides = ('old', 'new')
    reverse_graphs = {s: reverse(graphs[s]) for s in sides}
    changed = {SCALAR, JOINT, COMMON}
    external = {s: set().union(*(reverse_graphs[s].get(n, set()) for n in changed)) - changed for s in sides}
    clients = {ORDGEN, SMOOTH, UNIVERSAL}
    if any(external[s] != clients for s in sides):
        raise ValueError(f'changed set of project consumers: {external}')
    mains = {s: closure(graphs[s], ['Main']) for s in sides}
    if mains['old'] - mains['new'] or mains['new'] - mains['old'] != {COMMON}:
        raise ValueError('unexpected change to Main closure')
    modes = {k:{} for k in ['providers','controls']}
    restore = {}
    for s in sides:
        g=graphs[s]; providers=changed & g.keys(); affected=closure(reverse_graphs[s], CHANGED)
        pp=closure(g,providers);cp=closure(g,clients)
        if (pp & affected) != providers or (cp & affected) - providers != clients:
            raise ValueError(f'unexpected cold dependencies: {sorted((cp & affected) - providers - clients)}')
        for mode, roots, inputs in [('providers',providers,pp),('controls',clients,cp)]:
            modes[mode][s]={'targets':sorted(roots),'cold':sorted(roots),'inputs':sorted(inputs)}
        restore[s]=sorted((pp | cp)-affected)
        if any(set(g[n]) & affected for n in restore[s]):
            raise ValueError('published artifact would bypass a changed source')
    return {'workloads':modes,'restore':restore,'direct':sorted(clients),
            'main_counts':{s:len(x) for s,x in mains.items()},'main_changed':{'old':[],'new':[COMMON]}}


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
