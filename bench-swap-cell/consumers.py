"""Measure only the six direct importers after warming their exact old/new prerequisites."""
from collections import Counter
from pathlib import Path
from urllib.request import Request, urlopen
import gzip
import hashlib
import json
import statistics
import subprocess
import tempfile

URL = "https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis/"


def facets(h, roots, name, recursive=False):
    module = Path(*name.split("."))
    result = {}
    for label, directory in roots:
        if recursive:
            candidates = directory.rglob(module.name + ".*")
        else:
            candidates = (directory / module.parent).glob(module.name + ".*")
        for f in sorted(candidates):
            if f.is_file():
                suffix = f.name[len(module.name):]
                key = label + suffix
                if key in result:
                    raise ValueError(f"repeated {key} in {name}")
                result[key] = {"bytes": f.stat().st_size, "sha256": h.digest(f)}
    if not {"lib.olean", "lib.olean.private", "lib.ir.sig"} <= result.keys():
        raise ValueError(f"missing compiled facets for {name}: {list(result)}")
    return result


def from_project(h, project, names):
    build = project / ".lake/build"
    dirs = [("lib", build / "lib/lean"), ("ir", build / "ir")]
    return {n: facets(h, dirs, n) for n in sorted(names)}


def official(h, mf, names, toolchain, dest):
    found = {}
    chosen = [r for line in gzip.decompress(mf).decode().splitlines()
              if isinstance(r := json.loads(line), list) and r[0] in names]
    if len(chosen) != len(names):
        raise ValueError("missing B14 official module archive")
    for module, key, archive, digest in chosen:
        suffix = archive.removesuffix(".ltar") + ".art"
        request = Request(URL + suffix, headers={"Accept": "application/octet-stream",
                                                "User-Agent": "RH fork benchmark"})
        with urlopen(request, timeout=90) as src:
            data = src.read()
        if hashlib.sha256(data).hexdigest() != digest:
            raise ValueError(f"wrong official module archive for {module}")
        with tempfile.TemporaryDirectory(dir=h.ROOT) as td:
            work = Path(td)
            target = work / archive
            target.write_bytes(data)
            dirs = [("lib", work / "lib"), ("ir", work / "ir")]
            for _, folder in dirs:
                folder.mkdir()
            job = {"file": str(target), "hash": key, "base": [str(d) for _, d in dirs]}
            subprocess.run([toolchain / "bin/leantar", "--jobs", "1", "-f", "-x", "-j", "-"],
                           check=True, cwd=work, input=json.dumps([job]), text=True)
            found[module] = facets(h, dirs, module, recursive=True)
    h.write(dest / "official-facets.json", found)
    return found


def provenance(roots, users, prior, graph):
    affected = set(roots)
    while True:
        extra = {n for n, ds in graph.items() if affected.intersection(ds)} - affected
        if not extra:
            break
        affected.update(extra)
    names = set(prior["expected"]["old"]["extra"])
    return {"direct": sorted(users), "other_downstream": sorted(names & affected),
            "unaffected_prerequisites": sorted(names - affected)}


def install(h, original_build, here):
    prior = json.loads((here / "producer-receipt.json").read_text())
    config = json.loads((here / "cases.json").read_text())
    if (prior["artifact_sha256"] != "29188bb13aca9576b169f39df940eaa5b4bf4fed04149d411600c542f00e8ba8"
            or prior["revision"] != config["revision"] or prior["pending_head"] != config["pending_head"]):
        raise ValueError("wrong producer benchmark receipt")

    def benchmark(spec, main, graph, published, host, ci, prep, toolchain, packages):
        roots, users = set(spec["targets"]), set(spec["direct_importers"])
        dest = h.OUT / spec["name"]
        dest.mkdir()
        groups = provenance(roots, users, prior, graph)
        extras = set(groups["other_downstream"]) | set(groups["unaffected_prerequisites"])
        all_names = roots | users | extras
        h.write(dest / "compiler-groups.json", groups)
        samples, pairs, arms, first_facets = [], [], {}, {}
        with tempfile.TemporaryDirectory(prefix="swap-consumers-", dir=h.ROOT) as temp:
            for s, patches in spec["variants"].items():
                h.disk(f"initialize {s}", 12)
                arm = h.initialize_arm(Path(temp), s, patches, spec, main, graph, published, host,
                                       ci, prep, toolchain, packages)
                arms[s] = arm
                expect = prior["expected"][s]
                if sorted(arm[-1]) != expect["cold"]:
                    raise ValueError(f"{s} dependency cone differs from producer benchmark")
                original_build(arm, sorted(roots), dest, "producers-" + s)
                prod = json.loads((dest / ("producers-" + s + ".json")).read_text())
                if prod["outputs"] != expect["producer_outputs"]:
                    raise ValueError(f"{s} producer artifacts differ from four-pair receipt")
                original_build(arm, sorted(users), dest, "warm-" + s)
                cold = json.loads((dest / ("warm-" + s + ".json")).read_text())
                counts = Counter(r["module"] for r in cold["actual_compilers"])
                if (cold["outputs"] != expect["importer_outputs"] or set(counts) != users | extras or
                        any(r["exit_code"] or not r["project"] for r in cold["actual_compilers"])
                        or max(counts.values()) != 1):
                    raise ValueError(f"{s} consumer initialization differs from previous proof run")
                first_facets[s] = from_project(h, arm[0], all_names)
                h.write(dest / ("warm-facets-" + s + ".json"), first_facets[s])

            h.disk("pinned B14 official facet comparison")
            official(h, published[1], all_names, toolchain, dest)
            oldcpu = prior["cpu"]["cpu_sum_medians"]["old"]
            gain = oldcpu - prior["cpu"]["cpu_sum_medians"]["new"]
            orders = (("old", "new"), ("new", "old"), ("old", "new"), ("new", "old"))
            for pair, order in enumerate(orders, 1):
                runs = {}
                for s in order:
                    h.disk(f"direct importers pair {pair} {s}")
                    label = f"pair-{pair}-{s}"
                    original_build(arms[s], sorted(users), dest, label, check_extra=True)
                    row = json.loads((dest / (label + ".json")).read_text())
                    if row["outputs"] != prior["expected"][s]["importer_outputs"]:
                        raise ValueError(f"compiled importer interfaces drifted in {label}")
                    if any(not w["project"] or w["exit_code"] for w in row["actual_compilers"]):
                        raise ValueError(f"unexpected compiler worker in {label}")
                    cpu = sum(w["cpu_s"] for w in row["actual_compilers"])
                    current = from_project(h, arms[s][0], all_names)
                    changed = {n: sorted(k for k in set(current[n]) | set(first_facets[s][n])
                                          if current[n].get(k) != first_facets[s][n].get(k))
                               for n in all_names}
                    h.write(dest / (label + "-facet-drift.json"), {n: v for n, v in changed.items() if v})
                    runs[s] = {"cpu_s": cpu, "wall_s": row["wall_s"]}
                    samples.append({"side": s, "pair": pair, **runs[s]})
                pairs.append(runs["new"]["cpu_s"] - runs["old"]["cpu_s"])
                summary = {"producer_gain_s": gain, "samples": samples, "paired_importer_cost_s": pairs}
                if pair >= 2:
                    summary["medians"] = {s: {metric: statistics.median(x[metric] for x in samples if x["side"] == s)
                                               for metric in ("cpu_s", "wall_s")} for s in ("old", "new")}
                h.write(dest / "paired-importers.json", summary)
                # Two order-balanced pairs suffice if both imply the same decision with
                # one second of margin and their direct CPU differences agree within 2 s.
                if pair == 2 and (max(pairs) - min(pairs) <= 2
                                  and (max(pairs) < gain - 1 or min(pairs) > gain + 1)):
                    break
            for s, arm in arms.items():
                h.write(dest / ("final-facets-" + s + ".json"), from_project(h, arm[0], all_names))
    return benchmark
