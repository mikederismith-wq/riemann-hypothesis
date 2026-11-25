"""Check the joint Harris–Taylor construction and every importer on promoted main."""
import base64
import collections
import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import tarfile
import tempfile
import time
import traceback
from types import SimpleNamespace

FORK = "https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis"
BENCH = "79e6b8f8c8442f79968ff5e5dfc3bf4fc3daecdc"
PIN = "27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59"
ASSETS = {
    "measure.py": "74bb741fefdebe233a5b3494ed46150a14bc104cb95d53ff75adab63225dd26d",
    "Public.lean": "aa504ae2dc65eccb4e871749d32aecc7b0a1aaa15a101c451f4b622df61c81cb",
}
LOCAL_ASSETS = {
    "case.json": "0bd111ac85b99b632e6184c49b73387393dabdb7a079542d44cb03aa8618caef",
    "candidate.patch.b64": "f4fb03ef63693bc8dd6c5f0003e57f2417a6e9478eac212f9f1fb837022ae1d5",
}
TEMP = Path(os.environ["RUNNER_TEMP"]).resolve()
META = TEMP/"ks-bench"
RESULTS = TEMP/"rh-proof-results"
HEAVY = ("Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion", "Main")
GIB = 1024**3
HEADER_IMPORT = re.compile(r"^((?:(?:public|private|meta)\s+)*)import\s+(?:all\s+)?([\w'.]+)\s*$")

def source_graph(src):
    graph={}
    for path in src.rglob("*.lean"):
        depth=0
        imports=[]
        for line in path.read_text().splitlines():
            if depth or "/-" in line or "-/" in line:
                parts=[]
                i=0
                while i<len(line):
                    if line.startswith("/-",i):
                        depth+=1; i+=2
                    elif depth and line.startswith("-/",i):
                        depth-=1; i+=2
                    elif depth:
                        i+=1
                    elif line.startswith("--",i):
                        break
                    else:
                        parts.append(line[i]); i+=1
                line="".join(parts)
            else:
                line=line.partition("--")[0]
            line=line.strip()
            if not line or line in ("module","prelude"):
                continue
            match=HEADER_IMPORT.fullmatch(line)
            if match:
                imports.append(match[2])
                continue
            if re.match(r"(?:(?:public|private|meta)\s+)*import\b",line):
                raise ValueError(f"unsupported import header at {path}: {line!r}")
            break
        graph[".".join(path.relative_to(src).with_suffix("").parts)]=imports
    return graph

def digest(path):
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()

def setup():
    META.mkdir()
    for name, expected in ASSETS.items():
        dest = META/name
        subprocess.run(["curl", "-fsSL", "--retry", "2", "--max-time", "50", "-o", str(dest),
                        f"{FORK}/{BENCH}/ks-bench/{name}"], check=True)
        if digest(dest) != expected:
            raise ValueError(f"incorrect pinned harness input {name}")
    for name, expected in LOCAL_ASSETS.items():
        asset=Path(__file__).resolve().parent/name
        if digest(asset)!=expected:
            raise ValueError(f"incorrect current source patch or case {name}")
        shutil.copyfile(asset,META/name)
    spec = importlib.util.spec_from_file_location("ht", META/"measure.py")
    ks = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ks)
    return ks

def write(name, obj):
    (RESULTS/(name+".json")).write_text(json.dumps(obj, indent=2)+"\n")

def phase(name, **extra):
    value = dict(phase=name, **extra)
    print(json.dumps(value), flush=True)
    write("phase", value)

def vm(label, cmd=None):
    paths = ["/proc/meminfo", "/proc/swaps", "/proc/sys/vm/max_map_count",
             "/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory.swap.max",
             "/sys/fs/cgroup/memory.events"]
    report = {"host": {p:Path(p).read_text() if Path(p).is_file() else None for p in paths},
              "disk_free_gib": shutil.disk_usage(TEMP).free/GIB,
              "free_inodes": os.statvfs(TEMP).f_favail}
    if cmd:
        script = 'for f do printf "%s\n" "$f"; if test -r "$f"; then cat "$f"; fi; done'
        report["container"] = subprocess.run([*cmd,"/bin/sh","-c",script,"sh",*paths],
                                              capture_output=True,text=True,check=True).stdout
    write(label+"-resources", report)
    host = report["host"]
    fields = [x for x in host["/proc/meminfo"].splitlines()
              if x.split(":")[0] in ("MemTotal", "MemAvailable", "SwapTotal", "SwapFree")]
    print(label, *fields, "max_map_count", host["/proc/sys/vm/max_map_count"].strip(),
          "host cgroup RAM", host["/sys/fs/cgroup/memory.max"], "host cgroup swap",
          host["/sys/fs/cgroup/memory.swap.max"], "disk free GiB",round(report["disk_free_gib"],2),flush=True)

def sliced(seq,size):
    for start in range(0,len(seq),size):
        yield seq[start:start+size]

def restore(label, wanted, rows, prep, ci, options, project, cache, shared, cmd):
    # Keep a single private working set. Native Lake's .ltar alias is hardlinked
    # only within the build, exactly as on upstream CI. Drop trusted download
    # copies as soon as each batch has been independently verified and staged.
    names = sorted(wanted)
    random.Random(label+PIN).shuffle(names)
    count = 0
    t0 = time.monotonic()
    first_free = shutil.disk_usage(TEMP).free
    for batch in sliced(names,512):
        free = shutil.disk_usage(TEMP).free
        if free < 6*GIB or os.statvfs(TEMP).f_favail < 20000:
            raise RuntimeError(f"{label} restore stopped at {count}/{len(names)} with {free/GIB:.2f} GiB free")
        entries = {rows[n][1]:rows[n][2] for n in batch}
        hashes = {rows[n][2]:rows[n][3] for n in batch}
        prep.downloads(shared, entries, hashes)
        _, jobs, _ = ci.baseline(options, project, cache, modules=set(batch))
        if len(jobs)!=len(batch):
            raise ValueError("private ordinary/full staging missed a committed dependency")
        shutil.rmtree(shared/"artifacts")
        subprocess.run([*cmd,"/opt/lean/bin/leantar","--jobs","4","-f","-x","-j","-"],
                       input=json.dumps(jobs),text=True,check=True)
        # Complete native build outputs and their content-addressed input trace
        # are now present. With Lake's artifact cache disabled, the compressed
        # archives are no longer inputs to a successful warm build.
        for n in batch:
            stem=Path(*n.split("."))
            (project/".lake/build/ir"/stem.with_suffix(".ltar")).unlink()
        for file in set(entries.values()):
            (cache/"artifacts"/file).unlink()
        count+=len(batch)
        if count==len(names) or count%4096==0:
            free = shutil.disk_usage(TEMP).free
            stats = dict(phase=label,restored=count,total=len(names),seconds=time.monotonic()-t0,
                         growth_gib=(first_free-free)/GIB, free_gib=free/GIB,
                         free_inodes=os.statvfs(TEMP).f_favail)
            print(json.dumps(stats),flush=True)
            write(label+"-restore",stats)

def validate(sup,arm,names,label):
    project,cmd,result,overrides,_=arm
    sup.clear_targets(project,names)
    times=result/"compiler.jsonl"
    times.unlink(missing_ok=True)
    disklog=RESULTS/(label+".log")
    env=["RH_LEAN_TIMES=/work/result/compiler.jsonl","LAKE_ARTIFACT_CACHE=false","LEAN_NUM_THREADS=1"]
    args=[*cmd,"/usr/bin/env",*env,"/usr/bin/timeout","--kill-after=10s","40m","/opt/lean/bin/lake",
          "--packages",overrides,"--rehash","build",*("+"+n for n in names)]
    phase(label,targets=names)
    vm(label,cmd)
    t0=time.monotonic()
    with disklog.open("wb") as logfile:
        out=subprocess.run(args,stdout=logfile,stderr=subprocess.STDOUT)
    observed=[json.loads(l) for l in times.read_text().splitlines()] if times.is_file() else []
    counts=collections.Counter(row["module"] for row in observed if row["project"] and row["exit_code"]==0)
    expected=collections.Counter(names)
    unexpected=sorted(counts.keys()-expected.keys())
    extra_external=[r["module"] for r in observed if not r["project"]]
    artifacts={}
    for n in names:
        prefix=project/".lake/build/lib/lean"/Path(*n.split("."))
        p=prefix.with_suffix(".olean")
        if p.is_file():
            artifacts[n]=dict(sha256=digest(p),bytes=p.stat().st_size)
    verdict=out.returncode==0 and counts==expected and len(observed)==len(names) and set(artifacts)==set(names)
    record=dict(success=verdict,expected=names,exit=out.returncode,elapsed_s=time.monotonic()-t0,
                compiled=observed,unexpected_modules=unexpected,extra_external=extra_external,outputs=artifacts)
    write(label,record)
    print(label,json.dumps(dict(success=verdict, compiled=list(counts), exit=out.returncode)),flush=True)
    if not verdict:
        print("\n".join(disklog.read_text(errors="replace").splitlines()[-80:])[-20000:],flush=True)
        raise RuntimeError(f"{label} failed exact source-compiler or output checks")

def compare_interfaces(ks, prep, names, rows, arm, cache, case):
    project,cmd,result,_,_=arm
    names=sorted(names)
    retired=set(case["removed"])
    original_names=sorted(set(names)|retired)
    entries={rows[n][1]:rows[n][2] for n in original_names}
    hashes={rows[n][2]:rows[n][3] for n in original_names}
    prep.downloads(cache, entries, hashes)
    jobs=[]
    original={}
    for n in original_names:
        _,dep_hash,file,_=rows[n]
        stem=Path(*n.split("."))
        folder=Path("reference")/stem.parent
        (result/folder).mkdir(parents=True,exist_ok=True)
        base="/work/result/"+folder.as_posix()
        jobs.append({"file":"/work/cache/artifacts/"+file,"base":[base,base],"hash":dep_hash})
        original[n]=result/"reference"/stem.with_suffix(".olean")
    subprocess.run([*cmd,"/opt/lean/bin/leantar","--jobs","4","-f","-x","-j","-"],
                   input=json.dumps(jobs),text=True,check=True)
    tmpl=(META/"Public.lean").read_text()
    live_root="/work/project/.lake/build/lib/lean/"
    if tmpl.count(live_root)!=1:
        raise ValueError("pinned interface reader layout changed")
    by_arm={}
    for side,src_root in [("main","/work/result/reference/"),("candidate",live_root)]:
        (result/"importers.list").write_text("\n".join(original_names if side=="main" else names)+"\n")
        (result/"Interface.lean").write_text(tmpl.replace(live_root,src_root))
        dump=RESULTS/("importer-types-"+side+".jsonl")
        with dump.open("w") as out:
            ks.run(*cmd,"/opt/lean/bin/lean","--run","/work/result/Interface.lean",
                   "/work/result/importers.list",stdout=out)
        decl={}
        for line in dump.read_text().splitlines():
            r=json.loads(line)
            key=(r["module"],r["name"])
            if key in decl:
                raise ValueError(f"duplicate declaration record {key}")
            decl[key]=(r["typeHash"],r["universeParameters"])
        if not decl:
            raise ValueError("no exported declarations found")
        by_arm[side]=decl
    old,new=by_arm["main"],by_arm["candidate"]
    items={}
    for n in names:
        dotname=Path(*n.split("."))
        pub=project/".lake/build/lib/lean"/dotname.with_suffix(".olean")
        base=digest(original[n])
        current=digest(pub)
        items[n]=dict(published_olean_sha256=base,candidate_olean_sha256=current,
                      same_olean=base==current, declarations=sum(m==n for m,_ in new))
    added=sorted(new.keys()-old.keys())
    removed=sorted(old.keys()-new.keys())
    changed=sorted(k for k in old.keys() & new.keys() if old[k]!=new[k])
    write("importer-interface",dict(modules=items,added=added,removed=removed,changed=changed,
          published_declarations=len(old),candidate_declarations=len(new)))
    print("survivor, retired and downstream public interfaces", len(old), len(new), "declarations;",
          sum(v["same_olean"] for v in items.values()), "of", len(names), "byte-identical;",
          len(added), "added", len(removed), "removed", len(changed), "changed", flush=True)
    allowed_types=sorted([(case["survivor"],"GlobalTheory.HTCount.count"),
                          (case["survivor"],"GlobalTheory.T.harrisTaylor_firstOrder_deformations_basis_count")])
    if added or {n for n,_ in removed}!=retired or changed!=allowed_types:
        raise ValueError("unexpected public declaration or type change")

def main():
    RESULTS.mkdir(exist_ok=True)
    vm("initial")
    ks=setup()
    ROOT=ks.ROOT
    ROOT.mkdir()
    sup=ks.module("support",ks.checked_file(ks.PROOF_COMMIT,"proof-bench/proof.py",ks.PROOF_HASH))
    host=ks.module("host",ks.checked_file(ks.SUPPORT_COMMIT,"bench/quick-cache.py",ks.SUPPORT_HASH))
    timer=ks.checked_file(ks.PROOF_COMMIT,"proof-bench/lean-timer.py",ks.TIMER_HASH)
    host.STATE,host.REPORT=ROOT,RESULTS
    case=json.loads((META/"case.json").read_text())
    if (case["revision"]!=PIN or
            len(case["descendants"])!=15 or set(HEAVY)-set(case["descendants"])):
        raise ValueError("unexpected compatible case or revision")
    src=ROOT/"main"
    tc=host.toolchain()
    host.checkout(src,PIN,["src","scripts",*sup.CFG],1)
    ci=host.load("ci",src/"scripts/ci-build.py")
    prep=host.load("prep",src/"scripts/ci-prepare.py")
    ci.validate_inputs(src,ci.DEPENDENCIES)
    mp,mf,rec=sup.inputs(src,ci,prep,PIN)
    if (rec["candidate_tree"]!=case["candidate_tree"] or rec["source_tree"]!=case["source_tree"] or
            rec["map_sha256"]!="dfbad839a5423dcffc9b36826d34e54cf26b5b7177b3d9bf7ae4880bb6023c11"):
        raise ValueError("unrecognized promoted main tree or production archive map")
    pkgs=sup.packages(host,src,ci,tc)
    stream=io.BytesIO()
    with tarfile.open(fileobj=stream,mode="w"):
        pass
    ks.run("docker","import","-","rh-bench-empty:local",input=stream.getvalue())
    lean=tc/"bin/lean"
    lean.rename(tc/"bin/lean-real")
    shutil.copyfile(timer,lean)
    lean.chmod(0o755)
    with tempfile.TemporaryDirectory(dir=ROOT,prefix="down-") as tmp:
        work=Path(tmp)
        project=ks.variant(sup,"new",work,src,case)
        graph=source_graph(project/"src")
        root=case["survivor"]
        rev=ks.incoming(graph)
        descendants=sup.cone(rev,[root])-{root}
        if descendants!=set(case["descendants"]) or sorted(set(rev[root]))!=case["direct"]:
            raise ValueError("changed direct or complete reverse import graph")
        roots={root}|descendants
        ordinary=sorted(roots-set(HEAVY))
        near=sup.cone(graph,ordinary)-roots
        allwarm=sup.cone(graph,roots)-roots
        if (len(near)!=case["stages"]["ordinary_warm"] or len(allwarm)!=case["stages"]["all_warm"] or
                len(roots)!=case["stages"]["cold"] or any(n in graph for n in case["removed"])):
            raise ValueError("unexpected stage cones")
        # Validate all pinned module rows and complete archive map together once.
        entries,hashes=prep.manifest_artifacts(mf,mp,rec,modules=allwarm)
        rows={v[0]:v for line in gzip.decompress(mf).splitlines()[1:] if (v:=json.loads(line))}
        if len(entries)!=len(allwarm) or any(entries[rows[n][1]]!=rows[n][2] or
                                             hashes[rows[n][2]]!=rows[n][3] for n in allwarm):
            raise ValueError("unavailable or inconsistent published warm module")
        cache,shared,result,control=(work/n for n in ["cache","downloads","result","control"])
        for p in [cache/"artifacts",shared,result,control,project/".lake/packages"]:
            p.mkdir(parents=True)
        opts=SimpleNamespace(baseline_manifest=ROOT/"modules.gz",baseline_map=ROOT/"outputs.jsonl",
                             baseline_manifest_sha256=rec["module_manifest_sha256"],baseline_cache=shared)
        overrides=ci.package_overrides(project,control)
        cmd=ks.offline_sandbox(host,tc,project,pkgs,cache,result,control)
        arm=(project,cmd,result,overrides,sorted(roots))
        phase("ordinary-restore",unaffected=len(near))
        vm("after-packages",cmd)
        restore("ordinary",near,rows,prep,ci,opts,project,cache,shared,cmd)
        validate(sup,arm,ordinary,"ordinary-proof")
        witness=result/"CheckExports.lean"
        witness.write_text("module\npublic import "+root+"\n#check @GlobalTheory.UPel.HT.realise_isKS\n")
        with (RESULTS/"public-scalar.log").open("w") as log:
            ks.run(*cmd,"/opt/lean/bin/lake","--packages",overrides,"env","/opt/lean/bin/lean","-R",
                   "/work/result","/work/result/CheckExports.lean",stdout=log,stderr=subprocess.STDOUT)
        phase("full-restore",unaffected=len(allwarm-near))
        restore("full",allwarm-near,rows,prep,ci,opts,project,cache,shared,cmd)
        for n in HEAVY:
            validate(sup,arm,[n],n.rsplit(".",1)[-1])
        compare_interfaces(ks,prep,roots,rows,arm,cache,case)
        phase("complete",source_checked=[*ordinary,*HEAVY],direct=case["direct"],
              revision=PIN,
              transitive_importers=len(descendants),warm_dependencies=len(allwarm))

if __name__=="__main__":
    try:
        main()
    except Exception as e:
        RESULTS.mkdir(exist_ok=True)
        write("error",dict(error=str(e),traceback=traceback.format_exc()))
        raise
