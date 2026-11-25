"""One-arm source check of the Harris–Taylor replacement and every in-repository importer."""
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
PIN = "fcb6eac7534875d32d68030967e2deae6d686151"
ASSETS = {
    "measure.py": "74bb741fefdebe233a5b3494ed46150a14bc104cb95d53ff75adab63225dd26d",
    "case.json": "50ed416579865fc60182c6a9ae134e8c71c78ef081f0757494bf3d628ca82cfa",
    "candidate.patch.b64": "8ad2cd06d42daac119b3f696130f912e50ba25f3cc556d95233bc3746fa20637",
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
    if case["revision"]!=PIN or len(case["descendants"])!=15 or set(HEAVY)-set(case["descendants"]):
        raise ValueError("unexpected compatible case or revision")
    src=ROOT/"main"
    tc=host.toolchain()
    host.checkout(src,PIN,["src","scripts",*sup.CFG],1)
    ci=host.load("ci",src/"scripts/ci-build.py")
    prep=host.load("prep",src/"scripts/ci-prepare.py")
    ci.validate_inputs(src,ci.DEPENDENCIES)
    mp,mf,rec=sup.inputs(src,ci,prep,PIN)
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
        if len(near)!=12075 or len(allwarm)!=59705 or any(n in graph for n in case["removed"]):
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
        phase("full-restore",unaffected=len(allwarm-near))
        restore("full",allwarm-near,rows,prep,ci,opts,project,cache,shared,cmd)
        for n in HEAVY:
            validate(sup,arm,[n],n.rsplit(".",1)[-1])
        phase("complete",source_checked=[*ordinary,*HEAVY],direct=case["direct"],
              transitive_importers=len(descendants),warm_dependencies=len(allwarm))

if __name__=="__main__":
    try:
        main()
    except Exception as e:
        RESULTS.mkdir(exist_ok=True)
        write("error",dict(error=str(e),traceback=traceback.format_exc()))
        raise
