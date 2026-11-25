"""Stock-Lake proof benchmark in an offline, non-root container on the user's fork."""
from collections import Counter, defaultdict
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
import sys
import tarfile
import tempfile
import time
import traceback
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
TEMP = Path(os.environ["RUNNER_TEMP"])
ROOT = TEMP/"rh-proof"
OUT = TEMP/"rh-proof-results"
CFG = ("lakefile.toml","lake-manifest.json","lean-toolchain")
HOST_COMMIT = "c5b7dc99d50b61f102c619ba5634dde9465bf9d6"
HOST_DIGEST = "dea75b622f5fe5198f9c9141515d93654f2e267329769eb42e020c4ca37b15e6"
FORK = "https://github.com/mikederismith-wq/riemann-hypothesis.git"
IMPORT = re.compile(rb"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.\x80-\xff]+)")

def write(path, obj):
    path.write_text(json.dumps(obj,indent=2)+"\n")

def run(*cmd, **kw):
    return subprocess.run(list(map(str,cmd)),check=True,**kw)

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

def disk(phase,reserve=4):
    free=shutil.disk_usage(ROOT).free
    print(f"{phase}: {free/1024**3:.1f} GiB free",flush=True)
    write(OUT/"phase.json",dict(phase=phase,free_bytes=free))
    if free<reserve*1024**3:
        raise RuntimeError(f"less than {reserve} GiB available")

def setup_fixture(h,tc):
    """This independent cache-client diagnostic cannot abort the proof measurements."""
    pin="78a87162a3b34030a5f0640265851450ebb9a1c7"
    dest=ROOT/"fixture-repo"
    with (OUT/"cache-client-fixture.log").open("wb") as log:
        try:
            original=h.UPSTREAM
            try:
                h.UPSTREAM=FORK
                h.checkout(dest,pin,["scripts","tools",*CFG],1)
            finally:
                h.UPSTREAM=original
            shims=ROOT/"shim";shims.mkdir()
            wrapper=shims/"elan"
            wrapper.write_text("#!/bin/sh\n"
                f"if [ \"$#\" = 2 ] && [ \"$1 $2\" = 'which lean' ]; then echo '{tc}/bin/lean'; exit 0; fi\n"
                f"if [ \"$#\" -ge 3 ] && [ \"$1 $2 $3\" = 'run leanprover/lean4:v4.37.0-rc1 lean' ]; then shift 3; exec '{tc}/bin/lean' \"$@\"; fi\n"
                "exit 2\n")
            wrapper.chmod(0o755)
            env=dict(os.environ,PATH=f"{shims}:{tc}/bin:{os.environ['PATH']}",LEAN_SYSROOT=str(tc))
            p=subprocess.run([sys.executable,"scripts/tests/test_ci_cache_get.py"],cwd=dest,env=env,
                             stdout=log,stderr=subprocess.STDOUT,timeout=180)
            write(OUT/"cache-client-fixture.json",dict(commit=pin,exit_code=p.returncode,elan="pinned launcher"))
        except Exception as e:
            write(OUT/"cache-client-fixture.json",dict(commit=pin,error=str(e)))

def packages(h,project,ci,tc):
    deps=ROOT/"deps";deps.mkdir()
    for name in CFG:shutil.copyfile(project/name,deps/name)
    (deps/"src").mkdir()
    pkgs=deps/".lake/packages";pkgs.mkdir(parents=True)
    for p in json.loads((deps/"lake-manifest.json").read_text())["packages"]:
        path=pkgs/p["name"]
        run("git","init","-q",path)
        run("git","remote","add","origin",p["url"],cwd=path)
        run("git","fetch","-q","--depth=1","--no-tags","origin",p["rev"],cwd=path)
        run("git","checkout","-q","--detach",p["rev"],cwd=path)
    ci.validate_packages(project,pkgs)
    mc=ROOT/"mathlib-cache"
    env=dict(os.environ,PATH=f"{tc}/bin:{os.environ['PATH']}",LEAN_SYSROOT=str(tc),
             MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4",MATHLIB_CACHE_DIR=str(mc))
    with (OUT/"mathlib-cache.log").open("wb") as log:
        run(tc/"bin/lake","exe","mathlib/cache","get",cwd=deps,env=env,stdout=log,stderr=subprocess.STDOUT)
    ci.validate_packages(project,pkgs)
    if mc.is_dir():shutil.rmtree(mc)
    for p in pkgs.iterdir():shutil.rmtree(p/".git")
    return pkgs

def inputs(project,ci,prep,revision):
    client=load("proof_client",project/"scripts/ci-cache-get.py")
    identity=client.current_identity(project)
    raw=prep.get(f"{prep.BASE}/ci/revisions/{revision}.json")
    rec=client.matching_record(raw,identity)
    if rec is None or rec["candidate_head"]!=revision or rec["candidate_tree"]!=ci.git(project,"rev-parse","HEAD^{tree}"):
        raise ValueError("wrong proof-cache receipt")
    mp=prep.get(prep.BASE+"/"+rec["map_key"])
    mf=prep.get(prep.BASE+"/"+rec["module_manifest_key"])
    if prep.digest(mp)!=rec["map_sha256"] or prep.digest(mf)!=rec["module_manifest_sha256"] or len(mf)!=rec["module_manifest_bytes"]:
        raise ValueError("proof-cache content address mismatch")
    (ROOT/"modules.gz").write_bytes(mf);(ROOT/"outputs.jsonl").write_bytes(mp)
    write(OUT/"receipt.json",rec)
    return mp,mf,rec

def source_graph(src):
    return {".".join(p.relative_to(src).with_suffix("").parts):[b.decode() for b in IMPORT.findall(p.read_bytes())]
            for p in src.rglob("*.lean")}

def cone(graph,names):
    found=set();q=list(names)
    while q:
        n=q.pop()
        if n in graph and n not in found:found.add(n);q.extend(graph[n])
    return found

def apply_variant(main,dest,patches):
    dest.mkdir()
    for n in CFG:shutil.copyfile(main/n,dest/n)
    # Each variant owns its input files; archive checks are outside compiler timings.
    shutil.copytree(main/"src",dest/"src")
    touched=set()
    for name in patches:
        p=HERE/name
        for path in re.findall(r"^\+\+\+ b/(src/.*?\.lean)$",p.read_text(),re.M):
            touched.add(".".join(Path(path).relative_to("src").with_suffix("").parts))
        run("git","apply","--check",p,cwd=dest)
        run("git","apply",p,cwd=dest)
    return touched

def initialize_arm(d,arm,patches,spec,main,base_graph,published,h,ci,prep,tc,pkgs):
    project=d/arm;changed=apply_variant(main,project,patches)
    graph=base_graph.copy()
    for n in changed:
        graph[n]=[b.decode() for b in IMPORT.findall((project/"src"/Path(*n.split(".")).with_suffix(".lean")).read_bytes())]
    targets=set(spec["targets"]);users=set(spec["direct_importers"])
    direct={n for n,ds in graph.items() if targets.intersection(ds)}-targets
    if direct!=users:raise ValueError(f"direct-importer list differs: {direct^users}")
    deps=cone(graph,targets|users)
    reverse=defaultdict(list)
    for n in deps:
        for parent in graph[n]:reverse[parent].append(n)
    cold=cone({n:reverse[n] for n in deps},targets|changed|set(spec.get("force_cold",[])))
    if len(deps)!=spec["expected_cone"] or len(cold)!=spec["expected_cold"]:
        raise ValueError(f"unexpected proof graph: {len(deps)} modules, {len(cold)} affected")
    names=deps-cold
    mp,mf,rec=published
    entries,hashes=prep.manifest_artifacts(mf,mp,rec,modules=names)
    if len(entries)!=len(names):raise ValueError("missing verified dependency")
    shared=ROOT/"compressed"
    prep.downloads(shared,entries,hashes)
    for f in ("cache/artifacts","result","control"):
        (d/(arm+"-work")/f).mkdir(parents=True,exist_ok=True)
    work=d/(arm+"-work");(project/".lake/packages").mkdir(parents=True)
    overrides=ci.package_overrides(project,work/"control")
    args=SimpleNamespace(baseline_manifest=ROOT/"modules.gz",baseline_map=ROOT/"outputs.jsonl",
                         baseline_manifest_sha256=rec["module_manifest_sha256"],baseline_cache=shared)
    _,jobs,_=ci.baseline(args,project,work/"cache",modules=names)
    if len(jobs)!=len(names):raise ValueError("verified archive selection changed")
    cmd=h.sandbox(tc,project,pkgs,work/"cache",work/"result",work/"control")
    if "--interactive" not in cmd and "-i" not in cmd:raise ValueError("unpacker requires interactive stdin")
    run(*cmd,"/opt/lean/bin/leantar","--jobs","4","-f","-x","-j","-",input=json.dumps(jobs),text=True)
    return project,cmd,work/"result",overrides,sorted(cold)

def clear_targets(project,names):
    for n in names:
        m=Path(*n.split("."))
        for base in ("lib/lean","ir"):
            parent=project/".lake/build"/base/m.parent
            for p in parent.glob(m.name+".*"):
                if p.is_file():p.unlink()

def build(arm,targets,dest,label,check_extra=False):
    project,cmd,result,overrides,cold=arm
    clear_targets(project,targets)
    profile=result/"compiler.jsonl"
    profile.unlink(missing_ok=True)
    log=dest/(label+".log")
    start=time.monotonic()
    with log.open("wb") as stream:
        proc=subprocess.run([*cmd,"/usr/bin/env","RH_LEAN_TIMES=/work/result/compiler.jsonl",
           "LAKE_ARTIFACT_CACHE=false","LEAN_NUM_THREADS=2","/usr/bin/timeout","--kill-after=10s","20m",
           "/opt/lean/bin/lake","--packages",overrides,"--rehash","build",*["+"+n for n in targets]],
           stdout=stream,stderr=subprocess.STDOUT)
    elapsed=time.monotonic()-start
    rows=[json.loads(l) for l in profile.read_text().splitlines()] if profile.is_file() else []
    compiled=Counter(x["module"] for x in rows if x["project"] and x["exit_code"]==0)
    files={}
    for n in targets:
        m=project/".lake/build/lib/lean"/Path(*n.split("."))
        files[n]={typ:{"bytes":p.stat().st_size,"sha256":digest(p)} for typ in (".olean",".olean.private",".ir.sig")
                  if (p:=m.with_suffix(typ)).is_file()}
    report=dict(targets=targets,wall_s=elapsed,exit_code=proc.returncode,actual_compilers=rows,outputs=files)
    write(dest/(label+".json"),report)
    if proc.returncode or any(compiled[n]!=1 for n in targets):
        raise RuntimeError(f"{label}: Lake exited {proc.returncode}, target compiler counts "
                           f"{[(n,compiled[n]) for n in targets]}; see preserved log and timings")
    if check_extra and (set(compiled)!=set(targets) or any(not r["project"] for r in rows)):
        raise ValueError(f"{label} unexpectedly compiled extra modules")
    return {r["module"]:r["cpu_s"] for r in rows if r["module"] in targets}

def digest(path):
    with path.open("rb") as f:return hashlib.file_digest(f,"sha256").hexdigest()

def benchmark_case(spec, main,graph,published,h,ci,prep,tc,pkgs):
    name=spec["name"];dest=OUT/name;dest.mkdir()
    with tempfile.TemporaryDirectory(prefix=name+"-",dir=ROOT) as tmp:
        arms={}
        for side,patches in spec["variants"].items():
            disk(f"{name} restore {side}",12)
            arms[side]=initialize_arm(Path(tmp),side,patches,spec,main,graph,published,h,ci,prep,tc,pkgs)
            write(dest/(side+"-cold.json"),arms[side][-1])
        data={"old":[],"new":[]}
        for i,side in enumerate(("old","new","old","new","new","old","old","new","new","old")):
            disk(f"{name} {i} {side}")
            cpu=build(arms[side],spec["targets"],dest,f"{i}-{side}",check_extra=i>=2)
            if i>=2:data[side].append(cpu)
        medians={k:{n:statistics.median(r[n] for r in rs) for n in spec["targets"]} for k,rs in data.items()}
        write(dest/"module-cpu-medians.json",medians)
        print(name,json.dumps(medians),flush=True)
        for side,arm in arms.items():
            disk(f"{name} importer check {side}")
            build(arm,spec["direct_importers"],dest,"importers-"+side)

def main():
    with (HERE/"cases.json").open() as f:spec=json.load(f)
    ROOT.mkdir();OUT.mkdir(exist_ok=True)
    disk("stock toolchain and build inputs",32)
    url=f"https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis/{HOST_COMMIT}/bench/quick-cache.py"
    helper=ROOT/"fork_host.py"
    run("curl","-fLsS","--retry","2","-o",helper,url)
    if digest(helper)!=HOST_DIGEST:raise ValueError("fork benchmark helper digest differs")
    h=load("proof_host",helper);h.STATE=ROOT;h.REPORT=OUT
    tc=h.toolchain()
    project=ROOT/"main"
    h.checkout(project,spec["revision"],["src","scripts",*CFG],1)
    ci=h.load("proof_ci",project/"scripts/ci-build.py")
    prep=h.load("proof_prep",project/"scripts/ci-prepare.py")
    ci.validate_inputs(project,ci.DEPENDENCIES)
    if spec.get("cache_client_test"):setup_fixture(h,tc)
    disk("verified full Mathlib and RH inputs",22)
    pkgs=packages(h,project,ci,tc)
    published=inputs(project,ci,prep,spec["revision"])
    graph=source_graph(project/"src")
    (ROOT/"compressed").mkdir()
    empty=io.BytesIO()
    with tarfile.open(fileobj=empty,mode="w"):pass
    run("docker","import","-","rh-bench-empty:local",input=empty.getvalue())
    # Measure the real compiler's wait4 usage on the exact command issued by Lake.
    lean=tc/"bin/lean";lean.rename(tc/"bin/lean-real");shutil.copyfile(HERE/"lean-timer.py",lean);lean.chmod(0o755)
    failed=[]
    for case in spec["cases"]:
        try:benchmark_case(case,project,graph,published,h,ci,prep,tc,pkgs)
        except Exception as e:
            failed.append(case["name"]);write(OUT/(case["name"]+"-error.json"),{"error":str(e),"traceback":traceback.format_exc()})
            print(case["name"],e,flush=True)
    if failed:raise RuntimeError(f"benchmark cases failed: {failed}")
    write(OUT/"phase.json",dict(phase="complete"))

if __name__=="__main__":
    OUT.mkdir(exist_ok=True)
    try:main()
    except Exception as e:
        write(OUT/"error.json",dict(error=str(e),traceback=traceback.format_exc(),free_bytes=shutil.disk_usage(TEMP).free))
        raise
