"""Fork-only reproduction of the Lake portion of RH quick check 45456091397."""
from pathlib import Path
from types import SimpleNamespace
import hashlib
import importlib.util
import io
import json
import os
import re
import shutil
import statistics
import subprocess
import tarfile
import tempfile
import time
import traceback

UPSTREAM = "https://github.com/leanprover-community/riemann-hypothesis.git"
HARNESS = "fcb6eac7534875d32d68030967e2deae6d686151"
MERGE = "6483deb5e1b2a8930583db94872c6eae14687b09"
BASE = "307cef33f046955ee79dba47e0d828d06496d75f"
HEAD = "bfc6446813a5d872906699183236f34242f144ed"
LEAN_ARCHIVE = "lean-4.37.0-rc1-linux.tar.zst"
LEAN_DIGEST = "2e1bbb832870bb81b7131cb70b13aec2cc7ed9f22e2bdbb236b86076ae20382d"
PATCH_DIGEST = "d12e0f20538fd38c07d5794260eba81503e9697af73510f7c62f733efcac2f67"
TEMP = Path(os.environ["RUNNER_TEMP"]).resolve()
STATE = TEMP / "rh-benchmark"
REPORT = TEMP / "rh-benchmark-results"
BUILT = re.compile(r"\] Built (\S+) \(")

def run(*args, **kwargs):
    return subprocess.run(list(map(str, args)), check=True, **kwargs)

def output(*args, **kwargs):
    return run(*args, stdout=subprocess.PIPE, text=True, **kwargs).stdout.strip()

def write(name, value):
    (REPORT/name).write_text(json.dumps(value, indent=2) + "\n")

def check_space(minimum, stage):
    free = shutil.disk_usage(STATE).free
    print(f"{stage}: {free / 1024**3:.2f} GiB free", flush=True)
    if free < minimum * 1024**3:
        raise RuntimeError(f"{stage} requires {minimum} GiB free on this runner")

def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def checkout(directory, revision, entries, depth):
    run("git", "init", "-q", directory)
    run("git", "remote", "add", "origin", UPSTREAM, cwd=directory)
    run("git", "sparse-checkout", "set", "--no-cone", *["/"+p for p in entries], cwd=directory)
    run("git", "fetch", "-q", f"--depth={depth}", "--filter=blob:none", "--no-tags", "origin", revision, cwd=directory)
    run("git", "checkout", "-q", "--detach", revision, cwd=directory)
    assert output("git", "rev-parse", "HEAD", cwd=directory) == revision

def toolchain():
    tc = STATE / "lean"
    tar = STATE / LEAN_ARCHIVE
    tc.mkdir()
    run("curl", "-fLsS", "--retry", "3", "-o", tar,
        f"https://github.com/leanprover/lean4/releases/download/v4.37.0-rc1/{LEAN_ARCHIVE}")
    if digest(tar) != LEAN_DIGEST:
        raise ValueError("Lean release archive digest mismatch")
    run("tar", "--zstd", "-xf", tar, "--strip-components=1", "-C", tc)
    tar.unlink()
    version = output(tc/"bin/lean", "--version")
    if "0b77e12952ad39077d80d8bd6b66d601f225c321" not in version:
        raise ValueError(f"unexpected Lean build: {version}")
    return tc

def dependencies(project, controller, qc, plan, tc):
    deps = STATE/"dependency-project"
    deps.mkdir()
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        if (project/name).read_bytes() != (controller/name).read_bytes():
            raise ValueError(f"candidate differs from the pinned controller at {name}")
        shutil.copyfile(controller/name, deps/name)
    (deps/"src").mkdir()
    packages = deps/".lake/packages"
    packages.mkdir(parents=True)
    for pkg in json.loads((deps/"lake-manifest.json").read_text())["packages"]:
        path = packages/pkg["name"]
        run("git", "init", "-q", path)
        run("git", "remote", "add", "origin", pkg["url"], cwd=path)
        run("git", "fetch", "-q", "--depth=1", "--no-tags", "origin", pkg["rev"], cwd=path)
        run("git", "checkout", "-q", "--detach", pkg["rev"], cwd=path)
    qc.ci.validate_packages(project, packages)
    closure = set(plan["closure"])
    external = {n for m in closure for n in qc.imports(project/"src"/(m.replace(".", "/")+".lean"))} - closure
    # The other two external roots on this fixed merge come from the Lean distribution.
    modules = sorted(n for n in external if n.startswith(("Mathlib.", "Aesop.")))
    if len(modules) != 431 or any(not n.startswith(("Mathlib.", "Aesop.", "Std.")) for n in external):
        raise ValueError("unexpected package imports on fixed merge")
    cache = STATE/"mathlib-cache"
    env = dict(os.environ, PATH=f"{tc}/bin:{os.environ['PATH']}", LEAN_SYSROOT=str(tc),
               MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4", MATHLIB_CACHE_DIR=str(cache))
    print(f"Fetching {len(modules)} package roots; output is in mathlib-cache.log", flush=True)
    with (REPORT/"mathlib-cache.log").open("wb") as log:
        run(tc/"bin/lake", "exe", "mathlib/cache", "get", *modules, env=env, cwd=deps,
            stdout=log, stderr=subprocess.STDOUT)
    if cache.is_dir():
        shutil.rmtree(cache)
    qc.ci.validate_packages(project, packages)
    # These job-private packages have been checked against all pinned revisions.
    # Git data is unnecessary inside the offline build.
    for p in packages.iterdir():
        shutil.rmtree(p/".git")
    return packages

def seeds(old, new, request, project, plans):
    shared = STATE/"compressed"
    shared.mkdir()
    pinned = old.prep
    mp = pinned.get(f"{pinned.BASE}/revisions/{pinned.REPO}/tc/{pinned.settings.TOOLCHAIN_DIR}/{pinned.REVISION}.jsonl")
    mf = pinned.get(f"{pinned.BASE}/bootstrap/{pinned.REVISION}/modules.jsonl.gz")
    if pinned.digest(mp) != pinned.MAP_SHA or pinned.digest(mf) != pinned.MANIFEST_SHA:
        raise ValueError("pinned map or manifest digest mismatch")
    exact = new.prep.quick_base(request, project)
    if exact is None:
        raise RuntimeError("exact-base successful receipt is unavailable")
    retained = {}
    for side, (map_bytes, manifest, record), qc, names in (
        ("pinned", (mp, mf, None), old, set(plans[0]["closure"])),
        ("exact", exact, new, set(plans[1]["unchanged_ancestors"])),
    ):
        mapping, hashes = qc.prep.manifest_artifacts(manifest, map_bytes, record, modules=names)
        qc.prep.downloads(shared, mapping, hashes)
        map_path, manifest_path = STATE/(side+".map"), STATE/(side+".gz")
        map_path.write_bytes(map_bytes)
        manifest_path.write_bytes(manifest)
        args = SimpleNamespace(baseline_manifest=manifest_path, baseline_map=map_path,
                               baseline_cache=shared, baseline_manifest_sha256=qc.prep.digest(manifest))
        retained[side] = (qc, names, args, len(mapping))
    return retained

def sandbox(tc, project, packages, cache, results, control):
    # An empty local Docker image supplies the namespace only. The regular host
    # userspace, pinned Lean and the exact source tree are mounted read-only.
    mounts = [(Path(p), p, "ro") for p in ("/usr","/bin","/lib","/lib64") if Path(p).exists()]
    mounts += [(tc, "/opt/lean", "ro"), (project, "/work/project", "ro"),
               (project/".lake", "/work/project/.lake", "rw"), (packages, "/work/project/.lake/packages", "rw"),
               (cache, "/work/cache", "rw"), (results, "/work/result", "rw"), (control, "/control", "ro")]
    cmd = ["docker","run","--rm","--read-only","--network=none","--cap-drop=ALL",
           "--security-opt=no-new-privileges","--cpus=4","--pids-limit=4096",
           "--user",f"{os.getuid()}:{os.getgid()}","--tmpfs","/tmp:mode=1777","--tmpfs","/home/build:mode=1777",
           "--workdir","/work/project"]
    for src, dst, mode in mounts:
        cmd += ["--volume", f"{src}:{dst}:{mode}"]
    for key,val in dict(HOME="/home/build",PATH="/opt/lean/bin:/usr/bin:/bin",
                        LEAN_SYSROOT="/opt/lean",LAKE_HOME="/opt/lean",LAKE_CACHE_DIR="/work/cache",
                        LAKE_RESTORE_ARTIFACTS="true",LEAN_NUM_THREADS="4",RUST_MIN_STACK="8388608").items():
        cmd += ["--env", key+"="+val]
    return cmd+["rh-bench-empty:local"]

def trial(index, side, seed, project, plan, tc, packages, control, overrides):
    check_space(2, f"trial {index} {side}")
    qc,names,base,count = seed
    lake = project/".lake"
    lake.mkdir()
    (lake/"packages").mkdir()
    try:
        with tempfile.TemporaryDirectory(dir=STATE) as td:
            cache, results = Path(td)/"cache",Path(td)/"results"
            (cache/"artifacts").mkdir(parents=True)
            results.mkdir()
            start = time.monotonic()
            _,jobs,_ = qc.ci.baseline(base, project, cache, modules=names)
            if len(jobs) != count:
                raise ValueError("wrong number of archives selected for extraction")
            cmd=sandbox(tc,project,packages,cache,results,control)
            run(*cmd, "/opt/lean/bin/leantar","--jobs","4","-f","-x","-j","-",input=json.dumps(jobs),text=True)
            stage_sec=time.monotonic()-start
            log=REPORT/f"{index}-{side}.log"
            with log.open("wb") as stream:
                # The timer runs beside Lake, so its child usage includes all compiler workers.
                timer = (
                    "import resource,subprocess,sys,time\n"
                    "start=time.monotonic()\n"
                    "code=subprocess.run(sys.argv[1:]).returncode\n"
                    "use=resource.getrusage(resource.RUSAGE_CHILDREN)\n"
                    "with open('/work/result/timing','w') as f: "
                    "print(time.monotonic()-start,use.ru_utime,use.ru_stime,file=f)\n"
                    "sys.exit(code)"
                )
                proc=subprocess.run([*cmd,"/usr/bin/python3","-c",timer,
                    "/usr/bin/timeout","--kill-after=10s","15m","/opt/lean/bin/lake","--packages",overrides,
                    "--rehash","build",*["+"+n for n in plan["targets"]]],stdout=stream,stderr=subprocess.STDOUT)
            built={m[1] for line in log.read_text(errors="replace").splitlines() if (m:=BUILT.search(line))}
            external_built=built-set(plan["closure"])
            row=dict(side=side,warmup=index<2,exit_code=proc.returncode,staged=len(jobs),
                     stage_wall_s=stage_sec,built_project=sorted(built & set(plan["closure"])),
                     built_other=sorted(external_built))
            if (results/"timing").is_file():
                wall,user,system=map(float,(results/"timing").read_text().split())
                row.update(lake_wall_s=wall,lake_user_s=user,lake_system_s=system,lake_cpu_s=user+system)
            write(f"{index}-{side}.json",row)
            proc.check_returncode()
            if "lake_cpu_s" not in row or not set(plan["targets"]) <= built:
                raise ValueError("missing timing or a changed target was not recorded as built")
            if index>=2 and external_built:
                raise ValueError(f"a package module rebuilt in measured trial {index}: {sorted(external_built)[:3]}")
            return row
    finally:
        shutil.rmtree(lake)

def main():
    STATE.mkdir()
    check_space(11, "initial setup")
    write("phase.json", {"phase":"pinned toolchain"})
    tc=toolchain()
    write("phase.json", {"phase":"controller and candidate checkouts"})
    cfg=["lakefile.toml","lake-manifest.json","lean-toolchain"]
    original,patched,project=STATE/"controller",STATE/"patched",STATE/"project"
    checkout(original,HARNESS,["scripts",*cfg],1)
    shutil.copytree(original,patched,ignore=shutil.ignore_patterns(".git"))
    patch=Path(__file__).with_name("quick-cache.patch").resolve()
    if digest(patch)!=PATCH_DIGEST:
        raise ValueError("benchmark patch checksum mismatch")
    run("git","apply",patch,cwd=patched)
    old=load("bench_old",original/"scripts/quick-check.py")
    new=load("bench_new",patched/"scripts/quick-check.py")
    checkout(project,MERGE,["src",*cfg],2)
    if output("git","show","-s","--format=%P","HEAD",cwd=project).split()!=[BASE,HEAD]:
        raise ValueError("recorded historical merge parents differ")
    identity=load("bench_client",original/"scripts/ci-cache-get.py").current_identity(project)
    request=dict(base_ref="main",base_head=BASE,pr_head=HEAD,expected=dict(identity,candidate_head=MERGE))
    plans=[q.plan(project,request) for q in (old,new)]
    if plans[0]["closure"]!=plans[1]["closure"] or plans[0]["targets"]!=plans[1]["targets"]:
        raise ValueError("the plans changed the requested modules")
    if (len(plans[0]["targets"]),len(plans[0]["closure"]),len(plans[1]["unchanged_ancestors"]))!=(3,677,674):
        raise ValueError("pinned graph differs from the recorded #1331 case")
    write("plan.json",plans[1])
    write("phase.json", {"phase":"verify RH cache inputs"})
    caches=seeds(old,new,request,project,plans)
    # The isolated build receives the same full src tree. Its Git database is
    # no longer needed after plan/receipt verification.
    shutil.rmtree(project/".git")
    write("phase.json", {"phase":"locked package checkouts and selective Mathlib cache"})
    check_space(6, "before fetching packages")
    packages=dependencies(project,original,new,plans[1],tc)
    control=STATE/"control"
    control.mkdir()
    overrides=new.ci.package_overrides(project,control)
    empty=io.BytesIO()
    with tarfile.open(fileobj=empty,mode="w"):
        pass
    run("docker","import","-","rh-bench-empty:local",input=empty.getvalue())
    rows=[]
    for i,side in enumerate(("pinned","exact","pinned","exact","exact","pinned")):
        write("phase.json", {"phase":"trial","index":i,"side":side,"completed_trials":len(rows)})
        rows.append(trial(i,side,caches[side],project,plans[1],tc,packages,control,overrides))
        write("trials.json",rows)
        print(json.dumps({k:v for k,v in rows[-1].items() if not k.startswith("built")}),flush=True)
    totals={side:{k:statistics.median(r[k] for r in rows if r["side"]==side and not r["warmup"])
                  for k in ("stage_wall_s","lake_wall_s","lake_cpu_s")} for side in caches}
    write("medians.json",totals)
    write("phase.json", {"phase":"complete","completed_trials":len(rows)})
    print(json.dumps(totals),flush=True)

if __name__=="__main__":
    REPORT.mkdir(exist_ok=True)
    try:
        main()
    except Exception as e:
        write("error.json", {"error":str(e),"traceback":traceback.format_exc(),
                             "free_bytes":shutil.disk_usage(TEMP).free})
        raise
