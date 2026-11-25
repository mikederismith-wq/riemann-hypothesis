"""Stock Lean and Lake observations for direct reuse of the low-level rho theorem."""
import base64
from collections import Counter
import gzip
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import tarfile
import time
import traceback
import plan

HERE=Path(__file__).resolve().parent
TEMP=Path(os.environ['RUNNER_TEMP'])
OUT=TEMP/'joint-edge-results'
BOOT='6d7b35b32743ffaf89f56351f0162dc2ee31c378'
BOOT_SHA='34ecdf556afd7bc40287eb0e6793b0eb4881b52d99cb958cbcba0320e6031e0f'


def write(file, data):
    (OUT/file).write_text(json.dumps(data,indent=2)+'\n')


def bridge_driver():
    url=f'https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis/{BOOT}/lift-measure/measure.py'
    path=TEMP/'edge_stage.py'
    subprocess.run(['curl','-fsSL','--retry','2','--max-time','45','-o',str(path),url],check=True)
    if plan.digest(path.read_bytes())!=BOOT_SHA:raise ValueError('unexpected stock-cache staging source')
    spec=importlib.util.spec_from_file_location('edge_stage',path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.HERE,module.OUT=HERE,OUT
    return module


def put(project, name, data):
    # The input trees initially hardlink immutable official files. Detach before editing.
    file=project/plan.path(name)
    file.unlink(missing_ok=True)
    file.write_bytes(data)


def stock(arm, roots, label, expected=None, allowed=None):
    project,sandbox,result,overrides,_=arm
    profile=result/'compiler.jsonl'
    profile.unlink(missing_ok=True)
    args=[*sandbox,'/usr/bin/env','RH_LEAN_TIMES=/work/result/compiler.jsonl',
          'LAKE_ARTIFACT_CACHE=false','LEAN_NUM_THREADS=2','/usr/bin/timeout','--kill-after=10s','30m',
          '/opt/lean/bin/lake','--packages',overrides,'--rehash','build',*['+'+n for n in roots]]
    start=time.monotonic()
    log=OUT/(label+'.log')
    with log.open('wb') as stream:
        proc=subprocess.run(args,stdout=stream,stderr=subprocess.STDOUT)
    elapsed=time.monotonic()-start
    rows=[json.loads(l) for l in profile.read_text().splitlines()] if profile.is_file() else []
    modules=Counter(x['module'] for x in rows if x['project'] and x['exit_code']==0)
    facets={}
    for name in (plan.J,plan.S,plan.E,plan.U,plan.M):
        path=project/'.lake/build/lib/lean'/Path(*name.split('.'))
        facets[name]={t:{'bytes':f.stat().st_size,'sha256':plan.digest(f.read_bytes())} for t in ('.olean','.olean.private','.ir.sig')
                      if (f:=path.with_suffix(t)).is_file()}
    report={'targets':roots,'wall_s':elapsed,'exit_code':proc.returncode,'actual_compilers':rows,
            'outputs':facets,'cpu_s':sum(x['cpu_s'] for x in rows)}
    write(label+'.json',report)
    valid=not proc.returncode and all(x['project'] and x['exit_code']==0 for x in rows) and all(v==1 for v in modules.values())
    if expected is not None:valid=valid and modules==Counter(expected)
    if allowed is not None:valid=valid and set(modules)<=allowed and plan.S in modules
    if not valid:
        print('\n'.join(log.read_text(errors='replace').splitlines()[-35:]),flush=True)
        raise RuntimeError(f'{label}: stock Lake exit {proc.returncode}, observed {dict(modules)}, expected {expected}, allowed {allowed}')
    print(f'{label}: {len(modules)} Lean processes, {elapsed:.2f}s Lake wall, {report["cpu_s"]:.2f}s compiler CPU',flush=True)
    return {'cpu_s':report['cpu_s'],'wall_s':elapsed,'modules':dict(modules),
            'facets':{n:v.get('.olean',{}).get('sha256') for n,v in facets.items()}}


def prepare_sources(ks,sup,office,quick,case):
    base={'old_j':(office/plan.path(plan.J)).read_bytes(),'new_s':(office/plan.path(plan.S)).read_bytes()}
    for k,v in json.loads((HERE/'overlays.json').read_text()).items():
        base[k]=gzip.decompress(base64.b64decode(v,validate=True))
    actual={k:{'git_blob':plan.blob(v),'sha256':plan.digest(v),'bytes':len(v)} for k,v in base.items()}
    if actual!=case['files'] or {k:v['git_blob'] for k,v in actual.items()}!=plan.BLOBS:
        raise ValueError('source does not reproduce the precise accepted and experimental blobs')
    write('verified-files.json',actual)
    src=office/'src'
    official={'.'.join(f.relative_to(src).with_suffix('').parts):quick.imports(f) for f in src.rglob('*.lean')}
    projects={};graphs={};public={};hashes={}
    for side in ('old','new'):
        project=projects[side]=ks.ROOT/('arm-'+side)
        project.mkdir()
        for f in sup.CFG:shutil.copyfile(office/f,project/f)
        shutil.copytree(office/'src',project/'src',copy_function=os.link)
        for n in plan.RETIRE:(project/plan.path(n)).unlink()
        for n,key in [(plan.E,'early'),(plan.U,'late'),(plan.J,side+'_j')]:put(project,n,base[key])
        graphs[side]={};hashes[side]={}
        for state,key in [('post','new_s'),('pre','old_s')]:
            put(project,plan.S,base[key])
            graph=official.copy()
            for m in plan.RETIRE:del graph[m]
            for m in (plan.J,plan.S,plan.U,plan.E):graph[m]=quick.imports(project/plan.path(m))
            graphs[side][state]=graph
            hashes[side][state]=plan.tree(office,project)
            if state=='post':public[side]=ks.public_graph(project/'src')
    if hashes!=case['trees']:raise ValueError(f'differing complete source trees {hashes}')
    write('source-trees.json',hashes)
    safe,exclusive,summary=plan.freeze(graphs,official)
    if summary!=case['expected']:raise ValueError(f'changed source dependency plan {summary}')
    write('verified-plan.json',summary)
    write('exclusive-old-project-inputs.json',sorted(exclusive))
    return projects,base,public,safe,exclusive


def summaries(pairs):
    summary={}
    for metric in ('cpu_s','wall_s'):
        old=[p['old'][metric] for p in pairs]
        new=[p['new'][metric] for p in pairs]
        saved=[a-b for a,b in zip(old,new)]
        summary[metric]={'old':old,'new':new,'paired_saved':saved,'median_paired_saved':statistics.median(saved)}
    return summary


def measure(ks,sup,arms,source,public,exclusive):
    clients=[plan.U,plan.M];hot={plan.J,plan.S,plan.E,plan.U,plan.M}
    states={'old':'pre','new':'pre'}
    for side in ('old','new'):
        stock(arms[side],clients,'prime-pre-'+side,expected=hot)
    def transition(i,side,forward):
        prior,current=('old_s','new_s') if forward else ('new_s','old_s')
        previous,target=('pre','post') if forward else ('post','pre')
        project=arms[side][0]
        if states[side]!=previous or (project/plan.path(plan.S)).read_bytes()!=source[prior]:
            raise ValueError('accepted scalar edit starting state changed')
        put(project,plan.S,source[current])
        states[side]=target
        return stock(arms[side],clients,('accepted-' if forward else 'reverse-')+str(i)+'-'+side,allowed=hot)
    accepted=[]
    for i,order in enumerate([('old','new'),('new','old')],1):
        if i==2:
            for side in ('new','old'):transition(i,side,False)
        sample={side:transition(i,side,True) for side in order}
        accepted.append(sample)
        write('accepted-summary.json',summaries(accepted))
        if i==2 and any(accepted[0][side]['facets']!=sample[side]['facets'] for side in arms):
            raise ValueError('same accepted scalar edit gave different public artifacts')
    # Both real direct importers have been built from their own source by stock Lake.
    roots=[plan.J,plan.S,plan.E,plan.U,plan.M]
    interface={'survivor':plan.U,'direct':[plan.J,plan.E,plan.M,plan.S],'sides':{s:{'roots':roots} for s in arms}}
    ks.public_tables(sup,interface,arms,public)
    api=json.loads((OUT/'public-interface.json').read_text())
    if any(api.values()):raise ValueError(f'changed public declarations, signatures, or export closures: {api}')
    for side in arms:
        names={json.loads(l)['name'] for l in (OUT/(side+'-declarations.jsonl')).read_text().splitlines()}
        required={'GlobalTheory.HTGlueLie.root_sub_ne_zero','GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks','GlobalTheory.HTRealise.realise_core'}
        if required-names:raise ValueError('missing exposed declarations '+str(required-names))
    reports={}
    for mode in ('warm','cold'):
        pairs=[]
        for i,order in enumerate([('old','new'),('new','old')],1):
            sample={}
            for side in order:
                evict={plan.J} if mode=='warm' else exclusive|{plan.J}
                sup.clear_targets(arms[side][0],evict)
                expected=evict if side=='old' or mode=='warm' else {plan.J}
                sample[side]=stock(arms[side],[plan.J],mode+'-'+str(i)+'-'+side,expected=expected)
            pairs.append(sample)
            write(mode+'-summary.json',summaries(pairs))
        reports[mode]=summaries(pairs)
    write('complete.json',{'scope':'B14 + H + #2074','accepted_edit':summaries(accepted),**reports})


def main():
    case=json.loads((HERE/'case.json').read_text())
    if (case['main'],case['production'],case['split'],case['pre_scalar'],case['accepted_scalar_edit'])!=(plan.OFFICIAL,plan.PRODUCTION,plan.SPLIT,plan.PREVIOUS,plan.ACCEPTED):
        raise ValueError('unexpected experiment provenance')
    boot=bridge_driver();ks=boot.restore_driver();ks.ROOT.mkdir()
    sup=ks.module('edge_proof',ks.checked_file(ks.PROOF_COMMIT,'proof-bench/proof.py',ks.PROOF_HASH))
    host=ks.module('edge_host',ks.checked_file(ks.SUPPORT_COMMIT,'bench/quick-cache.py',ks.SUPPORT_HASH))
    timer=ks.checked_file(ks.PROOF_COMMIT,'proof-bench/lean-timer.py',ks.TIMER_HASH)
    host.STATE,host.REPORT,sup.OUT=ks.ROOT,OUT,OUT
    sup.disk('verified dependency setup',32);tc=host.toolchain();office=ks.ROOT/'main'
    host.checkout(office,plan.OFFICIAL,['src','scripts',*sup.CFG],1)
    ci=host.load('edge_ci',office/'scripts/ci-build.py');prep=host.load('edge_prepare',office/'scripts/ci-prepare.py')
    quick=host.load('edge_imports',office/'scripts/quick-check.py');ci.validate_inputs(office,ci.DEPENDENCIES)
    receipt=sup.inputs(office,ci,prep,plan.OFFICIAL)
    for key in ('candidate_head','candidate_tree','source_tree','build_exit_code','toolchain','build_receipt_sha256','map_sha256','module_manifest_sha256'):
        if receipt[2].get(key)!=case['receipt'][key]:raise ValueError('invalid promoted receipt '+key)
    sup.disk('pinned Mathlib',22);packages=sup.packages(host,office,ci,tc);(ks.ROOT/'compressed').mkdir()
    projects,source,pub,safe,exclusive=prepare_sources(ks,sup,office,quick,case)
    with io.BytesIO() as data:
        with tarfile.open(fileobj=data,mode='w'):pass
        ks.run('docker','import','-','rh-bench-empty:local',input=data.getvalue())
    lean=tc/'bin/lean';lean.rename(tc/'bin/lean-real');shutil.copyfile(timer,lean);lean.chmod(0o755)
    arms={}
    for side in ('new','old'):
        sup.disk('prepare '+side,12)
        arms[side]=boot.stage(ks,sup,host,ci,prep,projects[side],ks.ROOT/('work-'+side),tc,packages,receipt,safe)
    measure(ks,sup,arms,source,pub,exclusive)

if __name__=='__main__':
    OUT.mkdir(exist_ok=True)
    try:main()
    except Exception as exc:
        write('error.json',{'error':str(exc),'traceback':traceback.format_exc()})
        raise
