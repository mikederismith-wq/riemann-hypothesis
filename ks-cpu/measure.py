"""Measure retired proofs once per old input set, then pair the two real consumers."""
from collections import Counter
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
import tempfile
import traceback

PIN = '27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59'
SOURCE = 'c61a2dcaf85e1ad4253c0a99362952a1157082d2'
FORK = 'https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis'
TEMP = Path(os.environ['RUNNER_TEMP']).resolve()
RESULTS = TEMP/'rh-proof-results'
ASSETS = {'check.py': '9d2880e4d6dd4313ab32d1bf3f3e7aa4464818b61fe80cf1e0e2d3320f873016',
          'case.json': '0bd111ac85b99b632e6184c49b73387393dabdb7a079542d44cb03aa8618caef',
          'candidate.patch.b64': 'f4fb03ef63693bc8dd6c5f0003e57f2417a6e9478eac212f9f1fb837022ae1d5'}

def write(name,data):
    (RESULTS/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')

def controller():
    support=TEMP/'current-inputs'
    support.mkdir()
    for file,sha in ASSETS.items():
        path=support/file
        subprocess.run(['curl','-fsSL','--retry','2','--max-time','45','-o',str(path),
                        f'{FORK}/{SOURCE}/ks-downstream/{file}'],check=True)
        if hashlib.sha256(path.read_bytes()).hexdigest()!=sha:
            raise ValueError(f'incorrect source-validation input {file}')
    spec=importlib.util.spec_from_file_location('verified_inputs',support/'check.py')
    ctl=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ctl)
    return ctl

def official_outputs(ks,prep,published,arm,names):
    project,cmd,result,_,_=arm
    mp,mf,record=published
    selected=prep.manifest_artifacts(mf,mp,record,modules=set(names))
    entries,hashes=selected
    cache=result.parent/'cache'
    prep.downloads(cache,entries,hashes)
    rows={r[0]:r for line in gzip.decompress(mf).splitlines()[1:] if (r:=json.loads(line)) and r[0] in names}
    if len(rows)!=len(names):
        raise ValueError('missing current-main reference object')
    jobs=[]
    for n,(_,key,file,expected) in rows.items():
        if entries[key]!=file or hashes[file]!=expected:
            raise ValueError('unexpected reference object identity')
        folder=Path('published')/Path(*n.split('.')).parent
        (result/folder).mkdir(parents=True,exist_ok=True)
        base='/work/result/'+folder.as_posix()
        jobs.append(dict(file='/work/cache/artifacts/'+file,hash=key,base=[base,base]))
    subprocess.run([*cmd,'/opt/lean/bin/leantar','--jobs','4','-f','-x','-j','-'],
                   input=json.dumps(jobs),text=True,check=True)
    output={}
    for n in rows:
        stem=result/'published'/Path(*n.split('.'))
        output[n]={s:ks.digest(stem.with_suffix(s)) for s in ('.olean','.olean.private','.ir.sig')}
    write('published-original-facets',output)
    return output

def measure(ks,sup,arm,names,label,expected=None):
    sup.disk(label)
    ks.measured(sup,arm,names,label,check_extra=True)
    data=json.loads((RESULTS/(label+'.json')).read_text())
    rows=data['actual_compilers']
    if (data['exit_code'] or len(rows)!=len(names) or
            Counter(r['module'] for r in rows if r['project'] and r['exit_code']==0)!=Counter(names)):
        raise ValueError(f'{label} has an unexpected compiler invocation')
    out={n:{s:r['sha256'] for s,r in data['outputs'][n].items()} for n in names}
    if any(set(v)!={'.olean','.olean.private','.ir.sig'} for v in out.values()):
        raise ValueError(f'{label} is missing compiler output facets')
    mismatches={} if expected is None else {
        n:[s for s in out[n] if out[n][s]!=expected[n][s]] for n in names if out[n]!=expected[n]}
    if mismatches:
        write(label+'-facet-mismatches',mismatches)
        print(label,'compiler-facet mismatches',json.dumps(mismatches),flush=True)
    sample=dict(cpu={r['module']:r['cpu_s'] for r in rows},
                compiler_wall={r['module']:r['wall_s'] for r in rows},lake_wall=data['wall_s'])
    print(label,json.dumps(sample),flush=True)
    return sample,out

def summarize(removed,old,new):
    def med(rows):
        return {k:statistics.median(r['cpu'][k] for r in rows) for k in rows[0]['cpu']}
    def summed(row):
        return sum(row['cpu'].values())
    removed_cpu=statistics.median(summed(r) for r in removed)
    savings=[removed_cpu+summed(a)-summed(b) for a,b in zip(old,new)]
    return dict(retired_old_module_cpu=med(removed),surviving_old_module_cpu=med(old),
                surviving_new_module_cpu=med(new),retired_old_total_cpu=removed_cpu,
                composed_old_total_cpu=removed_cpu+statistics.median(summed(r) for r in old),
                new_total_cpu=statistics.median(summed(r) for r in new),
                net_cpu_savings=statistics.median(savings),savings_by_paired_consumers=savings,
                old_paired_consumer_lake_wall=[r['lake_wall'] for r in old],
                new_paired_consumer_lake_wall=[r['lake_wall'] for r in new],
                retired_group_lake_wall=[r['lake_wall'] for r in removed])

def main():
    RESULTS.mkdir(exist_ok=True)
    ctl=controller()
    ks=ctl.setup()
    case=json.loads((ctl.META/'case.json').read_text())
    if case['revision']!=PIN:
        raise ValueError('unexpected promoted main')
    ks.ROOT.mkdir()
    sup=ks.module('bench',ks.checked_file(ks.PROOF_COMMIT,'proof-bench/proof.py',ks.PROOF_HASH))
    h=ks.module('host',ks.checked_file(ks.SUPPORT_COMMIT,'bench/quick-cache.py',ks.SUPPORT_HASH))
    timer=ks.checked_file(ks.PROOF_COMMIT,'proof-bench/lean-timer.py',ks.TIMER_HASH)
    h.STATE,h.REPORT=ks.ROOT,RESULTS
    sup.disk('stock compiler',32)
    tc=h.toolchain()
    src=ks.ROOT/'main'
    h.checkout(src,PIN,['src','scripts',*sup.CFG],1)
    ci=h.load('ci_build',src/'scripts/ci-build.py')
    prep=h.load('ci_prepare',src/'scripts/ci-prepare.py')
    ci.validate_inputs(src,ci.DEPENDENCIES)
    published=sup.inputs(src,ci,prep,PIN)
    rec=published[2]
    if (rec['candidate_tree']!=case['candidate_tree'] or rec['source_tree']!=case['source_tree'] or
        rec['map_sha256']!='dfbad839a5423dcffc9b36826d34e54cf26b5b7177b3d9bf7ae4880bb6023c11' or
        rec['module_manifest_sha256']!='db39a50d765652f9d55f1eefc711a31b9552ad17704c332c6f099d2f36196ad6'):
        raise ValueError('wrong official baseline for this source tree')
    sup.disk('Mathlib preparation',22)
    packages=sup.packages(h,src,ci,tc)
    base_graph=ctl.source_graph(src/'src')
    (ks.ROOT/'compressed').mkdir()
    stream=io.BytesIO()
    with tarfile.open(fileobj=stream,mode='w'):
        pass
    ks.run('docker','import','-','rh-bench-empty:local',input=stream.getvalue())
    lean=tc/'bin/lean'
    lean.rename(tc/'bin/lean-real')
    shutil.copyfile(timer,lean)
    lean.chmod(0o755)
    with tempfile.TemporaryDirectory(dir=ks.ROOT,prefix='paired-') as td:
        work=Path(td)
        arms={}
        warm={}
        for side in ('new','old'):
            sup.disk('prepare '+side,12)
            prj=ks.variant(sup,side,work,src,case)
            arm,graph=ks.prepare_arm(side,work,case,base_graph,prj,published,sup,h,ci,prep,tc,packages)
            cold=case['sides'][side]['roots']
            if graph!=ctl.source_graph(prj/'src'):
                raise ValueError(f'{side} module graph disagrees with source-file headers')
            warm[side]=sup.cone(graph,cold)-set(cold)
            arms[side]=arm
        if warm['old']!=warm['new'] or len(warm['old'])!=6116:
            raise ValueError('the paired arms have different unaffected input modules')
        retired=case['removed']
        consumers=[case['survivor'],*case['direct']]
        if set(consumers)!=set(case['sides']['new']['roots']) or set(consumers+retired)!=set(case['sides']['old']['roots']):
            raise ValueError('unexpected current root/consumer grouping')
        ref=official_outputs(ks,prep,published,arms['old'],retired+consumers)
        _,new_ref=measure(ks,sup,arms['new'],consumers,'warm-new-consumers')
        measure(ks,sup,arms['old'],retired,'warm-old-retired',ref)
        measure(ks,sup,arms['old'],consumers,'warm-old-consumers',ref)
        groups={'retired':[],'old':[],'new':[]}
        seq=['retired','old','new','new','old','retired']
        for i,group in enumerate(seq):
            side='old' if group=='retired' else group
            target=retired if group=='retired' else consumers
            sample,_=measure(ks,sup,arms[side],target,f'{i}-{group}',new_ref if side=='new' else ref)
            groups[group].append(sample)
            write('observations',dict(trial_order=seq[:i+1],samples=groups))
        summary=summarize(groups['retired'],groups['old'],groups['new'])
        summary.update(revision=PIN,unaffected_warm=len(warm['old']),actual_added_dependencies=[],
                       retired=retired,direct_importers=case['direct'],trial_order=seq)
        summary['reference_mismatches']=[p.name for p in sorted(RESULTS.glob('*-facet-mismatches.json'))]
        write('medians',summary)
        print('completed current-main measurements',json.dumps(summary),flush=True)
        if summary['reference_mismatches']:
            raise ValueError('completed measurements have compiler facets requiring investigation')
        write('phase',dict(phase='complete'))

if __name__=='__main__':
    try:
        main()
    except Exception as e:
        RESULTS.mkdir(exist_ok=True)
        write('error',dict(error=str(e),traceback=traceback.format_exc()))
        raise
