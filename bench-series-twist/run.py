"""Bounded B14 transport test: charge real standalone, combined, and direct-importer builds."""
from collections import Counter
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import tempfile
from types import SimpleNamespace

import plan


HERE=Path(__file__).resolve().parent
PIN='1e6be6d46906f4b4f891a68a7d493782003c8bab'
FORK='https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis'
ASSETS={'proof.py':'2ab4a3a0bc574bf69e3d41cd5d38395d0f2e1f058b44c46c30677aceefdf804d',
        'lean-timer.py':'4e6ee472c842640d3611b55ec2f90c0f5f92de992cd0e188d40644d20e4a62c4'}
CFG=json.loads((HERE/'cases.json').read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def blob(data):
    return hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()


def relative(n):
    return Path('src')/Path(*n.split('.')).with_suffix('.lean')


def support():
    where=Path(os.environ['RUNNER_TEMP'])/'twist-driver'
    where.mkdir()
    for name,expected in ASSETS.items():
        dest=where/name
        subprocess.run(['curl','-fsSL','--retry','2','--max-time','60','-o',dest,
                        f'{FORK}/{PIN}/proof-bench/{name}'],check=True)
        if sha(dest.read_bytes())!=expected:raise ValueError(f'unrecognized driver {name}')
    shutil.copyfile(HERE/'cases.json',where/'cases.json')
    spec=importlib.util.spec_from_file_location('twist_measure',where/'proof.py')
    bench=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(bench)
    return bench


def snapshots(project,work):
    old={n:(project/relative(n)).read_bytes() for n in plan.OWNERS}
    for n,val in CFG['source_blobs'].items():
        if blob((project/relative(n)).read_bytes())!=val:raise ValueError('unexpected B14 source '+n)
    temp=work/'source-overlay'
    for n,contents in old.items():
        dest=temp/relative(n)
        dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(contents)
    patch=(HERE/'proof.patch').read_bytes()
    if sha(patch)!=CFG['patch_sha256']:raise ValueError('incorrect proof overlay')
    for flags in [('--check',),()]:
        subprocess.run(['git','apply','--whitespace=error',*flags,'-'],input=patch,cwd=temp,check=True)
    new={n:(temp/relative(n)).read_bytes() for n in plan.OWNERS}
    if {n:blob(t) for n,t in new.items()}!=CFG['patched_blobs']:raise ValueError('unexpected new source')
    return {'old':old,'new':new},temp


def set_arm(project,sources):
    for n,t in sources.items():
        f=project/relative(n)
        # The initial source tree is hardlinked to the verified checkout.
        f.unlink()
        f.write_bytes(t)


def stage(bench,prep,ci,arm,cache,shared,control,published,wanted):
    project,command,_,_,_=arm
    mp,mf,receipt=published
    entries,hashes=prep.manifest_artifacts(mf,mp,receipt,modules=wanted)
    if len(entries)!=len(wanted):raise ValueError('incomplete official dependency manifest')
    bench.disk(f'verified staged artifacts: {len(wanted)}',7)
    prep.downloads(shared,entries,hashes)
    opt=SimpleNamespace(baseline_manifest=bench.ROOT/'modules.gz',baseline_map=bench.ROOT/'outputs.jsonl',
                        baseline_manifest_sha256=receipt['module_manifest_sha256'],baseline_cache=shared)
    _,jobs,_=ci.baseline(opt,project,cache,modules=wanted)
    if len(jobs)!=len(wanted):raise ValueError('incomplete cache extraction plan')
    bench.run(*command,'/opt/lean/bin/leantar','--jobs','4','-f','-x','-j','-',input=json.dumps(jobs),text=True)


def exact_build(bench,arm,targets,expected,out,label):
    bench.build(arm,list(targets),out,label)
    log=json.loads((out/(label+'.json')).read_text())
    comp=log['actual_compilers']
    if Counter(c['module'] for c in comp if c['project'] and not c['exit_code'])!=Counter(expected) or len(comp)!=len(expected):
        raise ValueError(f'{label} compiled an unexpected workload: {[c["module"] for c in comp]}')
    return {c['module']:c for c in comp}


def save_outputs(arm,side,out):
    project,_,result,_,_=arm
    state=result/side
    state.mkdir()
    inventory={}
    for n in sorted(plan.IMPACTED):
        stem=project/'.lake/build/lib/lean'/Path(*n.split('.'))
        for ext in ('.olean','.olean.server','.olean.private'):
            shutil.copyfile(stem.with_suffix(ext),state/(n+ext))
        d=json.loads(stem.with_suffix('.ilean').read_text())
        if d['module']!=n:raise ValueError('wrong compiled declaration index')
        inventory[n]={'public_source_names':sorted(k for k in d['decls'] if not k.startswith('_')),
                      'public_olean_sha256':sha(stem.with_suffix('.olean').read_bytes())}
    (out/(side+'-interfaces.json')).write_text(json.dumps(inventory,indent=2)+'\n')
    return inventory


def compare(bench,case,main,graph,published,host,ci,prep,toolchain,packages):
    out=bench.OUT/case['name']
    out.mkdir()
    with tempfile.TemporaryDirectory(prefix='twist-transport-',dir=bench.ROOT) as tmp:
        work=Path(tmp)
        project=work/'project'; project.mkdir()
        for fname in bench.CFG:shutil.copyfile(main/fname,project/fname)
        shutil.copytree(main/'src',project/'src',copy_function=os.link)
        variants,overlay=snapshots(project,work)
        parser=bench.load('twist_changed_imports',main/'scripts/quick-check.py')
        modern=graph|{n:parser.imports(overlay/relative(n)) for n in plan.OWNERS}
        small,large=plan.verify(graph,modern)
        bench.write(out/'plan.json',{'revision':CFG['revision'],'early_cache_modules':len(small),
                    'importer_cache_modules':len(large),'roots':sorted(plan.OWNERS),'new_standalone_extra':sorted([plan.DONOR,plan.EXTRA]),
                    'direct_importers':sorted(plan.LEAVES),'impacted_importer_workflow':sorted(plan.IMPACTED)})
        result=work/'result'; cache=work/'cache'; control=work/'control'; shared=bench.ROOT/'compressed'
        for p in [result,cache/'artifacts',control,project/'.lake/packages']:p.mkdir(parents=True)
        overrides=ci.package_overrides(project,control)
        cmd=host.sandbox(toolchain,project,packages,cache,result,control)
        arm=(project,cmd,result,overrides,[])
        stage(bench,prep,ci,arm,cache,shared,control,published,small)
        cold=plan.OWNERS|{plan.EXTRA}
        pairs=[]
        for index,order in enumerate([('new','old'),('old','new')],start=1):
            row={}
            for side in order:
                set_arm(project,variants[side])
                bench.clear_targets(project,cold)
                expected={plan.BUYER} if side=='old' else cold
                obs=exact_build(bench,arm,[plan.BUYER],expected,out,f'pair-{index}-{side}-standalone')
                solo=sum(v['cpu_s'] for v in obs.values())
                if side=='old':
                    obs.update(exact_build(bench,arm,[plan.DONOR],{plan.DONOR,plan.EXTRA},out,f'pair-{index}-{side}-remaining-provider'))
                row[side]={'module_cpu':{n:v['cpu_s'] for n,v in obs.items()},'standalone_cpu':solo,
                           'combined_cpu':sum(v['cpu_s'] for v in obs.values())}
            pairs.append(row)
            bench.write(out/'pairs.json',pairs)
            gains={k:row['old'][k]-row['new'][k] for k in ('standalone_cpu','combined_cpu')}
            if min(gains.values())<=0:
                bench.write(out/'decision.json',{'stage':'standalone','pairs':index,'reason':'either standalone or combined slowed','gains_s':gains})
                print('First pass ends before importer restoration',gains,flush=True)
                return
        gains={k:statistics.median(r['old'][k]-r['new'][k] for r in pairs) for k in ('standalone_cpu','combined_cpu')}
        if gains['standalone_cpu']<3 or gains['combined_cpu']<8:
            bench.write(out/'decision.json',{'stage':'standalone','pairs':len(pairs),'reason':'small measured gain','gains_s':gains})
            return
        # Both true workloads improved twice. Restore the remaining shared dependencies once.
        # The extra prerequisite was withheld for stage one and is warm in the importer comparison.
        stage(bench,prep,ci,arm,cache,shared,control,published,large-small)
        saved={}
        # The direct workflow builds its five real roots; Lake decides the intervening modules.
        for side in ('old','new'):
            set_arm(project,variants[side])
            bench.clear_targets(project,plan.IMPACTED)
            exact_build(bench,arm,sorted(plan.LEAVES),plan.IMPACTED,out,'importers-'+side)
            saved[side]=save_outputs(arm,side,out)
        if any(saved['old'][n]['public_source_names']!=saved['new'][n]['public_source_names'] for n in plan.IMPACTED):
            raise ValueError('public source declarations changed')
        shutil.copyfile(HERE/'Check.lean',result/'Check.lean')
        with (out/'kernel.log').open('wb') as log:
            test=subprocess.run([*cmd,'/usr/bin/env','LEAN_NUM_THREADS=2','/usr/bin/timeout','15m',
                '/opt/lean/bin/lake','--packages',overrides,'env','/opt/lean/bin/lean','/work/result/Check.lean'],stdout=log,stderr=subprocess.STDOUT)
        if test.returncode:
            print((out/'kernel.log').read_text(errors='replace')[-10500:],flush=True)
            raise ValueError('compiled public kernel checks failed')
        shutil.copyfile(result/'signatures.json',out/'signatures.json')
        checked=json.loads((out/'signatures.json').read_text())
        if {q['module'] for q in checked}!=plan.IMPACTED or any(not q['retained_types'] or q['removed'] for q in checked):
            raise ValueError('incomplete compiled public comparison')
        bench.write(out/'decision.json',{'stage':'direct importers','pairs':2,'gains_s':gains,
                   'compiled_public_types':{q['module']:len(q['retained_types']) for q in checked}})


def main():
    bench=support(); baseline=bench.inputs
    def inputs(project,ci,prep,revision):
        pub=baseline(project,ci,prep,revision)
        if any(pub[2].get(k)!=v for k,v in CFG['receipt'].items()):raise ValueError('incorrect B14 receipt')
        return pub
    def source_graph(src):
        parser=bench.load('twist_imports',src.parent/'scripts/quick-check.py')
        return {'.'.join(p.relative_to(src).with_suffix('').parts):parser.imports(p) for p in src.rglob('*.lean')}
    bench.inputs=inputs;bench.source_graph=source_graph;bench.benchmark_case=lambda *x:compare(bench,*x)
    bench.main()


if __name__=='__main__':
    main()
