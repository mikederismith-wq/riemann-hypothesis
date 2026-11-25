"""Compare the joint geometric-lemma producer workload and check every direct consumer on official RH inputs."""
from collections import Counter
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess

HERE = Path(__file__).resolve().parent
HARNESS = '1e6be6d46906f4b4f891a68a7d493782003c8bab'
DIGESTS = {
    'proof.py': '2ab4a3a0bc574bf69e3d41cd5d38395d0f2e1f058b44c46c30677aceefdf804d',
    'lean-timer.py': '4e6ee472c842640d3611b55ec2f90c0f5f92de992cd0e188d40644d20e4a62c4',
}
def path(project, name):
    return project / 'src' / Path(*name.split('.')).with_suffix('.lean')
def blob(data):
    return hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()

def run():
    work = Path(os.environ['RUNNER_TEMP']) / 'swap-cell-harness'
    work.mkdir()
    for filename, expected in DIGESTS.items():
        address = f'https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis/{HARNESS}/proof-bench/{filename}'
        target = work / filename
        subprocess.run(['curl', '-fsSL', '--retry', '2', '--max-time', '60', '-o', target, address], check=True)
        if hashlib.sha256(target.read_bytes()).hexdigest() != expected:
            raise ValueError(f'unexpected {filename}')
    shutil.copyfile(HERE / 'cases.json', work / 'cases.json')
    for filename in ('pending.patch','generalize.patch'):
        (work / filename).write_bytes(gzip.decompress((HERE / (filename+'.gz')).read_bytes()))
    cfg=json.loads((work / 'cases.json').read_text())
    case=cfg['cases'][0]
    roots=set(case['targets'])
    users=set(case['direct_importers'])
    golden=cfg['source_blobs']
    spec=importlib.util.spec_from_file_location('swap_harness',work/'proof.py')
    h=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(h)
    original_inputs,original_variant,original_build = h.inputs,h.apply_variant,h.build

    def inputs(project, ci, prep, revision):
        published=original_inputs(project,ci,prep,revision)
        if any(published[2].get(k) != v for k,v in cfg['receipt'].items()):
            raise ValueError('official B14 RH receipt differs')
        if any(blob(path(project,n).read_bytes()) != v['main'] for n,v in golden.items()):
            raise ValueError('B14 source hashes changed')
        return published

    def graph(src):
        parser=h.load('swap_imports',src.parent/'scripts/quick-check.py')
        return {'.'.join(p.relative_to(src).with_suffix('').parts):parser.imports(p) for p in src.rglob('*.lean')}

    def apply_variant(main,dest,patches):
        touched=original_variant(main,dest,patches)
        expected={m for m,g in golden.items() if g[dest.name] != g['main']}
        if touched!=expected or any(blob(path(dest,n).read_bytes()) != v[dest.name] for n,v in golden.items()):
            raise ValueError(f'{dest.name} sources or cleanup patch differ')
        return touched

    def public_types(arm,dest,label):
        project,cmd,_,_,_=arm
        shutil.copyfile(HERE/'Public.lean',project/'SwapCellPublic.lean')
        (project/'swap-cell-modules.txt').write_text('\n'.join(sorted(roots | users))+'\n')
        with (dest/(label+'-types.jsonl')).open('wb') as out,(dest/(label+'-types.log')).open('wb') as err:
            subprocess.run([*cmd,'/opt/lean/bin/lean','--run','/work/project/SwapCellPublic.lean',
                            '/work/project/swap-cell-modules.txt'],check=True,stdout=out,stderr=err)

    def compare_types_and_cpu(dest):
        rows={}
        for side in ('old','new'):
            records=[json.loads(l) for l in (dest/(side+'-types.jsonl')).read_text().splitlines()]
            if {r['module'] for r in records}!=roots|users:
                raise ValueError('missing module in compiled public declarations')
            rows[side]={(r['module'],r['name']):(r['typeHash'],r['universeParameters']) for r in records}
        old,new=rows['old'],rows['new']
        removed=sorted([list(k) for k in old.keys()-new.keys()])
        added=sorted([list(k) for k in new.keys()-old.keys()])
        changed=sorted([list(k) for k in old.keys()&new.keys() if old[k]!=new[k]])
        report={'old_public':len(old),'new_public':len(new),'removed':removed,'added':added,
                'changed':changed,'per_module':{n:sum(1 for k in old if k[0]==n) for n in sorted(roots|users)}}
        h.write(dest/'public-signatures.json',report)
        order=['old','new','old','new','new','old','old','new','new','old']
        data=[]
        for i,side in enumerate(order):
            if i<2:continue
            rep=json.loads((dest/(str(i)+'-'+side+'.json')).read_text())
            comp={x['module']:x['cpu_s'] for x in rep['actual_compilers'] if x['project']}
            data.append({'side':side,'target_cpu_s':sum(comp[n] for n in roots),
                         'all_cpu_s':sum(comp.values()),'extra': sorted(set(comp)-roots)})
        totals={s:statistics.median(x['target_cpu_s'] for x in data if x['side']==s) for s in ('old','new')}
        deltas=[]
        for i in range(0,len(data),2):
            pair={r['side']:r['target_cpu_s'] for r in data[i:i+2]}
            deltas.append(pair['old']-pair['new'])
        h.write(dest/'joint-cpu.json',{'cpu_sum_medians':totals,'paired_savings':deltas,'samples':data})
        if removed or changed or len(added)!=1 or added[0][1] != cfg['added_name']:
            raise ValueError('compiled public declarations differ from the proposed generalization')

    def build(arm,targets,dest,label,check_extra=False):
        cpu=original_build(arm,targets,dest,label,check_extra=False)
        row=json.loads((dest/(label+'.json')).read_text())
        workers=row['actual_compilers'];counts=Counter(r['module'] for r in workers if r['project'] and r['exit_code']==0)
        if any(not r['project'] or r['exit_code']!=0 for r in workers) or any(v!=1 for v in counts.values()):
            raise ValueError('unexpected compiler or duplicate module in '+label)
        if label.startswith('importers-'):
            if not users<=set(counts) or not set(counts)<=set(arm[-1]):
                raise ValueError('unexpected direct-consumer compilation')
            side=label.removeprefix('importers-')
            public_types(arm,dest,side)
            if side=='new': compare_types_and_cpu(dest)
        elif not set(counts)<=set(cfg['warmup_cold']) or not roots<=set(counts):
            raise ValueError('unexpected producer compilation')
        return cpu
    h.inputs,h.source_graph,h.apply_variant,h.build = inputs,graph,apply_variant,build
    follow = h.load('swap_consumers', HERE / 'consumers.py')
    h.benchmark_case = follow.install(h, original_build, HERE)
    h.main()

if __name__=='__main__':
    run()
