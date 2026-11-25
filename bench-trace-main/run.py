"""Run the previously measured trace A/B on batch 2057's exact inputs."""
from collections import Counter
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
PIN = '1e6be6d46906f4b4f891a68a7d493782003c8bab'
FILES = {
    'proof.py':'2ab4a3a0bc574bf69e3d41cd5d38395d0f2e1f058b44c46c30677aceefdf804d',
    'lean-timer.py':'4e6ee472c842640d3611b55ec2f90c0f5f92de992cd0e188d40644d20e4a62c4',
    'trace-old.patch':'8ed949fe8d2b12c356e218809b998231ed4efdfcb92172feadbc1a0e816c853f',
}


def git_blob(path):
    data = path.read_bytes()
    return hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()


def run():
    work = Path(os.environ['RUNNER_TEMP']) / 'trace-pinned-harness'
    work.mkdir()
    for name, expected in FILES.items():
        path = work / name
        url = f'https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis/{PIN}/proof-bench/{name}'
        subprocess.run(['curl','-fsSL','--retry','2','--max-time','45','-o',path,url],check=True)
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f'unexpected pinned harness file {name}')
    shutil.copyfile(HERE/'cases.json',work/'cases.json')
    settings=json.loads((work/'cases.json').read_text());case=settings['cases'][0]
    spec=importlib.util.spec_from_file_location('trace_harness',work/'proof.py')
    h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
    original_inputs,original_apply,original_build=h.inputs,h.apply_variant,h.build

    def checked_inputs(project,ci,prep,revision):
        mp,mf,rec=original_inputs(project,ci,prep,revision)
        if any(rec.get(k)!=v for k,v in settings['receipt'].items()):
            raise ValueError('unexpected successful-build receipt')
        rows={r[0]:r[1] for r in map(json.loads,gzip.decompress(mf).splitlines()[1:])}
        if any(rows.get(n)!=v for n,v in settings['input_hashes'].items()):
            raise ValueError('unexpected root or direct importer build input hash')
        return mp,mf,rec

    def checked_graph(src):
        canonical=h.load('trace_quick_check',src.parent/'scripts/quick-check.py')
        graph={'.'.join(p.relative_to(src).with_suffix('').parts):canonical.imports(p) for p in src.rglob('*.lean')}
        # Neither side of the historical patch changes a module header. Check the
        # two changed files against the checked-out repository's full import parser.
        for n in case['targets']:
            p=src/Path(*n.split('.')).with_suffix('.lean')
            if graph[n]!=[v.decode() for v in h.IMPORT.findall(p.read_bytes())]:
                raise ValueError(f'pinned harness parser differs on changed module {n}')
        return graph

    def checked_variant(main,dest,patches):
        touched=original_apply(main,dest,patches)
        for n,blob in settings['source_blobs']['old' if patches else 'new'].items():
            p=dest/'src'/Path(*n.split('.')).with_suffix('.lean')
            if git_blob(p)!=blob:
                raise ValueError(f'unexpected source in {dest.name}: {n}')
        return touched

    def checked_build(arm,targets,dest,label,check_extra=False):
        cpu=original_build(arm,targets,dest,label,check_extra=check_extra)
        if label.startswith('importers-'):
            row=json.loads((dest/(label+'.json')).read_text())
            expected=set(arm[4])-set(case['targets'])
            actual=Counter(r['module'] for r in row['actual_compilers'] if r['project'] and r['exit_code']==0)
            if actual!=Counter(expected):
                raise ValueError(f'importer build differed from exact affected set: {actual.keys()^expected}')
            print(f'{label}: {len(targets)} direct importers and {len(actual)-len(targets)} intermediates verified',flush=True)
        return cpu

    h.inputs,h.source_graph,h.apply_variant,h.build=checked_inputs,checked_graph,checked_variant,checked_build
    h.main()


if __name__=='__main__':
    run()
