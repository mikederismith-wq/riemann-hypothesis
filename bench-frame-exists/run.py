"""Measure only the residual frame proof on current RH and the overlapping #1595 changes."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
HARNESS = '1e6be6d46906f4b4f891a68a7d493782003c8bab'
DIGESTS = {
    'proof.py': '2ab4a3a0bc574bf69e3d41cd5d38395d0f2e1f058b44c46c30677aceefdf804d',
    'lean-timer.py': '4e6ee472c842640d3611b55ec2f90c0f5f92de992cd0e188d40644d20e4a62c4',
}

def source(project, module):
    return project / 'src' / Path(*module.split('.')).with_suffix('.lean')

def blob(data):
    return hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()

def run():
    work = Path(os.environ['RUNNER_TEMP']) / 'frame-proof-harness'
    work.mkdir()
    for filename, expected in DIGESTS.items():
        path = work / filename
        url = f'https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis/{HARNESS}/proof-bench/{filename}'
        subprocess.run(['curl', '-fsSL', '--retry', '2', '--max-time', '60', '-o', path, url], check=True)
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f'unexpected pinned {filename}')
    for filename in ('cases.json', 'pending.patch', 'frame.patch'):
        shutil.copyfile(HERE / filename, work / filename)
    settings = json.loads((work / 'cases.json').read_text())
    module = settings['producer']
    spec = importlib.util.spec_from_file_location('frame_harness', work / 'proof.py')
    h = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(h)
    get_inputs = h.inputs

    def inputs(project, ci, prep, revision):
        result = get_inputs(project, ci, prep, revision)
        if any(result[2].get(k) != v for k, v in settings['receipt'].items()):
            raise ValueError('unexpected published RH proof receipt')
        sources = {module: settings['source_blobs']['main'], **settings['providers']}
        for n, identity in sources.items():
            if blob(source(project, n).read_bytes()) != identity:
                raise ValueError(f'wrong baseline source for {n}')
        return result

    def graph(src):
        parser = h.load('frame_imports', src.parent / 'scripts/quick-check.py')
        return {'.'.join(p.relative_to(src).with_suffix('').parts): parser.imports(p)
                for p in src.rglob('*.lean')}

    def benchmark(case, main, imports, published, host, ci, prep, tc, packages):
        dest = h.OUT / case['name']
        dest.mkdir()
        downstream = sorted(n for n, ds in imports.items() if module in ds)
        if downstream != settings['direct_importers']:
            raise ValueError('direct importer list changed since baseline was pinned')
        target = [module]
        subset = h.cone(imports, target + list(settings['providers']))
        if len(subset) != settings['expected_cone']:
            raise ValueError('unexpected dependencies of the pending producer')
        restricted = {n: imports[n] for n in subset}
        workload = {'targets': target, 'direct_importers': [], 'expected_cone': len(subset), 'expected_cold': 1}
        with tempfile.TemporaryDirectory(prefix='frame-', dir=h.ROOT) as tmp:
            arm = h.initialize_arm(Path(tmp), 'pending', ['pending.patch'], workload,
                                   main, restricted, published, host, ci, prep, tc, packages)
            project = arm[0]
            src = source(project, module)
            sides = {'old': src.read_bytes()}
            h.run('git', 'apply', '--check', work / 'frame.patch', cwd=project)
            h.run('git', 'apply', work / 'frame.patch', cwd=project)
            sides['new'] = src.read_bytes()
            for name, data in sides.items():
                if blob(data) != settings['source_blobs'][name]:
                    raise ValueError(f'unexpected {name} proof')
            if arm[-1] != target:
                raise ValueError(f'unexpected cold modules {arm[-1]}')
            h.write(dest / 'scope.json', {'changed': target, 'cold': arm[-1], 'verified_dependencies': len(subset)-1,
                                         'main_cone': len(h.cone(imports, target)), 'pending_cone': len(subset),
                                         'all_direct_importers': downstream, 'source_blobs': settings['source_blobs']})
            order = ['old', 'new', 'old', 'new', 'new', 'old', 'old', 'new', 'new', 'old']
            times = []; outputs = {}
            for index, side in enumerate(order):
                src.write_bytes(sides[side])
                label = f'{index:02d}-{side}'
                seconds = h.build(arm, target, dest, label, check_extra=True)
                row = json.loads((dest / (label + '.json')).read_text())
                current = row['outputs'][module]
                if set(current) != {'.olean', '.olean.private', '.ir.sig'}:
                    raise ValueError(f'missing output facets for {side}')
                if side in outputs and outputs[side] != current:
                    raise ValueError(f'nonreproducible {side} output')
                outputs[side] = current
                times.append({'side': side, 'cpu_s': seconds[module], 'lake_wall_s': row['wall_s']})
                h.write(dest / 'observations.json', times)
                print(side, label, times[-1], flush=True)
            median = {side: statistics.median(r['cpu_s'] for r in times[2:] if r['side']==side) for side in sides}
            pairs = []
            for k in range(2, len(order), 2):
                values = {r['side']: r['cpu_s'] for r in times[k:k+2]}
                pairs.append(values['old'] - values['new'])
            h.write(dest / 'summary.json', {'producer_cpu_medians': median, 'paired_cpu_savings': pairs,
                     'output_facets_identical': {k: outputs['old'][k] == outputs['new'][k] for k in outputs['old']}})

    h.inputs = inputs
    h.source_graph = graph
    h.benchmark_case = benchmark
    h.main()

if __name__ == '__main__':
    run()
