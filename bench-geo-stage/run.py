"""Compare the two stage-congruence proofs with pinned stock Lean and verified RH inputs."""
from collections import Counter
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess


HERE = Path(__file__).resolve().parent
HARNESS = '1e6be6d46906f4b4f891a68a7d493782003c8bab'
DIGESTS = {
    'proof.py': '2ab4a3a0bc574bf69e3d41cd5d38395d0f2e1f058b44c46c30677aceefdf804d',
    'lean-timer.py': '4e6ee472c842640d3611b55ec2f90c0f5f92de992cd0e188d40644d20e4a62c4',
}
MODULES = 'Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.'
PRODUCER = MODULES + 'GeometricHalfToAnalyticDataEnlargedBase'
IMPORTER = MODULES + 'ExistsExtendedColumnDataAllClausesButPlacesStatement'
IMPORTER_BLOB = 'b0c9c98e048113ae20d27ac658da2674969bba5b'
PRODUCER_BLOBS = {
    'main': '2290f21af0d64238652bc8cbce6043ab68a5be0d',
    'old': 'df2e5f8285182a1a1cc8987e8e7af69fc6c2f600',
    'new': '771688124a9ae926741dc0f024c61b05db16a04b',
}


def source_path(project, name):
    return project / 'src' / Path(*name.split('.')).with_suffix('.lean')


def blob(path):
    data = path.read_bytes()
    return hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()


def run():
    work = Path(os.environ['RUNNER_TEMP']) / 'geo-proof-harness'
    work.mkdir()
    for filename, expected in DIGESTS.items():
        path = work / filename
        url = f'https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis/{HARNESS}/proof-bench/{filename}'
        subprocess.run(['curl', '-fsSL', '--retry', '2', '--max-time', '60', '-o', path, url], check=True)
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f'unexpected {filename} from pinned benchmark')
    for filename in ('cases.json', 'pending.patch', 'joint.patch'):
        shutil.copyfile(HERE / filename, work / filename)
    config = json.loads((work / 'cases.json').read_text())
    spec = importlib.util.spec_from_file_location('stage_harness', work / 'proof.py')
    harness = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(harness)
    original_inputs, original_variant, original_build = harness.inputs, harness.apply_variant, harness.build

    def inputs(project, ci, prep, revision):
        published = original_inputs(project, ci, prep, revision)
        receipt = published[2]
        if any(receipt.get(k) != v for k, v in config['receipt'].items()):
            raise ValueError('unexpected published RH build receipt')
        if blob(source_path(project, PRODUCER)) != PRODUCER_BLOBS['main']:
            raise ValueError('unexpected main producer source')
        return published

    def source_graph(src):
        parser = harness.load('stage_imports', src.parent / 'scripts/quick-check.py')
        return {'.'.join(p.relative_to(src).with_suffix('').parts): parser.imports(p)
                for p in src.rglob('*.lean')}

    def variant(main, dest, patches):
        changed = original_variant(main, dest, patches)
        if changed != {PRODUCER} or blob(source_path(dest, PRODUCER)) != PRODUCER_BLOBS[dest.name]:
            raise ValueError(f'unexpected proof variant in {dest.name}')
        if blob(source_path(dest, IMPORTER)) != IMPORTER_BLOB:
            raise ValueError(f'unexpected direct importer in {dest.name}')
        parser = harness.load('stage_changed_imports', main / 'scripts/quick-check.py')
        source = source_path(dest, PRODUCER)
        if parser.imports(source) != [b.decode() for b in harness.IMPORT.findall(source.read_bytes())]:
            raise ValueError('changed producer header differs between the parsers')
        return changed

    def build(arm, targets, dest, label, check_extra=False):
        cpu = original_build(arm, targets, dest, label, check_extra=check_extra)
        if label.startswith('importers-'):
            row = json.loads((dest / (label + '.json')).read_text())
            compilers = row['actual_compilers']
            observed = Counter(r['module'] for r in compilers if r['project'] and r['exit_code'] == 0)
            if observed != Counter([IMPORTER]) or any(not r['project'] for r in compilers):
                raise ValueError(f'unexpected direct-importer workload: {observed}')
        return cpu

    harness.inputs = inputs
    harness.source_graph = source_graph
    harness.apply_variant = variant
    harness.build = build
    harness.main()


if __name__ == '__main__':
    run()
