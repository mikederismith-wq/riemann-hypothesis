"""Compile the candidate once, then compare its public API with published main using Lean's kernel."""
from collections import Counter
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import traceback

HERE = Path(__file__).resolve().parent
TEMP = Path(os.environ['RUNNER_TEMP']).resolve()
MODULES = TEMP / 'slice-check-engine'
OUT = TEMP / 'rh-proof-results'
BENCH = '9ca6441e25fabb007d07f008ede2cd34848801a2'
HEAD = 'fcb6eac7534875d32d68030967e2deae6d686151'
FORK = 'https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis'
ASSETS = {'proof.py': '04e9bef2749db09b3ad9474f3f076dea5268daa98ca9ea119fc7a836ff697be4',
 'cases.json': 'c0ab9aba07701ba00dccbe52a1fcda498afe67268cf88c33e5d46c4d6f7cc6a9',
 'tie-slices.patch': '39630cab07b761b70e824b81dd3679e9e00c3b1c94198edd50496b0bb92eb439',
 'lean-timer.py': '4e6ee472c842640d3611b55ec2f90c0f5f92de992cd0e188d40644d20e4a62c4'}


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def engine():
    MODULES.mkdir()
    for name, want in ASSETS.items():
        dest = MODULES / name
        subprocess.run(['curl', '-fsSL', '--retry', '2', '--max-time', '50', '-o', str(dest),
                        f'{FORK}/{BENCH}/proof-bench/{name}'], check=True)
        if digest(dest) != want:
            raise ValueError(f'bad pinned benchmark asset {name}')
    spec = importlib.util.spec_from_file_location('slice_measure', MODULES / 'proof.py')
    sup = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(sup)
    return sup


def compare(sup, spec, main, graph, published, host, ci, prepare, toolchain, packages):
    roots = spec['targets'] + spec['direct_importers']
    if spec['name'] != 'tie-slices' or len(roots) != 3:
        raise ValueError('unexpected measured case')
    with tempfile.TemporaryDirectory(prefix='slices-kernel-', dir=sup.ROOT) as work:
        arm = sup.initialize_arm(Path(work), 'candidate', spec['variants']['candidate'],
                                 spec, main, graph, published, host, ci, prepare, toolchain, packages)
        project, cmd, result, overrides, expected = arm
        sup.build(arm, roots, OUT, 'fresh-candidate')
        report = json.loads((OUT / 'fresh-candidate.json').read_text())
        compilers = Counter(x['module'] for x in report['actual_compilers'] if x['project'] and x['exit_code'] == 0)
        if compilers != Counter(expected) or len(compilers) != 33:
            raise ValueError('candidate did not build all 33 affected modules exactly once')

        mp, mf, receipt = published
        if receipt['candidate_head'] != HEAD or receipt['build_exit_code'] != 0:
            raise ValueError('expected successful exact-main publication')
        entries, hashes = prepare.manifest_artifacts(mf, mp, receipt, modules=set(roots))
        if len(entries) != len(roots):
            raise ValueError('missing legacy input')
        cache = sup.ROOT / 'compressed'
        prepare.downloads(cache, entries, hashes)
        rows = {r[0]:r for line in gzip.decompress(mf).splitlines()[1:] if (r:=json.loads(line))}
        dest = result / 'legacy'
        dest.mkdir()
        inputs = {}
        for n in roots:
            _, dependency_hash, archive, checksum = rows[n]
            file = cache / 'artifacts' / archive
            if entries[dependency_hash] != archive or digest(file) != checksum:
                raise ValueError(f'legacy archive differs for {n}')
            with tempfile.TemporaryDirectory(dir=work) as unpacked:
                base = Path(unpacked)
                job = dict(file=str(file), base=[str(base), str(base)], hash=dependency_hash)
                sup.run(toolchain/'bin/leantar', '--jobs', '1', '-f', '-x', '-j', '-', input=json.dumps([job]), text=True)
                short = n.rsplit('.',1)[-1]
                if json.loads((base/(short+'.trace')).read_text())['depHash'] != dependency_hash:
                    raise ValueError(f'legacy trace differs for {n}')
                compiled = dest/(n+'.olean')
                for suffix in ('', '.server', '.private'):
                    shutil.copyfile(base/(short+'.olean'+suffix), dest/(n+'.olean'+suffix))
                inputs[n] = {'archive_sha256':checksum, 'public_olean_sha256':digest(compiled)}
        sup.write(OUT/'official-inputs.json', inputs)
        shutil.copyfile(HERE/'Check.lean', result/'Check.lean')
        label = OUT/'kernel.log'
        with label.open('w') as log:
            proc = subprocess.run([*cmd,'/usr/bin/env','LEAN_NUM_THREADS=2','/usr/bin/timeout','15m',
                                   '/opt/lean/bin/lake','--packages',overrides,'env','/opt/lean/bin/lean',
                                   '/work/result/Check.lean'],stdout=log,stderr=subprocess.STDOUT)
        output = result/'legacy-check.json'
        if output.is_file():
            shutil.copyfile(output, OUT/output.name)
        if proc.returncode != 0:
            print(label.read_text(errors='replace')[-14000:],flush=True)
            raise ValueError(f'Lean kernel check exited {proc.returncode}')
        evidence=json.loads(output.read_text())
        counts={name:len(values) for name,values in evidence.items()}
        if counts != {'surviving_types':218,'replaced_types':75,'definition_values':13,
                      'proof_types':62,'failures':0,'facet_kinds':75}:
            raise ValueError(f'wrong kernel-checked counts {counts}')
        print('Kernel-checked declarations',counts,flush=True)


if __name__ == '__main__':
    OUT.mkdir(exist_ok=True)
    try:
        sup=engine()
        sup.benchmark_case=lambda *args:compare(sup,*args)
        sup.main()
    except Exception as exc:
        (OUT/'kernel-error.json').write_text(json.dumps({'error':str(exc),'traceback':traceback.format_exc()},indent=2)+'\n')
        raise
