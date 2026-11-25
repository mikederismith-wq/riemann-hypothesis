"""Check the two legacy reflexivity proofs using only the published provider and its exact dependencies."""
from types import SimpleNamespace
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


PROVIDER = 'Formalism.PolynomialDimension.MultinomialDepth.MonoCount'
PROVIDER_BLOB = 'f77a67a5621957785bd48afa197b93936cb6f110'
LEGACY = 'Formalism.PolynomialDimension.MultinomialDepth.TieOps'
LEGACY_OLEAN = 'c80ba9efe1d4e843a3c284961bcb5a7c6801375bb4b8a97e3294bde6ab2c43b1'
WANTED = ['Formalism.CountingSumsFrames.TO.ext.eq_1', 'Formalism.CountingSumsFrames.TO.slc.eq_1']


def compare(sup, spec, main, graph, published, host, ci, prepare, toolchain, packages):
    mp, mf, receipt = published
    if spec['name'] != 'tie-slices' or spec['targets'] != [LEGACY]:
        raise ValueError('unexpected measured case')
    if receipt['candidate_head'] != HEAD or receipt['build_exit_code'] != 0:
        raise ValueError('expected successful exact-main publication')
    source = 'src/' + PROVIDER.replace('.', '/') + '.lean'
    if ci.git(main, 'rev-parse', 'HEAD:' + source) != PROVIDER_BLOB or PROVIDER in spec['source_blobs']:
        raise ValueError('shared provider changed from the proof-checked refactor')
    deps = sup.cone(graph, [PROVIDER])
    if len(deps) != 11 or LEGACY in deps:
        raise ValueError(f'unexpected shared-provider import closure: {sorted(deps)}')
    entries, hashes = prepare.manifest_artifacts(mf, mp, receipt, modules=deps | {LEGACY})
    if len(entries) != len(deps) + 1:
        raise ValueError('missing published proof artifact')
    shared = sup.ROOT / 'compressed'
    prepare.downloads(shared, entries, hashes)
    rows = {r[0]: r for line in gzip.decompress(mf).splitlines()[1:] if (r := json.loads(line))}

    with tempfile.TemporaryDirectory(prefix='published-slices-', dir=sup.ROOT) as tmp:
        work = Path(tmp)
        for path in ('cache/artifacts', 'result/legacy', 'control', 'extract'):
            (work / path).mkdir(parents=True)
        result = work / 'result'
        (main / '.lake/packages').mkdir(parents=True, exist_ok=True)
        overrides = ci.package_overrides(main, work / 'control')
        args = SimpleNamespace(baseline_manifest=sup.ROOT / 'modules.gz',
                               baseline_map=sup.ROOT / 'outputs.jsonl',
                               baseline_manifest_sha256=receipt['module_manifest_sha256'], baseline_cache=shared)
        _, jobs, _ = ci.baseline(args, main, work / 'cache', modules=deps)
        if len(jobs) != len(deps):
            raise ValueError('verified provider archive selection changed')
        cmd = host.sandbox(toolchain, main, packages, work / 'cache', result, work / 'control')
        sup.run(*cmd, '/opt/lean/bin/leantar', '--jobs', '4', '-f', '-x', '-j', '-',
                input=json.dumps(jobs), text=True)

        _, dependency_hash, archive, archive_sha = rows[LEGACY]
        artifact = shared / 'artifacts' / archive
        if entries[dependency_hash] != archive or digest(artifact) != archive_sha:
            raise ValueError('legacy archive differs from the exact-main receipt')
        extract = work / 'extract'
        job = dict(file=str(artifact), base=[str(extract), str(extract)], hash=dependency_hash)
        sup.run(toolchain / 'bin/leantar', '--jobs', '1', '-f', '-x', '-j', '-', input=json.dumps([job]), text=True)
        if json.loads((extract / 'TieOps.trace').read_text())['depHash'] != dependency_hash:
            raise ValueError('legacy trace differs')
        old = result / 'legacy/TieOps.olean'
        shutil.copyfile(extract / old.name, old)
        if digest(old) != LEGACY_OLEAN:
            raise ValueError('legacy public module differs from the measured old build')
        sup.write(OUT / 'official-inputs.json', dict(provider=PROVIDER, provider_blob=PROVIDER_BLOB,
                  restored_archives={name: rows[name][3] for name in sorted(deps)},
                  legacy_module=LEGACY, legacy_public_olean_sha256=LEGACY_OLEAN))

        shutil.copyfile(HERE / 'Check.lean', result / 'Check.lean')
        log = OUT / 'kernel.log'
        with log.open('w') as stream:
            proc = subprocess.run([*cmd, '/usr/bin/env', 'RH_LEAN_TIMES=/work/result/compiler.jsonl',
                                   'LEAN_NUM_THREADS=2', '/usr/bin/timeout', '10m', '/opt/lean/bin/lake',
                                   '--packages', overrides, 'env', '/opt/lean/bin/lean', '-R', '/work/result',
                                   '-o', '/work/result/Check.olean', '/work/result/Check.lean'],
                                  stdout=stream, stderr=subprocess.STDOUT)
        for filename in ('compiler.jsonl', 'legacy-equations.json'):
            if (result / filename).is_file():
                shutil.copyfile(result / filename, OUT / filename)
        if proc.returncode:
            print(log.read_text(errors='replace')[-14000:], flush=True)
            raise ValueError(f'Lean kernel check exited {proc.returncode}')
        rows = [json.loads(line) for line in (OUT / 'compiler.jsonl').read_text().splitlines()]
        if len(rows) != 1 or rows[0]['project'] or rows[0]['exit_code'] != 0 or rows[0]['module'] != '/work/result/Check.lean':
            raise ValueError(f'unexpected compiler invocations: {rows}')
        verified = json.loads((result / 'legacy-equations.json').read_text())
        if verified != {'equations': WANTED, 'failures': []}:
            raise ValueError(f'wrong kernel-checked equations {verified}')
        print('Kernel proved both exact legacy equations using the published provider.', flush=True)


if __name__ == '__main__':
    OUT.mkdir(exist_ok=True)
    try:
        sup = engine()
        sup.benchmark_case = lambda *args: compare(sup, *args)
        sup.main()
    except Exception as exc:
        (OUT / 'kernel-error.json').write_text(json.dumps({'error': str(exc), 'traceback': traceback.format_exc()}, indent=2) + '\n')
        raise
