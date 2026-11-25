"""Check the exact TieOps candidate and its two direct importers on post-batch-13 main."""
from collections import Counter
from types import SimpleNamespace
import statistics
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import traceback

HERE = Path(__file__).resolve().parent
TEMP = Path(os.environ['RUNNER_TEMP']).resolve()
MODULES = TEMP / 'slice-check-engine'
OUT = TEMP / 'rh-proof-results'
BENCH = '9ca6441e25fabb007d07f008ede2cd34848801a2'
HEAD = '27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59'
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


SYM = 'Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SymmetryFinitenessWindowLevelDimOnAdmissible'
TARGET = 'Formalism.PolynomialDimension.MultinomialDepth.TieOps'
LATTICE = 'Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.LatticeTheoremEps28Valid'
PRIOR_CANDIDATE_PUBLIC = {
    TARGET: '41a5d7bada4772be50aaac989e6d4c42030bb0de8fb313481bd929909a24b0c9',
    SYM: 'b9e9a25b37be10852f65eec7146be8199fd96e7d5e4b55bfeef796651f9622ba',
    LATTICE: '5e84bff56527a71e4938aeb59af3b12254b9beff83f642d0ace5756427829e0c',
}
CANDIDATE_PRIVATE = {
    TARGET: '22958a260c47b56d60c1c8976ccdc0695477f6a4cc6e6304048a2faad541ce84',
    SYM: '70a9071eedec8d9055ae5eb71708cc5430256955f9f2d9186fc93164332ab862',
    LATTICE: 'cb12deb24c1925b016e1a2b78a03d7572a607b1720f81d78ad5fed0a77cbb381',
}


def source_graph(sup, src):
    parser = sup.load('current_slices_quick', src.parent / 'scripts/quick-check.py')
    graph = {'.'.join(p.relative_to(src).with_suffix('').parts): parser.imports(p) for p in src.rglob('*.lean')}
    if len(graph) != 59582:
        raise ValueError('unexpected number of current-main source files')
    return graph


def warm_unedited(sup, main, graph, published, host, ci, prepare, toolchain, packages, work):
    mp, mf, receipt = published
    deps = sup.cone(graph, [SYM])
    if len(deps) != 326:
        raise ValueError('wrong Symmetry control dependency closure')
    entries, hashes = prepare.manifest_artifacts(mf, mp, receipt, modules=deps)
    if len(entries) != len(deps):
        raise ValueError('missing stock Symmetry artifact')
    shared = sup.ROOT / 'compressed'
    prepare.downloads(shared, entries, hashes)
    for path in ('cache/artifacts', 'result', 'control'):
        (work / path).mkdir(parents=True)
    (main / '.lake/packages').mkdir(parents=True, exist_ok=True)
    overrides = ci.package_overrides(main, work / 'control')
    args = SimpleNamespace(baseline_manifest=sup.ROOT / 'modules.gz', baseline_map=sup.ROOT / 'outputs.jsonl',
                           baseline_manifest_sha256=receipt['module_manifest_sha256'], baseline_cache=shared)
    _, jobs, _ = ci.baseline(args, main, work / 'cache', modules=deps)
    if len(jobs) != len(deps):
        raise ValueError('incorrect number of input archives')
    cmd = host.sandbox(toolchain, main, packages, work / 'cache', work / 'result', work / 'control')
    sup.run(*cmd, '/opt/lean/bin/leantar', '--jobs', '4', '-f', '-x', '-j', '-', input=json.dumps(jobs), text=True)
    return main, cmd, work / 'result', overrides, []


def compare(sup, spec, main, graph, published, host, ci, prepare, toolchain, packages):
    roots = spec['targets'] + spec['direct_importers']
    if spec['name'] != 'tie-slices' or set(roots) != {TARGET, SYM, LATTICE}:
        raise ValueError('unexpected case')
    if published[2]['candidate_head'] != HEAD or published[2]['build_exit_code'] != 0:
        raise ValueError('incorrect published main receipt')
    provider = ci.git(main, 'rev-parse', 'HEAD:src/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean')
    if provider != 'f77a67a5621957785bd48afa197b93936cb6f110':
        raise ValueError('wrong provider')
    with tempfile.TemporaryDirectory(prefix='slices-27b-', dir=sup.ROOT) as d:
        work = Path(d)
        candidate = sup.initialize_arm(work, 'candidate', spec['variants']['candidate'], spec, main, graph,
                                       published, host, ci, prepare, toolchain, packages)
        sup.build(candidate, roots, OUT, 'current-candidate')
        built = json.loads((OUT / 'current-candidate.json').read_text())
        compiled = Counter(row['module'] for row in built['actual_compilers'] if row['project'] and row['exit_code'] == 0)
        if compiled != Counter(candidate[-1]) or len(compiled) != 33:
            raise ValueError(f'incorrect project compilation set: {list(compiled)}')
        outputs = built['outputs']
        fingerprints = {n: {'public_identical': outputs[n]['.olean']['sha256'] == PRIOR_CANDIDATE_PUBLIC[n],
                             'private_identical': outputs[n]['.olean.private']['sha256'] == CANDIDATE_PRIVATE[n]}
                        for n in roots}
        sup.write(OUT / 'candidate-comparison.json', fingerprints)
        if not all(row['public_identical'] for row in fingerprints.values()):
            raise ValueError(f'current candidate exported API differs from the kernel-checked candidate: {fingerprints}')

        control = warm_unedited(sup, main, graph, published, host, ci, prepare, toolchain, packages, work / 'control-arm')
        sup.build(control, [SYM], OUT, 'current-symmetry-control-warmup', check_extra=True)
        sup.build(candidate, [SYM], OUT, 'current-symmetry-candidate-warmup', check_extra=True)
        arms = {'main': control, 'candidate': candidate}
        times = {side: [] for side in arms}
        for i, side in enumerate(['main', 'candidate', 'candidate', 'main'] * 2):
            label = f'current-symmetry-{i}-{side}'
            times[side].append(sup.build(arms[side], [SYM], OUT, label, check_extra=True)[SYM])
        summary = {side: {'samples_cpu_s': t, 'median_cpu_s': statistics.median(t)} for side, t in times.items()}
        sup.write(OUT / 'symmetry-paired-comparison.json', summary)
        print('Fresh current-main build and direct-importer check', fingerprints, summary, flush=True)


if __name__ == '__main__':
    OUT.mkdir(exist_ok=True)
    try:
        sup = engine()
        config = MODULES / 'cases.json'
        case = json.loads(config.read_text())
        if case['revision'] != 'fcb6eac7534875d32d68030967e2deae6d686151':
            raise ValueError('unexpected prior benchmark revision')
        case['revision'] = HEAD
        sup.write(config, case)
        sup.source_graph = lambda src: source_graph(sup, src)
        sup.benchmark_case = lambda *args: compare(sup, *args)
        sup.main()
    except Exception as exc:
        (OUT / 'current-error.json').write_text(json.dumps({'error': str(exc), 'traceback': traceback.format_exc()}, indent=2) + '\n')
        raise
