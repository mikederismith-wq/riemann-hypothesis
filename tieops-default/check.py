"""Run the stock, default RH build with an exact published base and a cold changed subtree."""
from collections import Counter, defaultdict
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import tomllib
import traceback
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
TEMP = Path(os.environ['RUNNER_TEMP']).resolve()
OUT = TEMP / 'rh-proof-results'
PIN = '27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59'
FORK = 'https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis'
SUPPORT = ('eddb75a2e8ebfa4a4859de09eaee98471a94c7f4', 'kernel-check/verify.py',
           '39b402dc7bf9de20d69e377203f05a4a323d1663d7632a1062cdb9ec3cb3226a')
STAGER = ('c1f8178451258c3f132c6c579c2dff9d3354dddc', 'ks-downstream/check.py',
          'e4080ada3787f4a4283825c186389edc92547338d0639a724f84636066eb0653')
SET_DIGEST = '1eb76ee0524d517f2aee83915bb16f6c4a70a0ec00a0abeb5d6fddba95da6490'
LARGE_DIGEST = '5caa5d054f35e06be2ef8761c4af17b791243be88bd3849e3cd3bfd1a582b89e'
GIB = 1024**3


def checked_helper(name, reference):
    commit, path, sha = reference
    dest = TEMP / f'tie-full-{name}.py'
    subprocess.run(['curl', '-fsSL', '--retry', '2', '--max-time', '45', f'{FORK}/{commit}/{path}', '-o', str(dest)],
                   check=True)
    if hashlib.sha256(dest.read_bytes()).hexdigest() != sha:
        raise ValueError(f'incorrect frozen {name} helper')
    spec = importlib.util.spec_from_file_location('tie_full_' + name, dest)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def default_modules(config, graph, cone):
    roots = set()
    defaults = set(config['defaultTargets'])
    seen = set()
    for lib in config['lean_lib']:
        if lib['name'] not in defaults:
            continue
        seen.add(lib['name'])
        roots.update(lib.get('roots', []))
        for pattern in lib.get('globs', []):
            if not pattern.endswith('.+'):
                raise ValueError('unexpected default module glob')
            roots.update(n for n in graph if n.startswith(pattern[:-1]))
    if seen != defaults:
        raise ValueError('unexpected nonlibrary default target')
    return cone(graph, roots)


def project_variant(sup, spec, main, work):
    project = work / 'candidate'
    project.mkdir()
    for f in sup.CFG:
        shutil.copyfile(main / f, project / f)
    shutil.copytree(main / 'src', project / 'src', copy_function=os.link)
    def checked_source(n, side):
        f = project / 'src' / Path(*n.split('.')).with_suffix('.lean')
        content = f.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\0' + content).hexdigest()
        if blob != spec['source_blobs'][n][side]:
            raise ValueError(f'{side} source mismatch for {n}')
        return f, content
    if len(spec['source_blobs']) != 2:
        raise ValueError('unexpected candidate source footprint')
    for n in spec['source_blobs']:
        f, contents = checked_source(n, 'main')
        f.unlink()
        f.write_bytes(contents)
    patch = sup.HERE / 'tie-slices.patch'
    sup.run('git', 'apply', '--check', patch, cwd=project)
    sup.run('git', 'apply', patch, cwd=project)
    for n in spec['source_blobs']:
        checked_source(n, 'candidate')
    return project


def invoke(label, cmd, result, overrides, extra=(), limit='320m'):
    profile = result / 'compiler.jsonl'
    profile.unlink(missing_ok=True)
    events = result / 'worker-events.jsonl'
    events.unlink(missing_ok=True)
    args = [*cmd, '/usr/bin/env', 'LAKE_ARTIFACT_CACHE=false', 'LEAN_NUM_THREADS=2',
            'RH_LEAN_TIMES=/work/result/compiler.jsonl', 'RH_WORKER_DIR=/work/result',
            '/usr/bin/timeout', '--kill-after=15s', limit, '/opt/lean/bin/lake', '--packages',
            overrides, '--rehash', 'build', *extra]
    name = 'rh-tie-' + label
    args[2:2] = ['--name', name]
    started = time.monotonic()
    stop = None
    with (OUT / (label + '.log')).open('wb') as stream:
        proc = subprocess.Popen(args, stdout=stream, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
        while proc.poll() is None:
            free = shutil.disk_usage(TEMP).free
            if free < 6*GIB or os.statvfs(TEMP).f_favail < 20000:
                stop = 'disk or inode reserve reached'
                subprocess.run(['docker', 'stop', '--time', '10', name], check=False, capture_output=True)
                break
            if time.monotonic() - started > 60 and int(time.monotonic() - started) % 60 < 5:
                count = sum(1 for _ in profile.open()) if profile.is_file() else 0
                print(f'{label}: {count} compiler completions, {free/GIB:.2f} GiB free', flush=True)
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                continue
        status = proc.wait()
    for f in (profile, events):
        if f.is_file():
            shutil.copyfile(f, OUT / (label + '-' + f.name))
    elapsed = time.monotonic() - started
    rows = [json.loads(line) for line in profile.read_text().splitlines()] if profile.exists() else []
    ev = [json.loads(line) for line in events.read_text().splitlines()] if events.exists() else []
    active = {}
    peak = 0
    valid = True
    for e in sorted(ev, key=lambda x:x['time']):
        if e['stage'] == 'start':
            active[e['pid']] = e
            peak = max(peak, len(active))
            if len(active) > 2 or (len(active) > 1 and any(x['exclusive'] for x in active.values())):
                valid = False
        else:
            active.pop(e['pid'], None)
    return dict(exit_code=status, elapsed_wall_s=elapsed, disk_stop=stop, compiler_concurrency_peak=peak,
                bounded_workers=valid and not active, compilers=rows)


def complete(sup, stock, stage, ks, spec, main, graph, published, host, ci, prepare, toolchain, packages):
    mp, mf, rec = published
    if rec['candidate_head'] != PIN or rec['build_exit_code'] != 0 or spec['targets'] != [stock.TARGET]:
        raise ValueError('incorrect main receipt or source target')
    defaults = default_modules(tomllib.loads((main / 'lakefile.toml').read_text()), graph, sup.cone)
    reverse = defaultdict(list)
    for n, imports in graph.items():
        for imported in imports:
            reverse[imported].append(n)
    rev = {n:reverse[n] for n in graph}
    affected = sup.cone(rev, spec['source_blobs'])
    target_hash = hashlib.sha256(('\n'.join(sorted(affected)) + '\n').encode()).hexdigest()
    if target_hash != SET_DIGEST or len(affected) != 1434 or set(rev[stock.TARGET]) != {stock.SYM, stock.LATTICE}:
        raise ValueError('affected importers changed')
    rows = {v[0]:v for line in gzip.decompress(mf).splitlines()[1:] if (v := json.loads(line))}
    if defaults != set(rows) or len(defaults) != 59581 or set(graph) - defaults != {'Challenge'} or not affected <= defaults:
        raise ValueError('default proof inputs do not agree with the successful official full build')
    warm = defaults - affected
    entries, hashes = prepare.manifest_artifacts(mf, mp, rec, modules=warm)
    if len(entries) != 58147 or any(entries[rows[n][1]] != rows[n][2] or hashes[rows[n][2]] != rows[n][3] for n in warm):
        raise ValueError('incorrect signed warm input rows')
    if stock.digest(HERE / 'large-modules.txt') != LARGE_DIGEST:
        raise ValueError('unexpected large-worker list')
    large = set((HERE / 'large-modules.txt').read_text().splitlines())
    if len(large) != 144 or not large <= affected or 'Main' not in large:
        raise ValueError('unexpected high-memory groups')
    sup.write(OUT / 'expected.json', dict(upstream_main=PIN, default_target_count=len(defaults),
              unaffected_warm=len(warm), cold_affected=sorted(affected), large_exclusive=len(large)))

    lean = toolchain / 'bin/lean'
    lean.rename(toolchain / 'bin/lean-timed')
    shutil.copyfile(HERE / 'worker.py', lean)
    lean.chmod(0o755)
    with tempfile.TemporaryDirectory(prefix='tieops-full-', dir=sup.ROOT) as tmp:
        work = Path(tmp)
        project = project_variant(sup, spec, main, work)
        cache, shared, result, control = [work / n for n in ('cache', 'downloads', 'result', 'control')]
        for path in (cache/'artifacts', shared, result, control, project/'.lake/packages'):
            path.mkdir(parents=True)
        shutil.copyfile(HERE / 'large-modules.txt', result / 'large-modules.txt')
        overrides = ci.package_overrides(project, control)
        cmd = ks.offline_sandbox(host, toolchain, project, packages, cache, result, control)
        cmd[2:2] = ['--memory=14g', '--memory-swap=16g']
        opts = SimpleNamespace(baseline_manifest=sup.ROOT/'modules.gz', baseline_map=sup.ROOT/'outputs.jsonl',
                               baseline_manifest_sha256=rec['module_manifest_sha256'], baseline_cache=shared)
        stage.vm('before-restore', cmd)
        stage.restore('full', warm, rows, prepare, ci, opts, project, cache, shared, cmd)
        if shutil.disk_usage(TEMP).free < 6*GIB:
            raise RuntimeError('disk reserve reached after restore')
        lib = project/'.lake/build/lib/lean'
        path = lambda n: lib / Path(*n.split('.')).with_suffix('.olean')
        if any(path(n).exists() for n in affected):
            raise ValueError('an affected proof was prewarmed')
        stage.vm('after-restore', cmd)
        stage.phase('stock-default-build', workers=2, lean_threads=1, high_rss_exclusive=len(large))
        record = invoke('stock-default', cmd, result, overrides)
        compilers = record.pop('compilers')
        compiled = Counter(r['module'] for r in compilers if r['project'] and r['exit_code'] == 0)
        failed = [r['module'] for r in compilers if r['exit_code'] != 0]
        external = [r['module'] for r in compilers if not r['project']]
        missing = sorted(affected - compiled.keys())
        unexpected = sorted(compiled.keys() - affected)
        duplicates = sorted(n for n,c in compiled.items() if c != 1)
        missing_outputs = sorted(n for n in defaults if not path(n).is_file())
        record.update(successful_compilers=len(compiled), missing=missing, unexpected=unexpected,
                      duplicated=duplicates, failed=failed, external=external, missing_outputs=missing_outputs,
                      total_affected_module_cpu_s=sum(r['cpu_s'] for r in compilers if r['project'] and r['exit_code']==0))
        record['unique_outputs'] = {n:stock.digest(path(n)) for n in [stock.TARGET, stock.SYM, stock.LATTICE, 'Main'] if path(n).is_file()}
        record['matched_kernel_verified_public'] = all(record['unique_outputs'].get(n)==h for n,h in stock.PRIOR_CANDIDATE_PUBLIC.items())
        valid = (record['exit_code']==0 and record['disk_stop'] is None and record['bounded_workers'] and
                 record['matched_kernel_verified_public'] and not any([missing, unexpected, duplicates, failed, external, missing_outputs]))
        record['full_default_proof_build_passed'] = valid
        sup.write(OUT/'default-verdict.json', record)
        stage.vm('after-default', cmd)
        if not valid:
            unrelated = sorted(set(failed) & (set(graph)-affected))
            baseline = {'successful_official_receipt': rec['build_receipt_sha256'],
                        'failed_outside_both_changed_reverse_closures': unrelated,
                        'failed_inside_changed_reverse_closure': sorted(set(failed)&affected)}
            # This source and its entire import closure are identical on clean main. Repeat a bounded
            # first unrelated failure on those same unchanged inputs to separate it from the edit.
            if unrelated and not record['disk_stop'] and shutil.disk_usage(TEMP).free > 7*GIB:
                n = unrelated[0]
                if sup.cone(graph,[n]) & set(spec['source_blobs']):
                    raise ValueError('baseline replay unexpectedly depends on the patch')
                baseline['unaffected_source_replay'] = invoke('unchanged-replay',cmd,result,overrides,['+'+n],limit='5m')
            sup.write(OUT/'baseline-context.json',baseline)
            lines = (OUT/'stock-default.log').read_text(errors='replace').splitlines()
            print('\n'.join(lines[-60:])[-14000:], flush=True)
            raise RuntimeError('stock default build failed the exact compiler/output checks; see saved verdict')
        stage.phase('complete', cold_source_checked=len(compiled), exact_warm_inputs=len(warm),
                    actual_lake_default_targets=len(defaults), build_wall_s=record['elapsed_wall_s'])


if __name__ == '__main__':
    OUT.mkdir(exist_ok=True)
    try:
        stock = checked_helper('current', SUPPORT)
        stage = checked_helper('stager', STAGER)
        stage.PIN = PIN
        ks = stage.setup()
        sup = stock.engine()
        config = stock.MODULES/'cases.json'
        case = json.loads(config.read_text())
        if case['revision'] != 'fcb6eac7534875d32d68030967e2deae6d686151':
            raise ValueError('unexpected frozen case')
        case['revision'] = PIN
        sup.write(config,case)
        sup.source_graph = lambda src: stock.source_graph(sup,src)
        sup.benchmark_case = lambda *args: complete(sup,stock,stage,ks,*args)
        sup.main()
    except Exception as exc:
        (OUT/'full-error.json').write_text(json.dumps({'error':str(exc),'traceback':traceback.format_exc()},indent=2)+'\n')
        raise
