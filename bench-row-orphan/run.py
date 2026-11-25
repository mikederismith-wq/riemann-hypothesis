"""Compare the current legacy row construction against deletion, charging the direct importer."""
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


HERE = Path(__file__).resolve().parent
FORK = 'https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis'
PIN = '1e6be6d46906f4b4f891a68a7d493782003c8bab'
DIGESTS = {
    'proof.py': '2ab4a3a0bc574bf69e3d41cd5d38395d0f2e1f058b44c46c30677aceefdf804d',
    'lean-timer.py': '4e6ee472c842640d3611b55ec2f90c0f5f92de992cd0e188d40644d20e4a62c4',
}
CONFIG = json.loads((HERE/'cases.json').read_text())
CASE = CONFIG['cases'][0]
PRODUCER, = CASE['targets']
IMPORTER, = CASE['direct_importers']
MODULES = (PRODUCER, IMPORTER)


def source(project, module):
    return project/'src'/Path(*module.split('.')).with_suffix('.lean')


def blob(path):
    content = path.read_bytes()
    return hashlib.sha1(f'blob {len(content)}\0'.encode() + content).hexdigest()


def load_support():
    here = Path(os.environ['RUNNER_TEMP'])/'rows-support'
    here.mkdir()
    for name, expected in DIGESTS.items():
        p = here/name
        subprocess.run(['curl','-fsSL','--retry','2','--max-time','60','-o',p,
                        f'{FORK}/{PIN}/proof-bench/{name}'],check=True)
        if hashlib.sha256(p.read_bytes()).hexdigest() != expected:
            raise ValueError(f'unexpected support file {name}')
    for name in ('cases.json','proof.patch'):
        shutil.copyfile(HERE/name, here/name)
    if hashlib.sha256((here/'proof.patch').read_bytes()).hexdigest() != CONFIG['patch_sha256']:
        raise ValueError('candidate patch digest changed')
    spec = importlib.util.spec_from_file_location('proof_bench', here/'proof.py')
    bench = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(bench)
    return bench


def inspect_api(bench, arms, out):
    _, command, result, overrides, _ = arms['new']
    top = {}
    for side, arm in arms.items():
        destination = result/side
        destination.mkdir()
        top[side] = {}
        for mod in MODULES:
            stem = arm[0]/'.lake/build/lib/lean'/Path(*mod.split('.'))
            for suffix in ('.olean','.olean.server','.olean.private'):
                shutil.copyfile(stem.with_suffix(suffix), destination/(mod+suffix))
            doc = json.loads(stem.with_suffix('.ilean').read_text())
            if doc['module'] != mod:
                raise ValueError('wrong compiler index')
            top[side][mod] = set(doc['decls'])
    declared = set(CONFIG['public_removals'])
    for mod in MODULES:
        old, new = top['old'][mod], top['new'][mod]
        missing = {n for n in old-new if not n.startswith('_')}
        added = {n for n in new-old if not n.startswith('_')}
        if missing != (declared if mod==PRODUCER else set()) or added:
            raise ValueError(f'unexpected change to public source declarations in {mod}: {missing}, {added}')
    private_suffix = '.' + CONFIG['private_removal']
    if not any(n.endswith(private_suffix) for n in top['old'][PRODUCER]-top['new'][PRODUCER]):
        raise ValueError('missing private helper deletion')
    shutil.copyfile(HERE/'Check.lean',result/'Check.lean')
    log = out/'kernel.log'
    with log.open('wb') as stream:
        check = subprocess.run([*command,'/usr/bin/env','LEAN_NUM_THREADS=2','/usr/bin/timeout','15m',
                                '/opt/lean/bin/lake','--packages',overrides,'env','/opt/lean/bin/lean',
                                '/work/result/Check.lean'],stdout=stream,stderr=subprocess.STDOUT)
    if check.returncode:
        print(log.read_text(errors='replace')[-9000:],flush=True)
        raise RuntimeError('retained public signature check failed')
    report = json.loads((result/'signatures.json').read_text())
    shutil.copyfile(result/'signatures.json',out/'signatures.json')
    if [r['module'] for r in report] != list(MODULES):
        raise ValueError('incomplete signature report')
    for row in report:
        removed, checked = set(row['removed']), set(row['retained_types'])
        if not checked or not (set(n for n in top['new'][row['module']] if not n.startswith('_')) <= checked):
            raise ValueError(f'missing retained public source types in {row["module"]}')
        if row['module'] == IMPORTER and removed:
            raise ValueError('direct importer lost public declarations')
        if row['module'] == PRODUCER:
            if not declared <= removed:
                raise ValueError('missing expected producer removals')
            # Equation lemmas, projections and constructors are exposed beneath their original name.
            unrelated = [n for n in removed if not any(n == root or n.startswith(root+'.') for root in declared)]
            if unrelated:
                raise ValueError(f'additional compiled public removals need review: {unrelated}')
    print('Kernel compared all retained public types', [(r['module'],len(r['retained_types'])) for r in report],flush=True)


def compare(bench, case, main, graph, published, host, ci, prep, toolchain, packages):
    out = bench.OUT/case['name']
    out.mkdir()
    bench.write(out/'configuration.json',CONFIG)
    with tempfile.TemporaryDirectory(prefix='row-orphan-',dir=bench.ROOT) as tmp:
        arms = {}
        for side, patches in case['variants'].items():
            bench.disk('verified reduced source and cache for '+side, 12)
            arms[side] = bench.initialize_arm(Path(tmp),side,patches,case,main,graph,published,host,ci,prep,toolchain,packages)
            if set(arms[side][-1]) != set(MODULES):
                raise ValueError('unexpected affected modules in target and importer cone')
        def measure(side, label):
            totals = {}
            for module in MODULES:
                short = module.rsplit('.',1)[1]
                name = label+'-'+short
                out_cpu = bench.build(arms[side],[module],out,name,check_extra=True)
                data = json.loads((out/(name+'.json')).read_text())
                rows = data['actual_compilers']
                if Counter(r['module'] for r in rows if r['project'] and not r['exit_code']) != Counter([module]) or len(rows)!=1:
                    raise ValueError(f'unexpected actual compiler invocations in {name}')
                totals[module] = out_cpu[module]
            return totals
        for side in ('old','new'):
            measure(side,'warmup-'+side)
        observations=[]
        def pair(first,second):
            values={}
            for side in (first,second):
                values[side]=measure(side, f'pair-{len(observations)+1}-{side}')
            observations.append(values)
            bench.write(out/'paired-cpu.json',observations)
        pair('old','new')
        pair('new','old')
        def savings(row, module=None):
            return ((row['old'][module]-row['new'][module]) if module else
                    sum(row['old'].values())-sum(row['new'].values()))
        extend=(all(savings(r,PRODUCER)>0 and savings(r)>0 for r in observations)
                and statistics.median(savings(r) for r in observations)>=8)
        if extend:
            pair('old','new')
            pair('new','old')
        report={'pairs':len(observations),'extended':extend,
                'median_seconds':{s:{n:statistics.median(r[s][n] for r in observations) for n in MODULES}
                                  for s in ('old','new')},
                'paired_producer_plus_importer_cpu_savings':[savings(r) for r in observations]}
        bench.write(out/'summary.json',report)
        print(json.dumps(report,indent=2),flush=True)
        # Types are checked independently of the timed compiler invocations.
        inspect_api(bench,arms,out)


def main():
    bench = load_support()
    original_inputs = bench.inputs
    original_variant = bench.apply_variant
    def inputs(project,ci,prep,revision):
        result = original_inputs(project,ci,prep,revision)
        if result[2].get('build_exit_code') != 0 or any(result[2].get(k)!=v for k,v in CONFIG['receipt'].items()):
            raise ValueError('unrecognized current-main compiler receipt')
        return result
    def graph(src):
        parser = bench.load('rows_import_parser',src.parent/'scripts/quick-check.py')
        return {'.'.join(p.relative_to(src).with_suffix('').parts):parser.imports(p) for p in src.rglob('*.lean')}
    def variant(main,dest,patches):
        changed = original_variant(main,dest,patches)
        if changed != ({PRODUCER} if dest.name=='new' else set()):
            raise ValueError('source overlay changed the wrong modules')
        parser = bench.load('rows_import_check',main/'scripts/quick-check.py')
        for mod in MODULES:
            if blob(source(dest,mod))!=CONFIG['source'][mod][dest.name]:
                raise ValueError('unexpected '+dest.name+' source for '+mod)
            direct=parser.imports(source(dest,mod))
            if direct != parser.imports(source(main,mod)) or direct != [b.decode() for b in bench.IMPORT.findall(source(dest,mod).read_bytes())]:
                raise ValueError('changed import list or dependency discrepancy')
        return changed
    bench.inputs=inputs
    bench.source_graph=graph
    bench.apply_variant=variant
    bench.benchmark_case=lambda *args:compare(bench,*args)
    bench.main()


if __name__=='__main__':
    main()
