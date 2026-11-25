"""Compare the old and new generator-set subproof in the producer's normal Lake compiler context."""
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

import fixtures


HERE=Path(__file__).resolve().parent
REVISION='27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59'
PIN='1e6be6d46906f4b4f891a68a7d493782003c8bab'
FORK='https://raw.githubusercontent.com/mikederismith-wq/riemann-hypothesis'
ASSETS={'proof.py':'2ab4a3a0bc574bf69e3d41cd5d38395d0f2e1f058b44c46c30677aceefdf804d',
        'lean-timer.py':'4e6ee472c842640d3611b55ec2f90c0f5f92de992cd0e188d40644d20e4a62c4'}
CONFIG=json.loads((HERE/'cases.json').read_text())


def read_context():
    work=Path(os.environ['RUNNER_TEMP'])/'row-series-support'
    work.mkdir()
    for name,expected in ASSETS.items():
        dest=work/name
        subprocess.run(['curl','-fsSL','--retry','2','--max-time','60','-o',dest,
                        f'{FORK}/{PIN}/proof-bench/{name}'],check=True)
        if hashlib.sha256(dest.read_bytes()).hexdigest()!=expected:
            raise ValueError(f'incorrect compiler harness {name}')
    shutil.copyfile(HERE/'cases.json',work/'cases.json')
    spec=importlib.util.spec_from_file_location('rows_proof_support',work/'proof.py')
    bench=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(bench)
    return bench


def probe(bench,case,main,graph,published,host,ci,prep,toolchain,packages):
    out=bench.OUT/case['name']
    out.mkdir()
    original=(main/fixtures.PATH).read_bytes()
    inputs=fixtures.variants(original)
    hashes={side:hashlib.sha256(raw).hexdigest() for side,raw in inputs.items()}
    if hashes!=CONFIG['fixture_hashes']:
        raise ValueError('the exact probe source inputs differ from their local preflight')
    subset=bench.cone(graph,[fixtures.MODULE])
    if len(subset)!=5888 or len(graph[fixtures.MODULE])!=61:
        raise ValueError('unexpected complete original import graph')
    only_deps={m:graph[m] for m in subset}
    bench.write(out/'inputs.json',{'commit':REVISION,'producer_blob':fixtures.BLOB,'sha256':hashes,
               'public_and_private_imports':graph[fixtures.MODULE], 'cached_project_dependencies':len(subset)-1})
    with tempfile.TemporaryDirectory(prefix='series-proof-',dir=bench.ROOT) as work:
        arm=bench.initialize_arm(Path(work),'sliced',[],case,main,only_deps,published,host,ci,prep,toolchain,packages)
        project,command,result,overrides,cold=arm
        if cold!=[fixtures.MODULE]:
            raise ValueError('something other than the four-declaration source module would be compiled')
        # A failing elaboration attempt should not spend a full-module timeout on a small proof.
        arm=(project,[*command,'/usr/bin/timeout','--kill-after=5s','180s'],result,overrides,cold)
        file=project/fixtures.PATH
        samples={s:[] for s in inputs}
        failed={}
        # A control warm-up then two paired rounds in opposite order, with an observation
        # for the identical import header/local elaborator in each round.
        order=['control','old','new','control','control','new','old']
        for index,side in enumerate(order):
            if side in failed:
                continue
            file.write_bytes(inputs[side])
            label=f'{index}-{side}'
            try:
                bench.build(arm,[fixtures.MODULE],out,label,check_extra=True)
            except (ValueError,RuntimeError) as exc:
                failed[side]=str(exc)
                log=out/(label+'.log')
                if log.exists():print(log.read_text(errors='replace')[-10500:],flush=True)
                if side!='new':raise
                continue
            report=json.loads((out/(label+'.json')).read_text())
            cpus=report['actual_compilers']
            if len(cpus)!=1 or cpus[0]['module']!=fixtures.MODULE or cpus[0]['exit_code']:
                raise ValueError('unexpected compiler invocation')
            indexed=project/'.lake/build/lib/lean'/Path(*fixtures.MODULE.split('.')).with_suffix('.ilean')
            names=json.loads(indexed.read_text())['decls']
            present={short for short in fixtures.NAMES if any(n.endswith('.'+short) for n in names)}
            expected=set(fixtures.NAMES if side=='old' else (fixtures.NAMES[-1:] if side=='new' else []))
            if present!=expected:
                raise ValueError(f'wrong private declarations actually compiled for {side}: {present}')
            if index:
                samples[side].append(cpus[0])
            bench.write(out/'samples.json',samples)
        cpu={s:[r['cpu_s'] for r in rows] for s,rows in samples.items()}
        medians={s:statistics.median(v) for s,v in cpu.items() if v}
        report={'actual_compiler_cpu_s':cpu,'median_cpu_s':medians,'failed':failed,
                'old_median_above_control_s':medians['old']-medians['control'],
                'old_min_above_max_control_s':min(cpu['old'])-max(cpu['control']),
                'old_max_above_min_control_s':max(cpu['old'])-min(cpu['control'])}
        if len(cpu['new'])==2:
            report['paired_old_minus_new_s']=[a-b for a,b in zip(cpu['old'],cpu['new'])]
        bench.write(out/'summary.json',report)
        print(json.dumps(report,indent=2),flush=True)
        if failed:
            raise ValueError('candidate failed to compile; retained the control and old bounds')


def main():
    bench=read_context()
    oldinputs=bench.inputs
    def inputs(project,ci,prep,revision):
        data=oldinputs(project,ci,prep,revision)
        if revision!=REVISION or data[2].get('build_exit_code')!=0 or any(data[2].get(k)!=v for k,v in CONFIG['receipt'].items()):
            raise ValueError('unexpected published B13 proof cache')
        return data
    def physical_graph(src):
        parser=bench.load('rows_actual_graph',src.parent/'scripts/quick-check.py')
        return {'.'.join(p.relative_to(src).with_suffix('').parts):parser.imports(p) for p in src.rglob('*.lean')}
    bench.inputs=inputs
    bench.source_graph=physical_graph
    bench.benchmark_case=lambda *args:probe(bench,*args)
    bench.main()


if __name__=='__main__':main()
