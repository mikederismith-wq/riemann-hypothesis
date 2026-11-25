import argparse
import errno
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from unittest.mock import patch


HERE = Path(__file__).resolve().parent
CASE = json.loads((HERE / 'case.json').read_bytes())


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True).strip()


def cpu():
    me = resource.getrusage(resource.RUSAGE_SELF)
    child = resource.getrusage(resource.RUSAGE_CHILDREN)
    return me.ru_utime + me.ru_stime + child.ru_utime + child.ru_stime


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def usage(project):
    logical = blocks = files = dirs = 0
    for root, names, leaves in os.walk(project):
        dirs += len(names)
        for leaf in leaves:
            st = (Path(root) / leaf).stat()
            logical += st.st_size
            blocks += st.st_blocks
            files += 1
    return dict(files=files, directories=dirs, logical_bytes=logical, allocated_file_bytes=blocks * 512)


def run_snapshot(ci, historic, mode, work, art):
    with tempfile.TemporaryDirectory(dir=work) as tmp:
        project = Path(tmp) / 'project'
        project.mkdir()
        # Preserve an authenticated compiler-output LTAR at the same location used by Lake.
        prior = project / '.lake/build/ir/Main.ltar'
        prior.parent.mkdir(parents=True)
        shutil.copyfile(art, prior)
        prior_hash = sha(prior)
        prior_ino = prior.stat().st_ino
        prior_usage = usage(project)
        at = project / CASE['failure_file']
        old_open = Path.open
        seen = []

        def open_file(path, mode_='r', *args, **kwargs):
            if mode == 'interrupted' and path == at and mode_ == 'wb':
                seen.append(str(path.relative_to(project)))
                raise OSError(errno.ENOSPC, 'injected at observed upstream source path', str(path))
            return old_open(path, mode_, *args, **kwargs)

        t = time.monotonic()
        c = cpu()
        try:
            with patch.object(Path, 'open', open_file):
                ci.snapshot(historic, CASE['incident']['candidate_head'], project)
        except OSError as e:
            if mode != 'interrupted' or e.errno != errno.ENOSPC or seen != [CASE['failure_file']]:
                raise
        else:
            assert mode == 'complete', 'expected original ENOSPC was not raised'
        measured = dict(wall_seconds=round(time.monotonic()-t, 6), cpu_seconds=round(cpu()-c, 6))
        final = usage(project)
        retained = {name: final[name] - prior_usage[name] for name in final}
        assert sha(prior) == prior_hash == CASE['prior_artifact']['row'][3]
        assert prior.stat().st_ino == prior_ino
        return {**measured, 'snapshot_inputs_left':retained, 'prior_compiler_archive':prior_hash,
                'prior_compiler_inode_preserved':True, 'injected_at':seen}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--historical', type=Path, required=True)
    parser.add_argument('--artifact', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args=parser.parse_args()
    scripts=HERE.parent/'scripts'
    historic=args.historical.resolve()
    assert git(historic,'rev-parse',"HEAD:src") == CASE['incident']['source_tree']
    assert sha(args.artifact) == CASE['prior_artifact']['row'][3]
    assert args.artifact.stat().st_size == CASE['prior_artifact']['bytes']
    assert git(HERE.parent,'hash-object','scripts/_snapshot_old_ci.py') == 'e6039859107aa50e7271d3019c7d560cfbd24dae'
    assert git(HERE.parent,'hash-object','scripts/ci-build.py') == '3c26797c05ee560b791a00ec33f17aa0b45b8f31'
    cis={'old':load('snapshot_old',scripts/'_snapshot_old_ci.py'),'new':load('snapshot_new',scripts/'ci-build.py')}
    args.work.mkdir(parents=True,exist_ok=True)
    rows=[]
    warm=run_snapshot(cis['old'],historic,'complete',args.work,args.artifact)
    for pair,order in enumerate((('old','new'),('new','old')),1):
        for mode in ('interrupted','complete'):
            for variant in order:
                result=run_snapshot(cis[variant],historic,mode,args.work,args.artifact)
                entry={'pair':pair,'variant':variant,'mode':mode,**result}
                values=result['snapshot_inputs_left']
                if mode=='complete':
                    assert values==warm['snapshot_inputs_left']
                elif variant=='old':
                    assert (values['files'],values['directories'],values['logical_bytes'])==(CASE['source_files_before_failure'],CASE['dirs_before_failure'],CASE['bytes_before_failure'])
                else:
                    assert all(v==0 for v in values.values())
                rows.append(entry)
                print(json.dumps(entry),flush=True)
                args.output.parent.mkdir(parents=True,exist_ok=True)
                args.output.write_text(json.dumps({'case':CASE,'warm':warm,'rows':rows},indent=2)+'\n')
    for mode in ('interrupted','complete'):
        print(mode, {v:{k:statistics.median(row[k] for row in rows if row['mode']==mode and row['variant']==v) for k in ('cpu_seconds','wall_seconds')} for v in cis}, flush=True)


if __name__=='__main__':
    main()
