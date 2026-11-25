#!/usr/bin/python3
"""Give a large proof both compiler slots, and an ordinary proof one slot."""
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time


def main():
    timed = Path(__file__).with_name('lean-timed')
    args = sys.argv[1:]
    dest = os.environ.get('RH_WORKER_DIR')
    sources = [Path(a).resolve() for a in args if a.endswith('.lean')]
    if not dest or not sources or '-o' not in args:
        os.execv(timed, [str(timed), *args])
    result = Path(dest)
    root = Path('/work/project/src')
    source = next((p for p in sources if p.is_relative_to(root)), sources[0])
    module = '.'.join(source.relative_to(root).with_suffix('').parts) if source.is_relative_to(root) else str(source)
    large = set((result / 'large-modules.txt').read_text().splitlines())
    exclusive = module in large or not source.is_relative_to(root)
    slots = [(result / f'compiler-{i}.lock').open('a') for i in range(2)]
    if exclusive:
        for fp in slots:
            fcntl.flock(fp, fcntl.LOCK_EX)
    else:
        acquired = False
        while not acquired:
            for fp in slots:
                try:
                    fcntl.flock(fp, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    acquired = True
                    break
                except BlockingIOError:
                    continue
            if not acquired:
                time.sleep(0.2)
    def event(stage):
        with (result / 'worker-events.jsonl').open('a') as stream:
            stream.write(json.dumps(dict(time=time.monotonic(), pid=os.getpid(), module=module,
                                         stage=stage, exclusive=exclusive)) + '\n')
    event('start')
    try:
        # Lake can schedule two external processes. Each compiler has one Lean thread.
        return subprocess.call([str(timed), *args], env={**os.environ, 'LEAN_NUM_THREADS': '1'})
    finally:
        event('finish')


if __name__ == '__main__':
    sys.exit(main())
