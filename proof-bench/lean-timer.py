#!/usr/bin/python3
"""Time the real stock Lean compiler used by Lake; forward unmeasured queries unchanged."""
import json
import os
from pathlib import Path
import subprocess
import sys
import time

real = Path(__file__).with_name("lean-real")
log = os.environ.get("RH_LEAN_TIMES")
sources = [Path(s).resolve() for s in sys.argv[1:] if s.endswith(".lean")]
if not (log and sources and "-o" in sys.argv):
    os.execv(real, [sys.argv[0], *sys.argv[1:]])
source = next((s for s in sources if s.is_relative_to("/work/project/src")), sources[0])
project = source.is_relative_to("/work/project/src")
module = ".".join(source.relative_to("/work/project/src").with_suffix("").parts) if project else str(source)
start = time.monotonic()
proc = subprocess.Popen([sys.argv[0], *sys.argv[1:]], executable=real)
_, status, use = os.wait4(proc.pid, 0)
code = os.waitstatus_to_exitcode(status)
proc.returncode = code
row = dict(module=module, project=project, exit_code=code, wall_s=time.monotonic()-start,
           user_s=use.ru_utime, system_s=use.ru_stime, cpu_s=use.ru_utime+use.ru_stime, max_rss_kb=use.ru_maxrss)
with open(log, "a") as f:
    f.write(json.dumps(row) + "\n")
sys.exit(code if code >= 0 else 128-code)
