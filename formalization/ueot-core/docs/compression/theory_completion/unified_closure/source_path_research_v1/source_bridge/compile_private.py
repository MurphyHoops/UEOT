from pathlib import Path
import datetime
import hashlib
import json
import os
import signal
import subprocess
import sys
import time

base = Path('/workspace/scratch/9a8d58b21e30')
root = base / 'tmp/finite-encoding-20261021/resume-source-bridge'
source = root / 'SourcePolicyPathBridge.lean'
number = int(sys.argv[1])
attempt = root / f'lean-attempt-{number:03d}'
attempt.mkdir(exist_ok=False)
snapshot = attempt / source.name
snapshot.write_bytes(source.read_bytes())
runtime = base / 'tmp/registered-interfaces-20261021/linux-runtime/lean-4.33.1-linux/bin'
cwd = base / 'ueot-integration/formalization/ueot-core'
cmd = [str(runtime / 'lake'), 'env', str(runtime / 'lean'),
       '--root=' + str(root), '-o', str(attempt / 'SourcePolicyPathBridge.olean'),
       str(source)]
env = os.environ.copy()
env['LEAN_NUM_THREADS'] = '1'
env['PATH'] = str(runtime) + os.pathsep + env.get('PATH', '')
receipt = {
    'schema': 'UEOT_PRIVATE_SOURCE_BRIDGE_COMPILE_V1',
    'attempt': number,
    'status': 'RUNNING',
    'source': str(source),
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'source_snapshot': str(snapshot),
    'command': cmd,
    'cwd': str(cwd),
    'LEAN_NUM_THREADS': '1',
    'timeout_seconds': 180,
    'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'production_mutated': False,
    'lake_build_run': False,
}
status = attempt / 'STATUS.json'
status.write_text(json.dumps(receipt, indent=2) + '\n')
log = attempt / 'lean.log'
start = time.monotonic()
with log.open('wb') as output:
    process = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=output,
                               stderr=subprocess.STDOUT, start_new_session=True)
    receipt['process_group'] = process.pid
    receipt['launcher_child_pid'] = process.pid
    status.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'RUNNING', 'attempt': str(attempt),
                      'child_pid': process.pid,
                      'source_sha256': receipt['source_sha256']}), flush=True)
    timed_out = False
    try:
        code = process.wait(timeout=180)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(process.pid, signal.SIGTERM)
        try:
            code = process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            code = process.wait()
receipt.update(
    status='TIMEOUT' if timed_out else ('PASS' if code == 0 else 'FAIL'),
    exit_code=code,
    timed_out=timed_out,
    elapsed_seconds=round(time.monotonic() - start, 3),
    finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    stdout_stderr_log=str(log),
    log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
    source_sha256_after=hashlib.sha256(source.read_bytes()).hexdigest(),
)
olean = attempt / 'SourcePolicyPathBridge.olean'
if olean.exists():
    receipt['olean_sha256'] = hashlib.sha256(olean.read_bytes()).hexdigest()
status.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({key: receipt[key] for key in
                  ['status', 'exit_code', 'timed_out', 'elapsed_seconds', 'log_sha256']}),
      flush=True)
print(log.read_text(errors='replace'), flush=True)
raise SystemExit(124 if timed_out else (code if code >= 0 else 1))
