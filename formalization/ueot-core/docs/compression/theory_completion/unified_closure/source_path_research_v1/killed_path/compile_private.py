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
root = base / 'tmp/finite-encoding-20261021/resume-killed-formalization'
source = root / 'SameSourceKilledPath.lean'
number = int(sys.argv[1])
full_status = base / 'tmp/registered-interfaces-20261021/linux-build-attempt-8/STATUS.json'
native_status = base / 'tmp/registered-interfaces-20261021/native-repair-sequence-1/STATUS.json'
old_native_status = base / 'tmp/registered-interfaces-20261021/native-sequence-1/STATUS.json'

def read_gate():
    return {str(p): json.loads(p.read_text())
            for p in [full_status, native_status, old_native_status]}

gate = read_gate()
allowed = (gate[str(full_status)].get('state') == 'RUNNING'
           and gate[str(full_status)].get('active') == 'full_ueot'
           and gate[str(native_status)].get('state') == 'WAITING_FOR_ACTUAL_FULL_BUILD'
           and gate[str(old_native_status)].get('state') == 'STOPPED_BEFORE_NATIVE')
if not allowed:
    print(json.dumps({'status': 'PAUSED_BY_FULL_NATIVE_GATE', 'gate': gate}), flush=True)
    raise SystemExit(75)

window = root / 'ACTIVE_COMPILE_WINDOW.json'
if not window.exists():
    window.write_text(json.dumps({'start_unix': time.time(), 'max_wall_seconds': 480,
                                 'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()},
                                indent=2) + '\n')
w = json.loads(window.read_text())
remaining = w['max_wall_seconds'] - (time.time() - w['start_unix'])
if remaining <= 0:
    print(json.dumps({'status': 'PAUSED_WINDOW_EXHAUSTED', 'window': w}), flush=True)
    raise SystemExit(75)
timeout = min(180, remaining)

bridge_root = base / 'tmp/finite-encoding-20261021/resume-source-bridge'
bridge_source = bridge_root / 'SourcePolicyPathBridge.lean'
bridge_cache = bridge_root / 'lean-attempt-002'
bridge_olean = bridge_cache / 'SourcePolicyPathBridge.olean'
assert hashlib.sha256(bridge_source.read_bytes()).hexdigest() == '108500fc13229b8faffc9829d886313167142075112bc3f6c023a086c074ae91'
assert hashlib.sha256(bridge_olean.read_bytes()).hexdigest() == '0ef1132fbfb24b0e571693de99e2729f9a8ede4aa41203fb4b3be67d46915748'

attempt = root / f'lean-attempt-{number:03d}'
attempt.mkdir(exist_ok=False)
snapshot = attempt / source.name
snapshot.write_bytes(source.read_bytes())
original = root / 'SameSourceKilledPath_v1.lean'
if not original.exists():
    original.write_bytes(source.read_bytes())
runtime = base / 'tmp/registered-interfaces-20261021/linux-runtime/lean-4.33.1-linux/bin'
cwd = base / 'ueot-integration/formalization/ueot-core'
after_lake = ('import os,sys; '
              'os.environ["LEAN_PATH"]=sys.argv[1]+os.pathsep+os.environ.get("LEAN_PATH",""); '
              'os.execv(sys.argv[2],sys.argv[2:])')
cmd = [str(runtime / 'lake'), 'env', sys.executable, '-c', after_lake,
       str(bridge_cache), str(runtime / 'lean'), '--root=' + str(root),
       '-o', str(attempt / 'SameSourceKilledPath.olean'), str(source)]
env = os.environ.copy()
env['LEAN_NUM_THREADS'] = '1'
env['PATH'] = str(runtime) + os.pathsep + env.get('PATH', '')
receipt = {
    'schema': 'UEOT_PRIVATE_KILLED_SOURCE_COMPILE_ATTEMPT_V1',
    'attempt': number, 'status': 'RUNNING', 'source': str(source),
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'source_snapshot': str(snapshot), 'command': cmd, 'cwd': str(cwd),
    'LEAN_NUM_THREADS': '1', 'timeout_seconds': timeout,
    'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'gate_before_start': gate,
    'bridge_source_sha256': hashlib.sha256(bridge_source.read_bytes()).hexdigest(),
    'bridge_olean_sha256': hashlib.sha256(bridge_olean.read_bytes()).hexdigest(),
    'bridge_olean_directory': str(bridge_cache),
    'production_mutated': False, 'lake_build_run': False, 'native_run': False,
}
status = attempt / 'STATUS.json'
status.write_text(json.dumps(receipt, indent=2) + '\n')
log = attempt / 'lean.log'
start = time.monotonic()
with log.open('wb') as output:
    process = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=output,
                               stderr=subprocess.STDOUT, start_new_session=True)
    receipt['process_group'] = process.pid
    status.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'RUNNING', 'attempt': number, 'child_pid': process.pid,
                      'source_sha256': receipt['source_sha256'], 'timeout_seconds': timeout}), flush=True)
    timed_out = False
    try:
        code = process.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(process.pid, signal.SIGTERM)
        try:
            code = process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            code = process.wait()
receipt.update(status='TIMEOUT' if timed_out else ('PASS' if code == 0 else 'FAIL'),
               exit_code=code, timed_out=timed_out,
               elapsed_seconds=round(time.monotonic() - start, 3),
               finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               stdout_stderr_log=str(log),
               log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
               source_sha256_after=hashlib.sha256(source.read_bytes()).hexdigest())
olean = attempt / 'SameSourceKilledPath.olean'
if olean.exists():
    receipt['olean_sha256'] = hashlib.sha256(olean.read_bytes()).hexdigest()
status.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({key: receipt[key] for key in ['status', 'exit_code', 'timed_out', 'elapsed_seconds']}), flush=True)
print(log.read_text(errors='replace'), flush=True)
raise SystemExit(124 if timed_out else (code if code >= 0 else 1))
