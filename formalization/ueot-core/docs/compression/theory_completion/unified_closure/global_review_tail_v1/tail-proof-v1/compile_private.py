from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import os
import signal
import subprocess
import sys
import time

BASE = Path('/workspace/scratch/9a8d58b21e30')
ROOT = BASE / 'tmp/core-global-review-20261021/tail-proof-v1'
SOURCE = ROOT / 'SameSourceSurvivalTail.lean'
REPO = BASE / 'ueot-integration'
CWD = REPO / 'formalization/ueot-core'
RUNTIME = BASE / 'tmp/registered-interfaces-20261021/linux-runtime/lean-4.33.1-linux/bin'
MANIFEST = BASE / 'tmp/registered-interfaces-20261021/linux-build-attempt-9/SOURCE_MANIFEST.json'
number = int(sys.argv[1])
review_path = Path(sys.argv[2])
review_sha256 = sys.argv[3]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pin(path):
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha(path)}


lock = (ROOT / 'compile.lock').open('a')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
other_lean = []
for proc in Path('/proc').iterdir():
    if not proc.name.isdigit():
        continue
    try:
        comm = (proc / 'comm').read_text().strip()
        if comm in {'lean', 'lake'}:
            other_lean.append({'pid': int(proc.name), 'comm': comm})
    except (FileNotFoundError, PermissionError, ProcessLookupError):
        continue
if other_lean:
    print(json.dumps({'status': 'PAUSED_OTHER_LEAN_PROCESS', 'processes': other_lean}), flush=True)
    raise SystemExit(75)

assert sha(review_path) == review_sha256, 'Independent review identity changed'
assert sha(ROOT / 'CONTRACT.md') == 'a2dfbb80d0223c5ce91fe003346195eb457896366c410d1c24d0bc2935f28657'
assert sha(ROOT / 'API_INPUTS.json') == '21dc2c3ec7d80bde077f6fc1463a4b54556f3c0d648e26dcf2d9ab29cdaff076'
assert sha(ROOT / 'ENVIRONMENT_REUSE_BINDING.json') == '7bb829eb0886f0effe29b73645dfda546b33b2bbf4818c652d0ea2308ef50153'
api = json.loads((ROOT / 'API_INPUTS.json').read_text())
for item in api['records']:
    assert sha(Path(item['path'])) == item['sha256'], item
build = json.loads(MANIFEST.read_text())['build_identity']
actual_sources = {str(p.relative_to(REPO)): sha(p)
                  for p in [CWD / 'UEOT.lean', *sorted((CWD / 'UEOT').rglob('*.lean'))]}
assert actual_sources == {p['path']: p['sha256'] for p in build['source_files']}
for item in build['environment_files']:
    assert sha(REPO / item['path']) == item['sha256'], item
for item in build['runtime_tools'].values():
    assert sha(Path(item['executable'])) == item['sha256'], item
for key, expected in build['import_environment'].items():
    assert os.environ.get(key, '') == expected, (key, os.environ.get(key))

private = BASE / 'tmp/finite-encoding-20261021'
search_paths = [private / 'safe-prefix-bridge-v1/lean-attempt-003',
                private / 'infinite-source-bridge-v1/lean-attempt-003',
                private / 'resume-killed-formalization/lean-attempt-010',
                private / 'resume-source-bridge/lean-attempt-002']
attempt = ROOT / f'lean-attempt-{number:03d}'
attempt.mkdir(exist_ok=False)
snapshot = attempt / SOURCE.name
snapshot.write_bytes(SOURCE.read_bytes())
olean = attempt / 'SameSourceSurvivalTail.olean'
after_lake = r'''
import os, sys, json
from pathlib import Path
os.environ['LEAN_PATH'] = sys.argv[1] + os.pathsep + os.environ.get('LEAN_PATH', '')
keys = ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'ELAN_TOOLCHAIN', 'LEAN_NUM_THREADS']
Path(sys.argv[2]).write_text(json.dumps({k: os.environ.get(k, '') for k in keys}, indent=2) + '\n')
os.execv(sys.argv[3], sys.argv[3:])
'''
cmd = [str(RUNTIME / 'lake'), 'env', sys.executable, '-c', after_lake,
       os.pathsep.join(map(str, search_paths)), str(attempt / 'ENV_AFTER_LAKE.json'),
       str(RUNTIME / 'lean'), '--root=' + str(ROOT), '-o', str(olean), str(SOURCE)]
env = os.environ.copy()
env['LEAN_NUM_THREADS'] = '1'
env['PATH'] = str(RUNTIME) + os.pathsep + env.get('PATH', '')
receipt = {
    'schema': 'UEOT_SAME_SOURCE_TAIL_COMPILE_ATTEMPT_V1',
    'attempt': number, 'status': 'RUNNING',
    'source': pin(SOURCE), 'source_snapshot': pin(snapshot),
    'command': cmd, 'cwd': str(CWD), 'LEAN_NUM_THREADS': '1',
    'timeout_seconds': 180,
    'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'authorization': 'Root-authorized sole focused Lean process for the same-original-p0 survival-tail endpoint; no whole build/native, Git, production, frozen Stage1-7 or book edits.',
    'no_other_lean_process_at_start': True,
    'contract': pin(ROOT / 'CONTRACT.md'),
    'independent_static_review': pin(review_path),
    'API_inputs': pin(ROOT / 'API_INPUTS.json'),
    'API_record_count_checked': len(api['records']),
    'private_search_paths': list(map(str, search_paths)),
    'production_manifest': pin(MANIFEST),
    'production_complete_source_sha256': build['source_tree_sha256'],
    'production_complete_source_files_checked': len(actual_sources),
    'environment_reuse_binding': pin(ROOT / 'ENVIRONMENT_REUSE_BINDING.json'),
    'runner': pin(Path(__file__)),
    'production_mutated': False, 'lake_build_run': False, 'native_run': False,
}
status = attempt / 'STATUS.json'
status.write_text(json.dumps(receipt, indent=2) + '\n')
log = attempt / 'lean.log'
start = time.monotonic()
with log.open('wb') as output:
    process = subprocess.Popen(cmd, cwd=CWD, env=env, stdout=output,
                               stderr=subprocess.STDOUT, start_new_session=True)
    receipt['process_group'] = process.pid
    status.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'RUNNING', 'attempt': number,
                      'child_pid': process.pid,
                      'source_sha256': receipt['source']['sha256']}), flush=True)
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
receipt.update(status='TIMEOUT' if timed_out else ('PASS' if code == 0 else 'FAIL'),
               exit_code=code, timed_out=timed_out,
               elapsed_seconds=round(time.monotonic() - start, 3),
               finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               stdout_stderr_log=pin(log), source_after=pin(SOURCE))
if olean.exists():
    receipt['olean'] = pin(olean)
actual_env = attempt / 'ENV_AFTER_LAKE.json'
if actual_env.exists():
    receipt['actual_lake_environment'] = pin(actual_env)
status.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({k: receipt[k] for k in ['status', 'exit_code', 'timed_out', 'elapsed_seconds']}), flush=True)
print(log.read_text(errors='replace'), flush=True)
raise SystemExit(124 if timed_out else (code if code >= 0 else 1))
