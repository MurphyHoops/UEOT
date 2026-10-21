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

base = Path('/workspace/scratch/9a8d58b21e30')
root = base / 'tmp/finite-encoding-20261021/infinite-source-bridge-v1'
source = root / 'SameSourceInfinitePrefix.lean'
number = int(sys.argv[1])
timeout = 180


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pin(path):
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha(path)}


lock = (root / 'compile.lock').open('a')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
other_lean = []
for process_dir in Path('/proc').iterdir():
    if not process_dir.name.isdigit():
        continue
    try:
        comm = (process_dir / 'comm').read_text().strip()
        if comm in {'lean', 'lake'}:
            other_lean.append({'pid': int(process_dir.name), 'comm': comm,
                               'cmdline': (process_dir / 'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace')})
    except (FileNotFoundError, PermissionError, ProcessLookupError):
        continue
if other_lean:
    print(json.dumps({'status': 'PAUSED_OTHER_LEAN_PROCESS', 'processes': other_lean}), flush=True)
    raise SystemExit(75)

bridge_root = base / 'tmp/finite-encoding-20261021/resume-source-bridge'
bridge_cache = bridge_root / 'lean-attempt-002'
pins = {
    bridge_root / 'SourcePolicyPathBridge.lean':
        '108500fc13229b8faffc9829d886313167142075112bc3f6c023a086c074ae91',
    bridge_cache / 'SourcePolicyPathBridge.olean':
        '0ef1132fbfb24b0e571693de99e2729f9a8ede4aa41203fb4b3be67d46915748',
    base / 'tmp/interface-next-review/infinite-source-bridge-v1/REVIEW.json':
        '364b5c2c5698b575a10142a77b5277b2d176e72131e88844f09e43150e11fb3d',
}
for path, expected in pins.items():
    assert sha(path) == expected, f'Frozen dependency or review changed: {path}'

cwd = base / 'ueot-integration/formalization/ueot-core'
repo = base / 'ueot-integration'
manifest = base / 'tmp/registered-interfaces-20261021/linux-build-attempt-9/SOURCE_MANIFEST.json'
build = json.loads(manifest.read_text())['build_identity']
expected_sources = {p['path']: p['sha256'] for p in build['source_files']}
actual_sources = {str(p.relative_to(repo)): sha(p)
                  for p in [cwd / 'UEOT.lean', *sorted((cwd / 'UEOT').rglob('*.lean'))]}
assert actual_sources == expected_sources, 'Production complete-source input changed'
for item in build['environment_files']:
    assert sha(repo / item['path']) == item['sha256'], item
for item in build['runtime_tools'].values():
    assert sha(Path(item['executable'])) == item['sha256'], item
for key, expected in build['import_environment'].items():
    assert os.environ.get(key, '') == expected, (key, os.environ.get(key))
for item in json.loads((root / 'API_INPUTS.json').read_text())['records']:
    assert sha(Path(item['path'])) == item['sha256'], item

attempt = root / f'lean-attempt-{number:03d}'
attempt.mkdir(exist_ok=False)
snapshot = attempt / source.name
snapshot.write_bytes(source.read_bytes())
runtime = base / 'tmp/registered-interfaces-20261021/linux-runtime/lean-4.33.1-linux/bin'
after_lake = (
    'import os,sys,json,hashlib; from pathlib import Path; '
    'os.environ["LEAN_PATH"]=sys.argv[1]+os.pathsep+os.environ.get("LEAN_PATH",""); '
    'Path(sys.argv[2]).write_text(json.dumps({k:os.environ.get(k,"") for k in '
    '["LEAN_PATH","LEAN_SRC_PATH","LEAN_SYSROOT","ELAN_TOOLCHAIN","LEAN_NUM_THREADS"]},indent=2)+"\\n"); '
    'os.execv(sys.argv[3],sys.argv[3:])'
)
cmd = [str(runtime / 'lake'), 'env', sys.executable, '-c', after_lake,
       str(bridge_cache), str(attempt / 'ENV_AFTER_LAKE.json'), str(runtime / 'lean'),
       '--root=' + str(root), '-o', str(attempt / 'SameSourceInfinitePrefix.olean'), str(source)]
env = os.environ.copy()
env['LEAN_NUM_THREADS'] = '1'
env['PATH'] = str(runtime) + os.pathsep + env.get('PATH', '')
receipt = {
    'schema': 'UEOT_PRIVATE_INFINITE_PREFIX_COMPILE_ATTEMPT_V1',
    'attempt': number, 'status': 'RUNNING',
    'source': pin(source), 'source_snapshot': pin(snapshot),
    'command': cmd, 'cwd': str(cwd), 'LEAN_NUM_THREADS': '1',
    'timeout_seconds': timeout,
    'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'root_authorization': 'Root-authorized focused G1-G3 compilation after independent static CLEAR; no tail/K1 event bridge expansion, no production, consumer, book, native or Git writes.',
    'no_other_lean_process_at_start': True,
    'dependency_pins': {str(path): expected for path, expected in pins.items()},
    'production_complete_source_sha256': build['source_tree_sha256'],
    'production_complete_source_files_checked': len(actual_sources),
    'production_manifest': pin(manifest),
    'environment_reuse_binding': pin(root / 'ENVIRONMENT_REUSE_BINDING.json'),
    'static_review': pin(base / 'tmp/interface-next-review/infinite-source-bridge-v1/REVIEW.json'),
    'runner': pin(Path(__file__)),
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
                      'source_sha256': receipt['source']['sha256'],
                      'timeout_seconds': timeout}), flush=True)
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

receipt.update(
    status='TIMEOUT' if timed_out else ('PASS' if code == 0 else 'FAIL'),
    exit_code=code, timed_out=timed_out,
    elapsed_seconds=round(time.monotonic() - start, 3),
    finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    stdout_stderr_log=pin(log), source_after=pin(source),
)
olean = attempt / 'SameSourceInfinitePrefix.olean'
if olean.exists():
    receipt['olean'] = pin(olean)
env_actual = attempt / 'ENV_AFTER_LAKE.json'
if env_actual.exists():
    receipt['actual_lake_environment'] = pin(env_actual)
status.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({key: receipt[key] for key in
                  ['status', 'exit_code', 'timed_out', 'elapsed_seconds']}), flush=True)
print(log.read_text(errors='replace'), flush=True)
raise SystemExit(124 if timed_out else (code if code >= 0 else 1))
