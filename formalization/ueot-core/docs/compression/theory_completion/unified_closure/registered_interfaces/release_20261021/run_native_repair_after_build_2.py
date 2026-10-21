from pathlib import Path
import hashlib, json, os, subprocess, sys, time

TASK = Path('/workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021')
REPO = Path('/workspace/scratch/9a8d58b21e30/ueot-integration')
BUILD = TASK / 'linux-build-attempt-9'
BIN = TASK / 'linux-runtime/lean-4.33.1-linux/bin'
HELPERS = TASK / 'native-repair-tools'
OUT = TASK / 'native-repair-sequence-2'
OBSERVED = TASK / 'linux-native-repair-observed-2'
FINAL = TASK / 'linux-native-repair-final-2'
MANIFEST_SHA = 'c0c8593ab385220d9b6551aaa1df866b62706b798801634861a25af5fa4f22cf'
REVIEW_SHA = '695d790414507da6601b5a7a97f1de5a3f291205c1fad478a904ee3f32c23efa'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check_protocol():
    manifest_path = HELPERS / 'TOOLS_MANIFEST.json'
    if sha(manifest_path) != MANIFEST_SHA:
        raise RuntimeError('FROZEN_PROTOCOL_MANIFEST_DRIFT')
    review_path = TASK / 'ROOT_NATIVE_REPAIR_PROTOCOL_REVIEW.json'
    if sha(review_path) != REVIEW_SHA:
        raise RuntimeError('ROOT_PROTOCOL_REVIEW_DRIFT')
    manifest = json.loads(manifest_path.read_text())
    for row in manifest['files']:
        path = HELPERS / row['path']
        if path.stat().st_size != row['bytes'] or sha(path) != row['sha256']:
            raise RuntimeError('PROTOCOL_FILE_DRIFT: ' + row['path'])

check_protocol()
assert not OBSERVED.exists() and not FINAL.exists()
OUT.mkdir(exist_ok=False)
env = dict(os.environ)
env['PATH'] = str(BIN) + ':' + env.get('PATH', '')
env['LEAN_NUM_THREADS'] = '1'
env['XDG_CACHE_HOME'] = str(TASK / 'linux-cache')
env['PYTHONDONTWRITEBYTECODE'] = '1'
status = {
    'state': 'WAITING_FOR_ACTUAL_FULL_BUILD',
    'pid': os.getpid(),
    'results': [],
    'protocol_manifest_sha256': MANIFEST_SHA,
    'root_protocol_review_sha256': REVIEW_SHA,
    'scope': 'Local native execution and provisional evidence only. No consumer writes, canonical authorization or publication.',
}

def save():
    (OUT / 'STATUS.json').write_text(json.dumps(status, ensure_ascii=False, indent=2) + '\n')

save()
print(json.dumps({'state': status['state'], 'pid': os.getpid(), 'status_path': str(OUT / 'STATUS.json')}), flush=True)
deadline = time.monotonic() + 9000
try:
    while True:
        build = json.loads((BUILD / 'STATUS.json').read_text())
        if build['state'] == 'PASS':
            break
        if build['state'] != 'RUNNING':
            raise RuntimeError('Full build did not pass: ' + build['state'])
        if time.monotonic() > deadline:
            raise TimeoutError('No successful actual build before deadline')
        time.sleep(10)
    check_protocol()
    common = [
        '--repo', str(REPO), '--build-status', str(BUILD / 'STATUS.json'),
        '--build-manifest', str(BUILD / 'SOURCE_MANIFEST.json'),
        '--build-log-dir', str(BUILD), '--focused-label', 'new_modules',
        '--full-label', 'full_ueot', '--base-ref', '86dfbec88c20a9da3c98cd222611aac55cc55f2f',
    ]
    commands = [
        ('native_pipeline', [sys.executable, '-B', str(HELPERS / 'run_native_registered_interfaces_pipeline.py'),
                             *common, '--output', str(OBSERVED), '--lake', str(BIN / 'lake')]),
        ('observed_finalizer', [sys.executable, '-B', str(HELPERS / 'finalize_observed_registered_interfaces_overlay.py'),
                               *common, '--observed', str(OBSERVED), '--output', str(FINAL)]),
    ]
    for label, command in commands:
        check_protocol()
        status.update(state='RUNNING', active=label)
        save()
        start = time.monotonic()
        log = OUT / (label + '.log')
        with log.open('wb') as stream:
            result = subprocess.run(command, cwd=REPO, env=env, stdout=stream, stderr=subprocess.STDOUT)
        status['results'].append({
            'label': label, 'command': command, 'exit_code': result.returncode,
            'elapsed_seconds': time.monotonic() - start, 'log_sha256': sha(log),
        })
        save()
        if result.returncode:
            raise RuntimeError(label + ' failed')
    check_protocol()
    status.update(state='PASS_NATIVE_AND_PROVISIONAL_EVIDENCE')
    status.pop('active', None)
except Exception as error:
    status.update(state='FAIL', error=repr(error))
save()
print(json.dumps(status, ensure_ascii=False), flush=True)
sys.exit(0 if status['state'] == 'PASS_NATIVE_AND_PROVISIONAL_EVIDENCE' else 1)
