from pathlib import Path
import hashlib, json, os, shutil, subprocess, sys, time, traceback

TASK = Path('/workspace/scratch/9a8d58b21e30/tmp/registered-interfaces-20261021')
REPO = Path('/workspace/scratch/9a8d58b21e30/ueot-integration')
CORE = REPO / 'formalization/ueot-core'
BIN = TASK / 'linux-runtime/lean-4.33.1-linux/bin'
OLD = TASK / 'linux-build-attempt-8'
OUT = TASK / 'linux-build-attempt-9'
BASE = '86dfbec88c20a9da3c98cd222611aac55cc55f2f'
OLD_BASE = '65db00a12d20be41cd6c8befacb9ba2e74a2a8a9'
sys.path.insert(0, str(TASK / 'native-repair-tools'))
import build_identity

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO, text=True).strip()

OUT.mkdir(exist_ok=False)
state = {'state': 'RUNNING', 'pid': os.getpid(), 'results': [],
         'runtime_platform': 'Linux', 'runtime_environment': {'LEAN_NUM_THREADS': '1'},
         'scope': 'Actual incremental full build after interrupted process. Prior focused PASS is reused only after exact complete-source, dependency and runtime identity equality. Not resulting-main validation.'}

def save():
    (OUT / 'STATUS.json').write_text(json.dumps(state, indent=2) + '\n')

save()
try:
    assert git('rev-parse', 'origin/main') == BASE
    assert git('merge-base', '--is-ancestor', BASE, 'HEAD') == ''
    for path in ['formalization/ueot-core/UEOT', 'formalization/ueot-core/lean-toolchain',
                 'formalization/ueot-core/lakefile.lean', 'formalization/ueot-core/lake-manifest.json']:
        assert git('rev-parse', BASE + ':' + path) == git('rev-parse', OLD_BASE + ':' + path)
    original = json.loads((OLD / 'SOURCE_MANIFEST.json').read_text())
    expected = original['build_identity']
    identity = build_identity.capture(REPO, lake=BIN / 'lake', lean=BIN / 'lean',
                                      expected=expected, expected_module_count=666)
    focused = [x for x in json.loads((OLD / 'STATUS.json').read_text())['results']
               if x['label'] == 'new_modules']
    assert len(focused) == 1 and focused[0]['exit_code'] == 0
    assert sha(OLD / 'new_modules.log') == focused[0]['log_sha256']
    for row in original['files']:
        assert sha(REPO / row['path']) == row['sha256']
    shutil.copyfile(OLD / 'new_modules.log', OUT / 'new_modules.log')
    manifest = {'predecessor_head': BASE, 'candidate_head': git('rev-parse', 'HEAD'),
                'files': original['files'], 'build_identity': identity}
    (OUT / 'SOURCE_MANIFEST.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
    state['results'] = focused
    state['reused_focused_build_evidence'] = {
        'original_directory': str(OLD), 'original_status_sha256': sha(OLD / 'STATUS.json'),
        'original_source_manifest_sha256': sha(OLD / 'SOURCE_MANIFEST.json'),
        'original_log_sha256': sha(OLD / 'new_modules.log'),
        'complete_identity_matches_before_resume': True,
        'note': 'The focused result is the original real execution; it was not run again or relabeled as a new execution.'}
    state['source_manifest_sha256'] = sha(OUT / 'SOURCE_MANIFEST.json')
    state['source_tree_sha256'] = identity['source_tree_sha256']
    state['active'] = 'full_ueot'
    save()
    env = dict(os.environ)
    env['PATH'] = str(BIN) + ':' + env.get('PATH', '')
    env['LEAN_NUM_THREADS'] = '1'
    env['XDG_CACHE_HOME'] = str(TASK / 'linux-cache')
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    command = [str(BIN / 'lake'), 'build', 'UEOT']
    start = time.monotonic()
    with (OUT / 'full_ueot.log').open('wb') as stream:
        result = subprocess.run(command, cwd=CORE, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=7200)
    state['results'].append({'label': 'full_ueot', 'exit_code': result.returncode,
                             'elapsed_seconds': time.monotonic() - start,
                             'command': command, 'log_sha256': sha(OUT / 'full_ueot.log')})
    save()
    build_identity.capture(REPO, lake=BIN / 'lake', lean=BIN / 'lean',
                           expected=identity, expected_module_count=666)
    if result.returncode:
        raise RuntimeError('Actual resumed full build failed')
    state.update(state='PASS', complete_identity_matches_after_resume=True)
    state.pop('active', None)
except Exception as error:
    state.update(state='FAIL', error=repr(error), traceback=traceback.format_exc())
save()
print(json.dumps(state), flush=True)
sys.exit(0 if state['state'] == 'PASS' else 1)
