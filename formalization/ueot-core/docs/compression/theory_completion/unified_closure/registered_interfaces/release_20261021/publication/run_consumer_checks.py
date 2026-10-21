from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path('/workspace/scratch/9a8d58b21e30')
REPO = ROOT / 'ueot-integration'
OUT = Path(__file__).resolve().parent / 'consumer-checks-1'
OUT.mkdir(exist_ok=False)
PREFIX = 'formalization/ueot-core/docs/compression/theory_completion/'
BASE = '86dfbec88c20a9da3c98cd222611aac55cc55f2f'
assert subprocess.check_output(['git', 'rev-parse', 'origin/main'], cwd=REPO, text=True).strip() == BASE
env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
status = {'state': 'RUNNING', 'actual_origin_main': BASE, 'pid': os.getpid(), 'results': []}

def save():
    (OUT / 'STATUS.json').write_text(json.dumps(status, ensure_ascii=False, indent=2) + '\n')

save()
print(json.dumps({'state': status['state'], 'status_path': str(OUT / 'STATUS.json')}), flush=True)
commands = [
    ('generate_current_dag', [sys.executable, '-B', PREFIX + 'unified_closure/build_umc_global_map.py']),
    ('complete_reuse_suite', [sys.executable, '-B', PREFIX + 'knowledge/reuse/test_fkrg_reuse.py']),
    ('complete_fkrg_suite', [sys.executable, '-B', PREFIX + 'knowledge/test_fkrg.py']),
    ('live_reuse_status', [sys.executable, '-B', PREFIX + 'knowledge/reuse/fkrg_reuse.py', '--json', 'status']),
]
for label, command in commands:
    status['active'] = label
    save()
    log = OUT / (label + '.log')
    start = time.monotonic()
    with log.open('wb') as stream:
        result = subprocess.run(command, cwd=REPO, env=env, stdout=stream, stderr=subprocess.STDOUT)
    row = {'label': label, 'command': command, 'exit_code': result.returncode,
           'elapsed_seconds': time.monotonic() - start,
           'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()}
    status['results'].append(row)
    save()
    print(json.dumps(row), flush=True)
status['state'] = 'PASS' if all(x['exit_code'] == 0 for x in status['results']) else 'FAIL'
status.pop('active', None)
save()
print(json.dumps(status), flush=True)
sys.exit(0 if status['state'] == 'PASS' else 1)
