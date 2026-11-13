#!/usr/bin/env python3
"""Continue only the D3 query after v2's 15 successful source compilations.

Remove one unsupported display option; preserve every prior artifact and log.
This is a fixed incident continuation, not a replacement production build.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone

if sys.flags.optimize:
    raise RuntimeError('Python optimization disables audit assertions; use normal mode')

ROOT = Path('/Users/murphyhoops/Documents/ueot-core-audit-20261113')
PREVIOUS = ROOT / 'run-20261113T0932Z'
OUTPUT = ROOT / 'probe-continuation-20261113T0940Z'
BUNDLE = ROOT / 'bundle-v2'
REPO = ROOT / 'repository'
PROJECT = REPO / 'formalization/ueot-core'
HEAD = '6dd6a3bc13e26f41eddc10ee4d2f39fa1c8ab3d4'
RUNNER_HASH = '31b1671dba48e01386c1afb95f2aaa038c6e9ae96e6339e970f31da31a9412d1'
PROBE_HASH = '28c731287dc45ad7f7f6cbbdd67e011ef493614989da1462bf7f3135ed9bcb8c'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def now():
    return datetime.now(timezone.utc).isoformat()

assert sha(BUNDLE / 'run_d3_reproduction_v2.py') == RUNNER_HASH
spec = importlib.util.spec_from_file_location('fixed_runner_v2', BUNDLE / 'run_d3_reproduction_v2.py')
helper = importlib.util.module_from_spec(spec)
sys.dont_write_bytecode = True
spec.loader.exec_module(helper)
previous_path = PREVIOUS / 'D3_RECEIPT.json'
previous = json.loads(previous_path.read_text())
for bound_name in ('D3_PLAN.json', 'EXPECTED_SOURCE_BLOBS.json'):
    if sha(BUNDLE / bound_name) != previous['bundle_sha256'][bound_name]:
        raise RuntimeError('Original run bundle changed: ' + bound_name)
plan = json.loads((BUNDLE / 'D3_PLAN.json').read_text())
expected = json.loads((BUNDLE / 'EXPECTED_SOURCE_BLOBS.json').read_text())
assert previous['status'] == 'FAILED_OR_BLOCKED'
assert previous['git_head'] == HEAD
assert previous['steps'][-1]['label'] == 'D3Probe' and previous['steps'][-1]['exit_code'] == 1
assert previous['fresh_successful_source_count'] == 15
assert previous['old_target_cache_after']['status'] == 'UNCHANGED'
source_rows = [s for s in previous['steps'] if 'module' in s]
assert [s['module'] for s in source_rows] == [s['module'] for s in plan['fresh_modules']]
assert all(s['exit_code'] == 0 for s in source_rows)
assert helper.capture(['git', 'rev-parse', 'HEAD'], REPO) == HEAD

def validate_sources_and_artifacts():
    assert all(helper.blob(PROJECT / p) == h for p, h in expected['files'].items())
    for row in source_rows:
        assert sha(row['source']) == row['source_sha256']
        for artifact in row['new_artifacts']:
            p = Path(artifact['path'])
            assert not p.is_symlink() and p.is_file()
            assert p.resolve() == p.absolute()
            assert sha(p) == artifact['sha256']

validate_sources_and_artifacts()
for dep in previous['dependency_sources']:
    assert helper.capture(['git', 'rev-parse', 'HEAD'], dep['path']) == dep['expected_rev']
    assert not helper.capture(['git', 'status', '--porcelain', '--untracked-files=no'], dep['path'])
lean = previous['compiler']['command']
assert sha(lean) == previous['compiler']['sha256']
assert helper.capture([lean, '--version'], PROJECT) == previous['compiler']['version']
overlay = PREVIOUS / 'overlay'
cache_root = previous['cache_mirror']['source_cache_root']
stems = set(previous['cache_mirror']['protected_stems'])
cache_before = helper.snapshot_cached_targets(cache_root, stems)
original_cache = json.loads((PREVIOUS / 'OLD_TARGET_CACHE_BEFORE.json').read_text())
assert helper.compare_cached_targets(original_cache, cache_before)['status'] == 'UNCHANGED'
original_probe = (BUNDLE / 'D3Probe.lean').read_bytes()
assert hashlib.sha256(original_probe).hexdigest() == plan['probe_sha256']
assert original_probe.count(b'set_option pp.width 180\n') == 1
corrected_probe = original_probe.replace(b'set_option pp.width 180\n', b'')
assert hashlib.sha256(corrected_probe).hexdigest() == PROBE_HASH
OUTPUT.mkdir(exist_ok=False)
(OUTPUT / 'D3ProbeFinal.lean').write_bytes(corrected_probe)
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join(previous['lean_path'])
record = {
    'schema': 'UEOT-D3-PROBE-CONTINUATION-V1', 'status': 'RUNNING',
    'started_utc': now(), 'git_head': HEAD, 'output': str(OUTPUT),
    'source_compilation_receipt': str(previous_path),
    'source_compilation_receipt_sha256': sha(previous_path),
    'source_compilations_in_this_continuation': 0,
    'reused_fresh_source_compilations_from_previous_run': 15,
    'previous_source_artifacts_verified': sum(len(s['new_artifacts']) for s in source_rows),
    'source_and_config_files_verified': len(expected['files']),
    'python_optimization': sys.flags.optimize,
    'bound_plan_sha256': sha(BUNDLE / 'D3_PLAN.json'),
    'bound_source_manifest_sha256': sha(BUNDLE / 'EXPECTED_SOURCE_BLOBS.json'),
    'probe_sha256': PROBE_HASH, 'runner_sha256': sha(__file__),
    'compiler': previous['compiler'], 'lean_path': previous['lean_path'],
    'correction': 'Delete only unsupported set_option pp.width 180; all imports and query commands unchanged',
    'full_clean_build': False, 'production_source_mutations': False, 'steps': []
}

def checkpoint():
    helper.save(OUTPUT / 'CONTINUATION_RECEIPT.json', record)

def execute(label, argv):
    path = OUTPUT / (label + '.log')
    row = {'label': label, 'argv': argv, 'cwd': str(OUTPUT), 'started_utc': now(), 'log': str(path)}
    with path.open('wb') as log:
        p = subprocess.run(argv, cwd=OUTPUT, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=180)
    row.update(exit_code=p.returncode, finished_utc=now(), log_sha256=sha(path))
    record['steps'].append(row); checkpoint()
    print(json.dumps(row), flush=True)
    assert p.returncode == 0, label + ' returned nonzero; inspect the preserved log'
    return path.read_text()

checkpoint()
try:
    deps_text = execute('D3ProbeFinal-deps', [lean, '--deps', 'D3ProbeFinal.lean'])
    deps = [helper.classify_dependency(s.strip().strip('"'), OUTPUT, overlay)
            for s in deps_text.splitlines() if s.strip().strip('"').endswith('.olean')]
    for item in deps:
        item['sha256'] = sha(item['resolved_path'])
    required = {str((overlay / (m['module'].replace('.', '/') + '.olean')).resolve()) for m in plan['fresh_modules']}
    found = {x['resolved_path'] for x in deps if x['fresh_overlay']}
    assert required <= found
    record['resolved_dependencies'] = deps
    record['all_15_selected_imports_resolved_to_previous_fresh_artifacts'] = True
    checkpoint()
    text = execute('D3ProbeFinal', [lean, '-o', str(OUTPUT / 'D3ProbeFinal.olean'), '-i',
                                  str(OUTPUT / 'D3ProbeFinal.ilean'), 'D3ProbeFinal.lean'])
    assert not re.search(r'declaration uses.*sorry|sorryAx', text)
    parsed = {}
    for match in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", text, re.S):
        parsed[match.group(1)] = [s.strip() for s in (match.group(2) or '').split(',') if s.strip()]
    rows = []
    for endpoint in plan['endpoints']:
        axioms = parsed[endpoint['name']]
        extra = [a for a in axioms if a not in endpoint['allowed_axioms']]
        suffix = endpoint.get('allowed_native_axiom_suffix')
        if suffix:
            assert len(extra) == 1 and (extra[0] == suffix or extra[0].endswith('.' + suffix)), extra
        else:
            assert not extra, extra
        rows.append({'name': endpoint['name'], 'axioms': axioms, 'source': endpoint['source'],
                     'evidence_mode': endpoint['evidence_mode'], 'role': endpoint['role']})
    assert len(rows) == 44
    artifacts = []
    for path in sorted(OUTPUT.glob('D3ProbeFinal.*')):
        if path.suffix in ('.lean', '.log'):
            continue
        assert path.is_file() and not path.is_symlink() and path.resolve() == path.absolute()
        artifacts.append({'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha(path)})
    assert (OUTPUT / 'D3ProbeFinal.olean').is_file()
    validate_sources_and_artifacts()
    cache_after = helper.snapshot_cached_targets(cache_root, stems)
    comparison = helper.compare_cached_targets(cache_before, cache_after)
    assert comparison['status'] == 'UNCHANGED'
    helper.save(OUTPUT / 'OLD_TARGET_CACHE_AFTER.json', cache_after)
    record.update(status='PASS_QUERY_EXECUTION_REVIEW_REQUIRED', finished_utc=now(),
                  endpoint_count=len(rows), axiom_results=rows, new_probe_artifacts=artifacts,
                  old_target_cache=comparison, source_and_previous_artifacts_unchanged_after=True,
                  not_claimed=['new compilation of production sources in this continuation',
                               'full clean build', 'new native evaluation of cached numerical endpoints',
                               'semantic adequacy without review', 'empirical validity', 'global novelty'])
    checkpoint()
    print(json.dumps({'status': record['status'], 'receipt': str(OUTPUT / 'CONTINUATION_RECEIPT.json')}), flush=True)
except Exception as exc:
    record.update(status='FAILED_OR_BLOCKED', finished_utc=now(), failure=str(exc))
    try:
        record['old_target_cache'] = helper.compare_cached_targets(cache_before, helper.snapshot_cached_targets(cache_root, stems))
    except Exception as cache_exc:
        record['old_target_cache'] = {'status': 'CHECK_FAILED', 'failure': str(cache_exc)}
    checkpoint()
    print(json.dumps({'status': record['status'], 'failure': str(exc)}), flush=True)
    raise
