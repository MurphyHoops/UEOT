"""C's read-only evidence calculation. Never imports a runner or calls Lean.

Uses a literal grammar for the five actually observed axiom tokens, independently
of B's general constant/universe parser. Writes only its own C evidence JSON.
"""
from pathlib import Path
import collections
import hashlib
import json
import re
import zipfile

BASE = Path(__file__).resolve().parents[3]
OBS = BASE / 'reproduction-evidence/observed-execution'
B = BASE / 'agents/B/reproduction-20261113'
OUT = Path(__file__).resolve().parent
MAC = '/Users/murphyhoops/Documents/ueot-core-audit-20261113/'
HEAD = '6dd6a3bc13e26f41eddc10ee4d2f39fa1c8ab3d4'
failures = []

def require(value, message):
    if not value:
        failures.append(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(rel):
    return json.loads((OBS / rel).read_text())

def local(mac_path):
    require(mac_path.startswith(MAC), 'Unrecognized Mac path: ' + mac_path)
    return OBS / mac_path.removeprefix(MAC)

plan = json.loads((B / 'D3_PLAN.json').read_text())
expected = json.loads((B / 'EXPECTED_SOURCE_BLOBS.json').read_text())
v1 = read('run-20261113T0920Z/D3_RECEIPT.json')
v2 = read('run-20261113T0932Z/D3_RECEIPT.json')
continuation = read('probe-continuation-20261113T0940Z/CONTINUATION_RECEIPT.json')
post = read('FINAL_SOURCE_ARTIFACT_CHECK.json')
setup = read('SOURCE_SETUP.json')
mirror = read('run-20261113T0932Z/CACHE_MIRROR_MANIFEST.json')
archive = BASE / 'reproduction-evidence/D3_OBSERVED_EXECUTION_EVIDENCE.zip'
require(sha(archive) == '85267f06ecf16ce3394eb5112ca0b3a74ed3c3cb949c4fcc65c8ee4034bb090d', 'Archive SHA mismatch')
with zipfile.ZipFile(archive) as z:
    zip_files = [n for n in z.namelist() if not n.endswith('/')]
    for n in zip_files:
        p = OBS / n
        require(p.is_file() and p.read_bytes() == z.read(n), 'ZIP/local bytes mismatch: ' + n)

log_checks = []
for tag, data in [('v1', v1), ('v2', v2), ('continuation', continuation)]:
    require(data['git_head'] == HEAD, tag + ' HEAD mismatch')
    for step in data['steps']:
        path = local(step['log'])
        actual = sha(path)
        require(actual == step['log_sha256'], 'Raw log SHA mismatch: ' + str(path))
        log_checks.append({'run': tag, 'label': step['label'], 'exit_code': step['exit_code'],
                           'relative_log': str(path.relative_to(OBS)), 'sha256': actual})

require(len(v1['steps']) == 1 and v1['steps'][0]['label'].endswith('-deps'), 'Unexpected v1 execution scope')
require(v1['fresh_lean_execution'] is False, 'v1 incorrectly counted fresh source execution')
source_rows = [s for s in v2['steps'] if 'module' in s]
require([s['module'] for s in source_rows] == [s['module'] for s in plan['fresh_modules']], 'Source target list/order mismatch')
require(len(source_rows) == 15 and all(s['exit_code'] == 0 for s in source_rows), 'Not all 15 target sources exited zero')
require(v2['steps'][-1]['label'] == 'D3Probe' and v2['steps'][-1]['exit_code'] == 1, 'v2 probe failure overwritten')
v2_probe_text = local(v2['steps'][-1]['log']).read_text()
v2_error_lines = [s for s in v2_probe_text.splitlines() if 'error:' in s]
require(len(v2_error_lines) == 1 and 'Unknown option `pp.width`' in v2_error_lines[0], 'v2 contains an unexpected Lean error')
require([s['exit_code'] for s in continuation['steps']] == [0, 0], 'Final Lean commands did not both exit zero')
for f in ['D3_PROCESS_EXIT.json', 'D3_V2_PROCESS_EXIT.json', 'D3_CONTINUATION_PROCESS_EXIT.json']:
    require(read(f)['exit_code'] == 1, 'Original wrapper failure exit overwritten: ' + f)
require(all(d['status'] == 'FAILED_OR_BLOCKED' for d in [v1, v2, continuation]), 'Original wrapper status overwritten')

v2_file = OBS / 'run-20261113T0932Z/D3_RECEIPT.json'
continuation_file = OBS / 'probe-continuation-20261113T0940Z/CONTINUATION_RECEIPT.json'
require(continuation['source_compilation_receipt_sha256'] == sha(v2_file), 'Continuation does not bind actual v2 receipt')
require(post['source_compilation_receipt_sha256'] == sha(v2_file), 'Post-check v2 binding mismatch')
require(post['continuation_receipt_sha256'] == sha(continuation_file), 'Post-check continuation binding mismatch')
for name in ['D3_PLAN.json', 'EXPECTED_SOURCE_BLOBS.json', 'D3Probe.lean', 'run_d3_reproduction_v2.py']:
    require(v2['bundle_sha256'][name] == sha(B / name), 'Executed bundle identity mismatch: ' + name)
require(continuation['bound_plan_sha256'] == sha(B / 'D3_PLAN.json'), 'Continuation plan binding mismatch')
require(continuation['bound_source_manifest_sha256'] == sha(B / 'EXPECTED_SOURCE_BLOBS.json'), 'Continuation source-manifest binding mismatch')
require(continuation['runner_sha256'] == sha(BASE / 'run_d3_probe_continuation.py'), 'Continuation script identity mismatch')
require(continuation['probe_sha256'] == sha(B / 'D3ProbeFinal.lean'), 'Final probe identity mismatch')
require(continuation['python_optimization'] == 0, 'Continuation assertions disabled')
require(continuation['source_compilations_in_this_continuation'] == 0, 'Continuation source count wrong')
require(v2['source_identity']['compared_files'] == len(expected['files']) == 1055, 'Source identity count mismatch')
require(v2['source_identity']['mismatches'] == [], 'Source identity mismatch was present')

setup_sources = {x['path']: x for x in setup['verified_files']}
prefix = plan['project_relative'] + '/'
for rel, value in expected['files'].items():
    require(setup_sources.get(prefix + rel, {}).get('git_blob') == value, 'Bootstrap/source-plan blob mismatch: ' + rel)
for row, target in zip(source_rows, plan['fresh_modules']):
    require(row['source_git_blob'] == target['git_blob'] == expected['files'][target['source']], 'Compiled source blob mismatch: ' + row['module'])
    require(row['source_sha256'] == setup_sources[prefix + target['source']]['sha256'], 'Compiled source SHA mismatch: ' + row['module'])
require(setup['head'] == HEAD and setup['tree'] == '339b3e216d4c036bdd30a87b9653475a88646dde', 'Bootstrap HEAD/tree mismatch')
require(len(v2['dependency_sources']) == 9 and all(x['actual_rev'] == x['expected_rev'] and not x['tracked_status'] for x in v2['dependency_sources']), 'Dependency identity mismatch')
require(v2['compiler'] == continuation['compiler'], 'Compiler changed between source and probe')
require('4.33.1' in v2['compiler']['version'] and plan['lean_commit'] in v2['compiler']['version'], 'Compiler version mismatch')

artifacts = [a for s in source_rows for a in s['new_artifacts']]
require(len(artifacts) == 30 and artifacts == post['source_artifacts'], 'Post-check target artifact bindings differ')
artifact_by_path = {x['path']: x for x in artifacts}
required_paths = {str(Path(v2['output']) / 'overlay' / (x['module'].replace('.', '/') + '.olean')) for x in plan['fresh_modules']}
deps = continuation['resolved_dependencies']
fresh_deps = {x['resolved_path']: x for x in deps if x['fresh_overlay']}
require(required_paths <= set(fresh_deps), 'Final probe did not resolve every selected fresh artifact')
for path in required_paths:
    require(fresh_deps[path]['sha256'] == artifact_by_path[path]['sha256'], 'Resolved fresh artifact SHA mismatch: ' + path)
raw_dep_lines = [s.strip().strip('"') for s in local(continuation['steps'][0]['log']).read_text().splitlines() if s.strip().strip('"').endswith('.olean')]
require(raw_dep_lines == [x['reported_path'] for x in deps], 'Dependency receipt does not reproduce raw --deps output')

before_path = OBS / 'run-20261113T0932Z/OLD_TARGET_CACHE_BEFORE.json'
after_path = OBS / 'run-20261113T0932Z/OLD_TARGET_CACHE_AFTER.json'
before = json.loads(before_path.read_text())
after = json.loads(after_path.read_text())
require(len(before) == len(after) == 63 and before == after, 'Old target cache before/after differs')
require(sha(before_path) == v2['old_target_cache_before']['snapshot_sha256'], 'Old-cache before SHA mismatch')
require(sha(after_path) == v2['old_target_cache_after']['snapshot_sha256'], 'Old-cache after SHA mismatch')
require(post['old_target_cache'] == {'status':'UNCHANGED','before_count':63,'after_count':63,'changes':[]}, 'Post-execution old-cache check failed')
require(mirror['linked_directory_count'] == 0, 'Overlay contains linked directories')
for link in mirror['file_links']:
    rel = link['overlay_path'].removeprefix(mirror['overlay_root'] + '/')
    require(not any(rel == s or rel.startswith(s + '.') for s in mirror['protected_stems']), 'Selected target linked to old cache: ' + rel)
require(sha(OBS / 'run-20261113T0932Z/CACHE_MIRROR_MANIFEST.json') == v2['cache_mirror']['manifest_sha256'], 'Mirror manifest SHA mismatch')
require(post['source_and_config_files_unchanged'] == 1055 and post['source_module_artifacts_unchanged'] == 30, 'Post-source/target recheck incomplete')

log_path = local(continuation['steps'][-1]['log'])
raw = log_path.read_text()
require(sha(log_path) == post['final_probe_log_sha256'], 'Final probe raw log hash mismatch')
require(not re.search(r'error:|sorryAx|declaration uses.*sorry', raw), 'Final log has a proof/query error')
matches = list(re.finditer(r"(?m)^'([^'\r\n]+)' depends on axioms:\s*\[([^\]]*)\]", raw))
require([m.group(1) for m in matches] == [x['name'] for x in plan['endpoints']], 'Axiom endpoint sequence incomplete, duplicate or unexpected')
standard = {'propext':'propext', 'Classical.choice.{u}':'Classical.choice', 'Quot.sound.{u}':'Quot.sound'}
parsed_rows = []
for match, endpoint in zip(matches, plan['endpoints']):
    tokens = dict(standard)
    native = endpoint['name'] + '._native.native_decide.ax_1_1' if endpoint.get('allowed_native_axiom_suffix') else None
    if native:
        tokens[native] = native
    alternatives = '|'.join(re.escape(x) for x in sorted(tokens, key=len, reverse=True))
    one = '(?:' + alternatives + ')'
    body = match.group(2)
    literal_ok = re.fullmatch(r'\s*' + one + r'(?:\s*,\s*' + one + r')*\s*', body) is not None
    require(literal_ok, 'Axiom list includes a token outside exact observed whitelist: ' + endpoint['name'])
    found = re.findall(one, body) if literal_ok else []
    require(len(found) == len(set(found)), 'Duplicate axiom token: ' + endpoint['name'])
    if native:
        require(found.count(native) == 1, 'Disclosed native axiom missing/multiple: ' + endpoint['name'])
    normalized = [tokens[x] for x in found]
    require(all(x in endpoint['allowed_axioms'] or x == native for x in normalized), 'Endpoint-specific standard allowlist mismatch')
    # pp.explicit prints polymorphic query heads with @; accept that exact prefix,
    # and still require the whole constant/universe header followed by a colon.
    type_heads = re.findall(r'(?m)^@?' + re.escape(endpoint['name']) + r'(?:\.\{[^{}]*\})?\s*:', raw)
    require(len(type_heads) == 1, 'Unique exact type query header absent: ' + endpoint['name'])
    parsed_rows.append({'endpoint':endpoint['name'],'raw_list':body,'raw_tokens':found,'constants':normalized,'line':raw[:match.start()].count('\n')+1,'evidence_mode':endpoint['evidence_mode']})
for name in plan['printed_definitions']:
    require(re.search(r'(?m)^(?:structure|def) ' + re.escape(name) + r'(?:\.|\s|$)', raw) is not None, 'Printed definition absent: ' + name)

summary = {
    'status':'PASS_MECHANICAL_BINDINGS_AND_LITERAL_AXIOM_LISTS' if not failures else 'FAIL_REVIEW_REQUIRED',
    'scope':'Read-only cross-binding of observed records; no Lean rerun and no remote artifact-byte rehash by C',
    'failures':failures, 'zip_file_count':len(zip_files), 'raw_logs_rehashed':len(log_checks),
    'source_targets_exit_zero':len(source_rows), 'source_artifact_records_cross_bound':len(artifacts),
    'source_and_config_manifest_count':len(expected['files']),
    'bootstrap_extra_files':sorted(set(setup_sources)-{prefix+p for p in expected['files']}),
    'old_cache_target_records_equal':len(before),
    'probe_type_query_count':len(parsed_rows), 'definition_outputs':len(plan['printed_definitions']),
    'endpoint_modes':dict(collections.Counter(x['evidence_mode'] for x in parsed_rows)),
    'standard_only_endpoint_count':sum(not any('._native.' in a for a in x['constants']) for x in parsed_rows),
    'native_endpoint_count':sum(any('._native.' in a for a in x['constants']) for x in parsed_rows),
    'all_observed_raw_axiom_tokens':sorted({a for x in parsed_rows for a in x['raw_tokens']}),
    'ellipsis_lines':[i for i,s in enumerate(raw.splitlines(),1) if '⋯' in s or '...' in s],
    'v2_error_lines':v2_error_lines,
    'final_probe_log_sha256':sha(log_path), 'raw_log_checks':log_checks, 'axiom_rows':parsed_rows,
    'limits':['Binary .olean/.ilean bytes stay on Mac; C cross-binds their actual lead-computed hashes, not independently rehashing remote binaries',
              'Some pretty-printed types contain ellipsis; successful queries are not a claim of complete printed term expansion',
              'Seven declarations use reused .olean artifacts; native computations are not repeated',
              'The three wrapper failure receipts are intentionally retained']}
(OUT/'C_OBSERVED_EVIDENCE_VERIFICATION.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['raw_log_checks','axiom_rows']},ensure_ascii=False,indent=2))
