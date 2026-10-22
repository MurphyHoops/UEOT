#!/usr/bin/env python3
"""Read-only verification of the imported actual canonical execution; no Lean rerun."""
import base64
import datetime
import hashlib
import importlib.util
import json
import lzma
from pathlib import Path, PurePosixPath
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path('/workspace/scratch/534b0448126c/ueot-core-next')
TMP = Path('/workspace/scratch/534b0448126c/tmp/core-path-realization-20261022')
PREFIX = Path('formalization/ueot-core/docs/compression/theory_completion')
PACKET = ROOT / PREFIX / 'unified_closure/path_realization_v1'
ACTUAL = PACKET / 'actual-execution'
IMPORTED = TMP / 'mac-canonical-import-01'
BASE = 'd503586107974c56e0773b4ea106b41a7d144b43'
SOURCE = 'de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379'
watched = {}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def read(path):
    path = Path(path)
    data = path.read_bytes()
    value = digest(data)
    if path in watched:
        assert watched[path] == value, ('INPUT_CHANGED_DURING_REVIEW', str(path))
    watched[path] = value
    return data

def js(path):
    return json.loads(read(path))

def git_object(path):
    result = subprocess.run(['git', 'show', BASE + ':' + str(path)], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    assert result.returncode == 0, (str(path), result.stderr.decode())
    return result.stdout

def record(path):
    path = Path(path)
    data = read(path)
    return {'path': str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path),
            'bytes': len(data), 'sha256': digest(data)}

transfer = TMP / 'transfer-canonical-01'
manifest = js(transfer / 'MANIFEST.json')
encoded = read(transfer / 'payload.b64')
assert manifest['state'] == 'EXPORTED_EXACT_BYTES'
assert len(encoded) == manifest['encoded_bytes']
assert digest(encoded) == manifest['encoded_sha256']
compressed = base64.b64decode(encoded.strip(), validate=True)
assert len(compressed) == manifest['compressed_bytes']
assert digest(compressed) == manifest['compressed_sha256']
payload_raw = lzma.decompress(compressed)
assert len(payload_raw) == manifest['payload_bytes']
assert digest(payload_raw) == manifest['payload_sha256']
payload = json.loads(payload_raw)
assert payload['schema'] == 'PATH_REALIZATION_CANONICAL_EXACT_BYTE_EXPORT_V1'
rows = payload['files']
assert len(rows) == len({r['path'] for r in rows}) == manifest['files'] == 17
assert [{k: v for k, v in row.items() if k != 'data_b64'} for row in rows] == manifest['inventory']
receipt = js(TMP / 'MAC_CANONICAL_IMPORT_RECEIPT_01.json')
assert receipt['state'] == 'PASS_EXACT_RAW_BYTES_IMPORTED_AND_ARCHIVED'
assert receipt['files'] == 17 and receipt['raw_file_bytes'] == 3557798
assert receipt['payload_sha256'] == manifest['payload_sha256']
assert receipt['encoded_sha256'] == manifest['encoded_sha256']
assert receipt['source_root'] == payload['source_root']
assert read(ACTUAL / 'canonical-import-01/IMPORT_RECEIPT.json') == read(TMP / 'MAC_CANONICAL_IMPORT_RECEIPT_01.json')
import_records = []
for row in rows:
    relative = PurePosixPath(row['path'])
    assert not relative.is_absolute() and '..' not in relative.parts
    data = base64.b64decode(row['data_b64'], validate=True)
    assert len(data) == row['bytes'] and digest(data) == row['sha256']
    assert read(IMPORTED / str(relative)) == data
    assert read(ACTUAL / str(relative)) == data
    import_records.append({**{k: v for k, v in row.items() if k != 'data_b64'},
                           'archived_path': str((ACTUAL / str(relative)).relative_to(ROOT))})
assert import_records == receipt['records']
assert sum(r['bytes'] for r in rows) == manifest['raw_file_bytes'] == 3557798

sync = js(ACTUAL / 'canonical-sync-01/RECEIPT.json')
sync_payload = js(ACTUAL / 'canonical-sync-01/PAYLOAD.json')
assert sync['state'] == 'PASS_EXACT_INPUTS_SOURCE_RUNTIME_DEPENDENCIES_UNCHANGED'
assert sync['base_ref'] == sync_payload['base_ref'] == BASE
assert sync['source_tree_sha256'] == sync_payload['source_tree_sha256'] == SOURCE
assert sync['payload_sha256'] == digest(read(ACTUAL / 'canonical-sync-01/PAYLOAD.json'))
assert sync['driver_sha256'] == digest(read(ACTUAL / 'canonical-sync-01/driver.py'))
assert read(ACTUAL / 'canonical-sync-01/driver.py') == read(ACTUAL / 'sync_canonical_inputs.py')
assert len(sync['files']) == len(sync_payload['files']) == 10
assert sync['files'] == [{k: v for k, v in r.items() if k != 'data_b64'} for r in sync_payload['files']]
expected = {str(PREFIX / p) for p in (
    'unified_closure/UMC_GLOBAL_MODULE_DAG_V4.json',
    'knowledge/README.md', 'knowledge/reuse/fkrg_reuse.py',
    'knowledge/reuse/test_fkrg_reuse.py', 'knowledge/reuse/README.md',
    'knowledge/reuse/REBUILD_CLONE_CANDIDATES.py',
    'knowledge/reuse/PATH_REALIZATION_NATIVE_V1.json',
    'knowledge/reuse/PATH_REALIZATION_REUSE_OVERLAY_V1.json',
    'knowledge/reuse/VERIFY_PATH_REALIZATION_OVERLAY_TYPES.lean',
    'unified_closure/path_realization_v1/publication/run_canonical_umc.py')}
assert {r['path'] for r in sync['files']} == expected
before_count = 0
for row in sync_payload['files']:
    content = base64.b64decode(row['data_b64'], validate=True)
    assert len(content) == row['bytes'] and digest(content) == row['sha256']
    assert read(ROOT / row['path']) == content
    old = row['before_sha256']
    if old is not None:
        before_count += 1
        assert digest(git_object(row['path'])) == old
        assert read(ACTUAL / 'canonical-sync-01/before' / row['path']) == git_object(row['path'])
    else:
        found = subprocess.run(['git', 'cat-file', '-e', BASE + ':' + row['path']],
                               cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        assert found.returncode != 0
assert before_count == 6

execution = js(ACTUAL / 'umc-full-01/EXECUTION.json')
audit = js(ACTUAL / 'umc-full-01/UMC_FULL_AUDIT.json')
log = read(ACTUAL / 'umc-full-01/canonical-audit.log')
driver = read(ACTUAL / 'umc-full-01/driver.py')
assert execution['state'] == 'PASS' and execution['exit_code'] == 0
assert execution['command'] == [
    '/opt/homebrew/opt/python@3.14/bin/python3.14', '-B',
    str(PREFIX / 'unified_closure/audit_umc_local.py'), '--full', '--output',
    payload['source_root'] + '/umc-full-01/UMC_FULL_AUDIT.json']
assert execution['source_tree_sha256'] == SOURCE
assert execution['source_runtime_dependencies_before'] == execution['source_runtime_dependencies_after'] == 'EXACT_ACCEPTED_FULL_BUILD_IDENTITY'
assert execution['log_sha256'] == digest(log)
assert execution['driver_sha256'] == digest(driver) == 'f6dda475d5518ebf1e325fde43050e147e16f7b3c73d07bf948255c682796725'
assert execution['audit_sha256'] == digest(read(ACTUAL / 'umc-full-01/UMC_FULL_AUDIT.json'))
assert driver == read(PACKET / 'publication/run_canonical_umc.py')
old_wrapper = read(ROOT / PREFIX / 'unified_closure/finite_memory_v1/publication/run_canonical_umc.py')
assert driver == old_wrapper.replace(b'audit["global_bundled_Lean_modules"] == 684', b'audit["global_bundled_Lean_modules"] == 691')
auditor_path = PREFIX / 'unified_closure/audit_umc_local.py'
auditor = read(ACTUAL / 'umc-full-01/auditor.py')
assert auditor == read(ROOT / auditor_path) == git_object(auditor_path)
assert digest(auditor) == '7acc030d2607cd2afbcea00a5967a542cee34f7bb3ce897adca2c7761fd87c48'
lines = log.decode().splitlines()
assert len(lines) == 2 and lines[0].startswith('UMC_LOCAL_AUDIT_PASS ')
assert json.loads(lines[0].removeprefix('UMC_LOCAL_AUDIT_PASS ')) == audit
assert lines[1] == 'UMC_VERIFIED_GIT_HEAD ' + BASE
observed = js(ACTUAL / 'tool-observations/CANONICAL_01_TOOL_OUTPUT.json')
assert observed['isError'] is False
observed_text = '\n'.join(x['text'] for x in observed['content'] if x['type'] == 'text')
observed_json, _ = json.JSONDecoder().raw_decode(observed_text[observed_text.index('{'):])
assert observed_json == execution and 'Process completed with exit code 0' in observed_text
assert read(ACTUAL / 'tool-observations/CANONICAL_01_TOOL_OUTPUT.json') == read(TMP / 'CANONICAL_01_TOOL_OUTPUT.json')
sync_observed = js(ACTUAL / 'tool-observations/CANONICAL_SYNC_01_TOOL_OUTPUT.json')
sync_text = '\n'.join(x['text'] for x in sync_observed['content'] if x['type'] == 'text')
sync_observed_json, _ = json.JSONDecoder().raw_decode(sync_text[sync_text.index('{'):])
assert sync_observed_json == sync

build_path = ACTUAL / 'full-build-02/FULL_BUILD_RECEIPT.json'
build = js(build_path)
assert execution['full_build_receipt_sha256'] == digest(read(build_path)) == '142c7f832a3d9cd9a012abf38a3bc748ae75f01a94c09f9296da40a5378658d7'
assert build['state'] == 'PASS' and build['full_build']['exit_code'] == 0
assert build['identity']['source_tree_sha256'] == SOURCE
core = ROOT / 'formalization/ueot-core'
all_paths = [core / 'UEOT.lean', *(core / 'UEOT').rglob('*.lean')]
modules = {p.relative_to(core).with_suffix('').as_posix().replace('/', '.'): p for p in all_paths}
source_rows = []
source_digest = hashlib.sha256()
for module, path in sorted(modules.items()):
    raw = read(path)
    source_rows.append({'module': module, 'path': str(path.relative_to(ROOT)), 'bytes': len(raw), 'sha256': digest(raw)})
    source_digest.update(module.encode() + b'\x00' + raw + b'\x00')
assert source_rows == build['identity']['source_files']
assert len(source_rows) == build['identity']['module_count'] == 691
assert source_digest.hexdigest() == SOURCE
dag_path = ROOT / PREFIX / 'unified_closure/UMC_GLOBAL_MODULE_DAG_V4.json'
dag = js(dag_path)
assert dag['source_tree_sha256'] == SOURCE and set(dag['entries']) == set(modules)
assert dag['total_Lean_modules'] == dag['reachable_from_UEOT_root'] == 691
assert not dag['cycles_detected'] and not dag['missing_internal_imports'] and not dag['not_reachable_from_UEOT_root']
assert dag['category_counts']['UMC_New_Bridges'] == 92
proof_dir = core / 'UEOT/V3/Compression/TheoryCompletion/UnifiedClosure'
proofs = sorted(proof_dir.glob('*.lean'))
assert len(proofs) == 92
fkrg_path = ROOT / PREFIX / 'knowledge/fkrg.py'
assert read(fkrg_path) == git_object(fkrg_path.relative_to(ROOT))
sys.path.insert(0, str(fkrg_path.parent))
import fkrg
names = []
for path in proofs:
    module = path.relative_to(core).with_suffix('').as_posix().replace('/', '.')
    declarations, _ = fkrg.extract(module, path)
    names.extend(row[5] for row in declarations if row[3] in ('theorem', 'lemma') and not row[5].startswith('private@'))
assert len(names) == len(set(names)) == 672
public_root = core / 'UEOT/V3/Compression/TheoryCompletion.lean'
root_imports = [line.split()[1] for line in read(public_root).decode().splitlines()
                if line.startswith('import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.')]
assert len(root_imports) == 92 and set(root_imports) == {
    'UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.' + p.stem for p in proofs}
assert audit['canonical_main'] == BASE
assert audit['research_modules'] == audit['public_root_imports'] == 92
assert audit['UMC_theorems_and_lemmas'] == 672 and audit['global_bundled_Lean_modules'] == 691
assert audit['source_PIDs_located'] == 106
assert audit['source_provenance'] == {'DOC_REFERENCED_LOCATION_FOUND': 106}
assert audit['UMC_axioms'] == '1404/1404_LEAN_STANDARD_AXIOMS'
census = audit['UMC_native_census']
assert census['theorem_constants'] == 1404 and census['private_theorem_constants'] == 176
assert census['confirmed_public_source_candidates'] == 672 and census['other_native_public_constants'] == 556
assert census['source_modules'] == 92 and 176 + 672 + 556 == 1404
assert audit['full_Lean'] == 'PASS' and audit['full_import_dag_acyclic_reachable_complete'] is True
assert audit['global_strong_unified_closure'] == 'NOT_ESTABLISHED'
assert audit['scientific_external_evidence'] == 'UNVERIFIED' and audit['frozen_source_impact'] == 'NONE'
assert audit['publication_actions'] == 'NOT_PERFORMED_BY_THIS_READ_ONLY_AUDIT'

evidence_paths = [ACTUAL / row['path'] for row in rows] + [
    ACTUAL / 'canonical-import-01/IMPORT_RECEIPT.json',
    ACTUAL / 'tool-observations/CANONICAL_01_TOOL_OUTPUT.json',
    ACTUAL / 'tool-observations/CANONICAL_SYNC_01_TOOL_OUTPUT.json',
    build_path, dag_path,
    PACKET / 'independent/ACTUAL_EXECUTION_REVIEW.json',
    transfer / 'MANIFEST.json', transfer / 'payload.b64', Path(__file__)]
result = {
    'schema': 'PATH_REALIZATION_CANONICAL_INDEPENDENT_BYTE_REVIEW_V1',
    'state': 'PASS_READ_ONLY_BYTE_IDENTITY_AND_ACTUAL_RECEIPT_REVIEW',
    'reviewer': '/root/finite_window_source',
    'observed_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'baseline_ref': BASE, 'source_tree_sha256': SOURCE,
    'actual_execution': execution, 'actual_audit': audit,
    'actual_import': {k: v for k, v in receipt.items() if k != 'records'},
    'decoded_and_archived_files': 17, 'decoded_raw_file_bytes': 3557798,
    'canonical_sync_files': sync['files'],
    'baseline_before_files_verified': before_count,
    'current_complete_source_records_verified': len(source_rows),
    'current_research_source_modules_verified': len(proofs),
    'current_public_source_candidates_verified': len(names),
    'current_public_root_imports_verified': len(root_imports),
    'dag_sha256': digest(read(dag_path)),
    'auditor_sha256': digest(auditor), 'auditor_equal_immutable_baseline': True,
    'wrapper_only_predecessor_difference': 'expected module assertion 684 -> 691',
    'evidence_files': [record(p) for p in evidence_paths],
    'review_execution_scope': 'Local read-only decoding, hashing, immutable Git-object reads and lexical source rediscovery. No Mac call, Lean, lake, native or canonical audit rerun.',
    'native_census_scope': 'The unchanged canonical auditor actually checked temporary native records and emits their aggregate census. This reviewer did not receive the 1404 per-constant temporary rows. The separate final increment of 249 constants was retained and independently reviewed in ACTUAL_EXECUTION_REVIEW.json.',
    'remaining_scope': 'Immutable candidate Git-object review, actual publication and resulting-main gates remain separate.'
}
for path, expected_hash in watched.items():
    assert digest(path.read_bytes()) == expected_hash, ('INPUT_CHANGED_DURING_REVIEW', str(path))
result['watched_input_files_unchanged'] = len(watched)
print(json.dumps(result, indent=2, ensure_ascii=False))
