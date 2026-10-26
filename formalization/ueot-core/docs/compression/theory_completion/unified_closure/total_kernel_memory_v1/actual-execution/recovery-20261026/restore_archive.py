from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
import importlib.util
import json
import subprocess

repo = Path('/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/total-kernel-memory-20261023')
evidence = repo.parent / 'total-kernel-memory-evidence-20261023'
packet = Path('formalization/ueot-core/docs/compression/theory_completion/unified_closure/total_kernel_memory_v1')
overlay_path = repo / 'formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/TOTAL_KERNEL_MEMORY_REUSE_OVERLAY_V1.json'
overlay_bytes = overlay_path.read_bytes()
assert sha256(overlay_bytes).hexdigest() == 'a2f8966fedd58492b28d2e0235329d5994d27ee74d3deba0c081b22ce54c478f'
overlay = json.loads(overlay_bytes)
mapping = json.loads(Path('/tmp/ueot-r0-recovery-map-20261026.json').read_bytes())
base = overlay['baseline_ref']
spec = importlib.util.spec_from_file_location('r0_protocol', repo / packet / 'native_protocol/protocol_adapter.py')
protocol = importlib.util.module_from_spec(spec)
spec.loader.exec_module(protocol)
_, derived = protocol.adapted_driver('register_overlay', repo, evidence / 'FROZEN_INPUTS_FINAL_01.json', base)
planned = {}
observations = []
assert len(mapping['observations']) == len(overlay['registration_provenance']['inputs'])
for row, original in zip(mapping['observations'], overlay['registration_provenance']['inputs']):
    assert row['target'] == original['path'] and row['sha256'] == original['sha256']
    target = repo / row['target']
    assert target.resolve().is_relative_to((repo / packet / 'actual-execution').resolve())
    if row.get('local_sources'):
        source = row['local_sources'][0]; content = Path(source).read_bytes(); method = 'EXISTING_LOCAL_EVIDENCE'
    elif row.get('repo_source'):
        source = row['repo_source']; content = Path(source).read_bytes(); method = 'MATCHING_REPOSITORY_BYTES'
    elif row.get('git_source'):
        source = row['git_source']; content = subprocess.check_output(['git', 'show', source], cwd=repo); method = 'IMMUTABLE_BASE_GIT_BLOB'
    else:
        source = row['reconstruct_from_adapter']; content = derived[source]; method = 'DETERMINISTIC_ADAPTER_RECONSTRUCTION'
    assert sha256(content).hexdigest() == original['sha256'], target
    assert target not in planned or planned[target] == content
    assert not target.exists() or target.read_bytes() == content
    planned[target] = content
    observations.append({'role': row['role'], 'path': row['target'], 'sha256': row['sha256'], 'recovery_method': method, 'source': source})
assert len(observations) == 39 and len(planned) == 38
for target, content in planned.items():
    target.parent.mkdir(parents=True, exist_ok=True)
    if not target.exists():
        with target.open('xb') as stream: stream.write(content)
    assert sha256(target.read_bytes()).hexdigest() == sha256(content).hexdigest()
archive = repo / packet / 'actual-execution/native-01'
registered_copy = archive / 'REGISTERED_OVERLAY.json'
assert not registered_copy.exists() or registered_copy.read_bytes() == overlay_bytes
if not registered_copy.exists(): registered_copy.write_bytes(overlay_bytes)
raw_row = next(row for row in overlay['registration_provenance']['inputs'] if row['role'] == 'actual_native_output' and row['path'].endswith('/TOTAL_KERNEL_MEMORY_REUSE_OVERLAY_V1.json'))
raw = json.loads((repo / raw_row['path']).read_bytes())
additions = ['lexical_pr_preflight', 'registration_provenance']
assert {k:v for k,v in overlay.items() if k not in additions} == raw
receipt = {
    'schema': 'TOTAL_KERNEL_MEMORY_REGISTRATION_RECEIPT_V1',
    'state': 'PASS_METADATA_ONLY_CONSUMER_UNCHANGED',
    'operation': 'ARCHIVE_RECOVERY_FROM_PINNED_MANIFEST',
    'observed_at': datetime.now(timezone.utc).isoformat(),
    'registration_reexecuted': False,
    'historical_registration_receipt_recovered': False,
    'claim_scope': 'Current pinned-input hash and raw-payload verification. This is a newly issued archive recovery receipt, not a recovered historical registration run or independent review.',
    'baseline_ref': base,
    'source_tree_sha256': overlay['registration_provenance']['source_tree_sha256'],
    'input_files': overlay['registration_provenance']['inputs'],
    'registered_overlay': {'path': overlay_path.relative_to(repo).as_posix(), 'sha256': sha256(overlay_bytes).hexdigest()},
    'raw_overlay_sha256': raw_row['sha256'],
    'added_top_level_keys': additions,
    'stripped_registered_json_equals_raw': True,
    'lexical_hinted_count': overlay['lexical_pr_preflight']['new_theorems_with_lexical_reuse_candidates'],
    'candidate_ref': None,
    'git_object_pr_preflight': 'NOT_PERFORMED_SEPARATE_GATE',
    'recovery_record': (packet / 'actual-execution/recovery-20261026/RECOVERY_RECEIPT.json').as_posix()
}
receipt_path = archive / 'REGISTRATION_RECEIPT.json'
assert not receipt_path.exists(), 'Never overwrite a registration receipt'
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
out = repo / packet / 'actual-execution/recovery-20261026'
out.mkdir(parents=True, exist_ok=False)
(out / 'restore_archive.py').write_bytes(Path(__file__).read_bytes())
recovery = {'schema':'UEOT_TOTAL_KERNEL_MEMORY_ARCHIVE_RECOVERY_V1','state':'PASS','observed_at':receipt['observed_at'],'records':len(observations),'distinct_files':len(planned),'overlay_bytes_unchanged':overlay_path.read_bytes()==overlay_bytes,'registration_reexecuted':False,'historical_registration_receipt_recovered':False,'source_build_or_native_rerun':False,'recovered_inputs':observations,'new_registration_receipt_sha256':sha256(receipt_path.read_bytes()).hexdigest(),'execution_script_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
(out / 'RECOVERY_RECEIPT.json').write_text(json.dumps(recovery, indent=2) + '\n')
assert recovery['overlay_bytes_unchanged']
print(json.dumps({k:v for k,v in recovery.items() if k!='recovered_inputs'}))
