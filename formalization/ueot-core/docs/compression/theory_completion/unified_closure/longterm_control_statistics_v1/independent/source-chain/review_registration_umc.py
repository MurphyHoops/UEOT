#!/usr/bin/env python3
"""Independent read-only registration delta and actual UMC receipt review.

This script does not execute Lean, edit the repository, or replace the earlier
full/native evidence review. Its only writes are two new scratch receipts.
"""
from pathlib import Path
from hashlib import sha256
import importlib.util
import json
import subprocess
import sys

sys.dont_write_bytecode = True
REPO = Path('/workspace/scratch/534b0448126c/ueot-core-next')
CORE = REPO / 'formalization/ueot-core'
UC = CORE / 'docs/compression/theory_completion/unified_closure'
PACKET = UC / 'longterm_control_statistics_v1'
EVIDENCE = PACKET / 'actual-execution'
NATIVE = EVIDENCE / 'native-02'
REUSE = CORE / 'docs/compression/theory_completion/knowledge/reuse'
OUT = Path('/workspace/scratch/534b0448126c/tmp/source-chain-production-review')
BASE = 'ff71e63256c88ad2bb527fdd3004d55c77894ab7'
SOURCE = '60cd5f8ab161c5b51394463c466947a4c6a6c1742ecdcd9c2bbfc41c0c06bd31'
NAME = 'LONGTERM_CONTROL_STATISTICS'
OVERLAY = NAME + '_REUSE_OVERLAY_V1.json'
ARTIFACT = NAME + '_NATIVE_V1.json'
VERIFIER = 'VERIFY_' + NAME + '_OVERLAY_TYPES.lean'


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write_receipt(name, value):
    path = OUT / name
    data = (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()
    if path.exists() and path.read_bytes() != data:
        raise RuntimeError('Refuse to overwrite different review receipt: ' + str(path))
    path.write_bytes(data)


def main():
    checks = []

    def check(label, value):
        if not value:
            raise AssertionError(label)
        checks.append(label)

    # Registration may add files under native-02. The immutable original
    # manifest identifies the original 45 records; each must remain byte-exact.
    original = read(EVIDENCE / 'EXACT_TRANSFER_MANIFEST.json')
    check('original_transfer_count', len(original['files']) == 45)
    for row in original['files']:
        path = EVIDENCE / row['relative_path']
        check('original_evidence_preserved:' + row['relative_path'],
              path.stat().st_size == row['bytes'] and digest(path) == row['sha256'])

    raw_path = NATIVE / OVERLAY
    registered_path = REUSE / OVERLAY
    raw, registered = read(raw_path), read(registered_path)
    receipt_path = NATIVE / 'REGISTRATION_RECEIPT.json'
    receipt = read(receipt_path)
    keys = {'lexical_pr_preflight', 'registration_provenance'}
    check('raw_not_augmented', not keys.intersection(raw))
    check('exact_two_key_addition', set(registered) - set(raw) == keys)
    check('no_original_key_removed', set(raw) <= set(registered))
    check('full_stripped_json_equals_original',
          {k: v for k, v in registered.items() if k not in keys} == raw)
    check('registered_archive_identical_bytes', registered_path.read_bytes() ==
          (NATIVE / 'REGISTERED_OVERLAY.json').read_bytes())
    check('raw_overlay_known_sha', digest(raw_path) ==
          'c04d08aac1ed70cc1dd73ee5821a196aaf8ac7d0168e4eabd5de70bd8c1c7edd')
    check('registered_overlay_known_sha', digest(registered_path) ==
          'cb5792eff95b2a1386a7c0832eeeedc5a283f212b462f2c6c6d3342dd5e1bb06')
    check('registration_receipt_known_sha', digest(receipt_path) ==
          'dff9caf5fdbddf977ab0e7e4a0c5f1daaf9299195503125d5e878c106ccf811f')
    check('metadata_receipt_state', receipt['state'] == 'PASS_METADATA_ONLY_CONSUMER_UNCHANGED')
    check('metadata_receipt_bindings', receipt['baseline_ref'] == BASE and
          receipt['source_tree_sha256'] == SOURCE and
          receipt['registered_overlay'] == {'path': registered_path.relative_to(REPO).as_posix(),
                                           'sha256': digest(registered_path)} and
          receipt['raw_overlay_sha256'] == digest(raw_path) and
          set(receipt['added_top_level_keys']) == keys and
          receipt['stripped_registered_json_equals_raw'] is True)
    for name in (ARTIFACT, VERIFIER):
        check('registered_evidence_byte_copy:' + name,
              (REUSE / name).read_bytes() == (NATIVE / name).read_bytes())

    pre = read(NATIVE / 'SOURCE_PREFLIGHT.json')
    lexical = registered['lexical_pr_preflight']
    hinted = sum(bool(row['reuse_candidates']) for row in pre['lexical_reuse_hints'])
    recomputed = read(OUT / 'REGISTRATION_LEXICAL_RECOMPUTATION.json')
    check('lexical_actual_H', hinted == lexical['new_theorems_with_lexical_reuse_candidates'] ==
          receipt['lexical_hinted_count'] == 27)
    check('lexical_scope_counts',
          (lexical['base_lean_module_count'], lexical['candidate_lean_module_count'],
           lexical['base_public_lexical_theorem_count'], lexical['candidate_public_lexical_theorem_count'],
           lexical['new_public_source_theorem_count'], lexical['historical_public_repair_count'],
           lexical['overlay_public_registration_count']) == (666, 678, 4147, 4237, 90, 0, 90))
    check('lexical_worktree_scope_explicit', lexical['candidate_ref'] is None and
          lexical['baseline_ref'] == BASE and lexical['candidate_source_tree_sha256'] == SOURCE and
          'immutable Git-object PR preflight is separately required' in lexical['candidate_scope'])
    provenance = registered['registration_provenance']
    check('provenance_input_receipt_equal', provenance['inputs'] == receipt['input_files'])
    check('metadata_scope_truthful', provenance['metadata_additions_only'] == sorted(keys) and
          provenance['raw_evidence_bytes_preserved'] is True and
          provenance['consumer_registry_modified'] is False and
          provenance['git_object_pr_preflight'] == 'NOT_PERFORMED_SEPARATE_GATE' and
          provenance['independent_review'] == 'SEPARATE_GATE')
    roles = {}
    for entry in receipt['input_files']:
        target = (REPO / entry['path']).resolve()
        check('registered_snapshot_safe_path:' + entry['path'], target.is_relative_to(REPO))
        check('registered_snapshot_sha:' + entry['path'], digest(target) == entry['sha256'])
        roles[entry['role']] = roles.get(entry['role'], 0) + 1
        if entry['role'] == 'immutable_base_consumer':
            rel = 'formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/fkrg_reuse.py'
            source = subprocess.check_output(['git', 'show', BASE + ':' + rel], cwd=REPO)
        else:
            source = Path(entry['input_path']).read_bytes()
        check('registered_snapshot_source_bytes:' + entry['path'], target.read_bytes() == source)
    check('fixed_ten_raw_inputs', roles['actual_native_output'] == 10 and len(receipt['input_files']) == 21)

    driver = PACKET / 'native_protocol/register_overlay.py'
    check('registration_driver_binding', digest(driver) ==
          '3679552fc1599894cd1cf0ce5aba3324c1d13d885fbcdd6c96fc1796dbc1c939')
    command = ['python3', '-B', str(driver), '--repo', str(REPO), '--native-output', str(NATIVE),
               '--archive-relative', NATIVE.relative_to(REPO).as_posix(), '--build-receipt',
               str(EVIDENCE / 'full-build-04/FULL_BUILD_RECEIPT.json'), '--check-only']
    watched = [*NATIVE.rglob('*'), registered_path, REUSE / ARTIFACT, REUSE / VERIFIER]
    before = {str(p): digest(p) for p in watched if p.is_file()}
    result = subprocess.run(command, cwd=REPO, capture_output=True, text=True)
    check('post_registration_check_only_exit_zero', result.returncode == 0)
    summary = json.loads(result.stdout)
    check('post_registration_check_only_exact_summary', summary == {
        'state': 'CHECKED_NO_FILES_WRITTEN', 'registered_overlay': receipt['registered_overlay'],
        'receipt': receipt_path.relative_to(REPO).as_posix(), 'receipt_sha256': digest(receipt_path),
        'lexical_hinted_count': 27, 'planned_output_files': 26})
    after = {str(p): digest(p) for p in [*NATIVE.rglob('*'), registered_path, REUSE / ARTIFACT,
                                      REUSE / VERIFIER] if p.is_file()}
    check('check_only_no_artifact_changes', before == after)
    check('raw_preflight_historical_state_preserved',
          pre['status'] == 'PENDING_ACTUAL_NATIVE_EXECUTION')
    write_receipt('REGISTRATION_STATIC_AND_EXECUTION_REVIEW.json', {
        'status': 'CLEAR_METADATA_REGISTRATION_AND_BYTE_PRESERVATION',
        'review_scope': 'Static script review plus actual registered artifact delta; independent read-only check-only replay. No Lean execution or consumer mutation by this reviewer.',
        'baseline_ref': BASE, 'source_tree_sha256': SOURCE,
        'registration_driver_sha256': digest(driver), 'raw_overlay_sha256': digest(raw_path),
        'registered_overlay_sha256': digest(registered_path), 'receipt_sha256': digest(receipt_path),
        'added_top_level_keys': sorted(keys), 'lexical_hinted_count': hinted,
        'provenance_roles': roles, 'post_registration_check_only': summary,
        'consumer_review': 'Separate independent SISC-agent review; not certified by this receipt.',
        'git_object_preflight': 'Separate required gate, not performed by this metadata review.',
        'checks': checks})

    checks = []
    manifest = read(EVIDENCE / 'UMC_TRANSFER_MANIFEST.json')
    check('umc_transfer_three_files', len(manifest['files']) == 3)
    for row in manifest['files']:
        path = EVIDENCE / row['relative_path']
        check('umc_transfer:' + row['relative_path'],
              path.stat().st_size == row['bytes'] and digest(path) == row['sha256'])
    umc_dir = EVIDENCE / 'umc-full-01'
    status = read(umc_dir / 'STATUS.json')
    audit = read(umc_dir / 'UMC_FULL_AUDIT.json')
    log = (umc_dir / 'audit.log').read_text()
    check('umc_status_exit_zero', status['exit_code'] == 0)
    check('umc_status_source_binding', status['source_tree_sha256'] == SOURCE)
    check('umc_log_sha', status['log_sha256'] == digest(umc_dir / 'audit.log') ==
          '44bf9f93533da1105b575b24de4ae6552dbfdab3bf1465f090459bd1d533308e')
    marker = 'UMC_LOCAL_AUDIT_PASS '
    records = [json.loads(line[len(marker):]) for line in log.splitlines() if line.startswith(marker)]
    check('umc_unique_success_record_equals_receipt', records == [audit])
    check('umc_logged_head_is_baseline', [line for line in log.splitlines() if
          line.startswith('UMC_VERIFIED_GIT_HEAD ')] == ['UMC_VERIFIED_GIT_HEAD ' + BASE])
    relative = 'formalization/ueot-core/docs/compression/theory_completion/unified_closure/audit_umc_local.py'
    driver = REPO / relative
    check('umc_validator_unchanged_from_base', driver.read_bytes() ==
          subprocess.check_output(['git', 'show', BASE + ':' + relative], cwd=REPO))
    check('umc_actual_command', status['command'][:5] == ['python3', '-B', relative, '--full', '--output']
          and len(status['command']) == 6 and status['command'][-1] ==
          next(row['original_path'] for row in manifest['files'] if row['relative_path'].endswith('/UMC_FULL_AUDIT.json')))
    spec = importlib.util.spec_from_file_location('independent_umc_receipt_review', driver)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    graph = module.validate_global_source_dag()
    proofs = sorted((CORE / 'UEOT/V3/Compression/TheoryCompletion/UnifiedClosure').glob('*.lean'))
    public = module.discover_umc_theorem_candidates(proofs)
    check('umc_current_79_modules_564_lexical', len(proofs) == 79 and len(public) == len(set(public)) == 564)
    check('umc_current_graph_678_source', graph['source_tree_sha256'] == SOURCE and
          graph['total_Lean_modules'] == graph['reachable_from_UEOT_root'] == 678)
    check('umc_receipt_scope_counts',
          (audit['research_modules'], audit['UMC_theorems_and_lemmas'], audit['source_PIDs_located'],
           audit['public_root_imports'], audit['global_bundled_Lean_modules']) == (79, 564, 106, 79, 678))
    census = audit['UMC_native_census']
    check('umc_native_census_partition',
          (census['theorem_constants'], census['private_theorem_constants'],
           census['confirmed_public_source_candidates'], census['other_native_public_constants'],
           census['source_modules']) == (1073, 103, 564, 406, 79))
    check('umc_native_census_arithmetic', 103 + 564 + 406 == 1073)
    check('umc_native_axioms_fullbuild_report', audit['UMC_axioms'] == '1073/1073_LEAN_STANDARD_AXIOMS' and
          audit['full_Lean'] == 'PASS')
    check('umc_claim_boundaries_retained', audit['canonical_main'] == BASE and
          audit['global_strong_unified_closure'] == 'NOT_ESTABLISHED' and
          audit['scientific_external_evidence'] == 'UNVERIFIED' and
          audit['frozen_source_impact'] == 'NONE' and
          audit['source_provenance'] == {'DOC_REFERENCED_LOCATION_FOUND': 106} and
          audit['publication_actions'] == 'NOT_PERFORMED_BY_THIS_READ_ONLY_AUDIT')
    write_receipt('UMC_ACTUAL_EXECUTION_REVIEW.json', {
        'status': 'CLEAR_ACTUAL_UNCHANGED_UMC_VALIDATOR_RECEIPT',
        'review_scope': 'Original transferred raw outer log and aggregate receipt checked against unchanged validator source, actual command/status, and current source inventory. No new Lean execution by this reviewer.',
        'baseline_ref': BASE, 'source_tree_sha256': SOURCE,
        'validator_sha256': digest(driver), 'actual_seconds': status['seconds'],
        'status_sha256': digest(umc_dir / 'STATUS.json'), 'log_sha256': digest(umc_dir / 'audit.log'),
        'receipt_sha256': digest(umc_dir / 'UMC_FULL_AUDIT.json'),
        'UMC_scope': census,
        'new_increment_scope_is_separate': {'modules': 12, 'public_source': 90, 'all_owned_theorem_constants': 199},
        'scope_limit': 'The unchanged UMC validator validates all 1073 compiler-owned theorem constants internally and emits the aggregate census. This archived UMC log does not contain its internal per-theorem JSON. The separate native-02 evidence does retain complete per-constant records for all 199 constants in the 12 added modules; these records were independently reviewed in ACTUAL_EXECUTION_REVIEW.json.',
        'global_strong_unified_closure': 'NOT_ESTABLISHED', 'checks': checks})
    print('REGISTRATION_AND_UMC_ACTUAL_REVIEW_CLEAR')


if __name__ == '__main__':
    main()
