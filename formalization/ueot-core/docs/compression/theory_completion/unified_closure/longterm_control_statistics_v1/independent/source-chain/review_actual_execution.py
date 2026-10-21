#!/usr/bin/env python3
"""Independent read-only review of transferred actual Lean execution evidence."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import importlib.util
import json
import subprocess
import sys
import types

sys.dont_write_bytecode = True
REPO = Path('/workspace/scratch/534b0448126c/ueot-core-next')
CORE = REPO / 'formalization/ueot-core'
PACKET = CORE / 'docs/compression/theory_completion/unified_closure'
REUSE = CORE / 'docs/compression/theory_completion/knowledge/reuse'
EVIDENCE = PACKET / 'longterm_control_statistics_v1/actual-execution'
OUT = Path('/workspace/scratch/534b0448126c/tmp/source-chain-production-review')
BASE = 'ff71e63256c88ad2bb527fdd3004d55c77894ab7'
SOURCE = '60cd5f8ab161c5b51394463c466947a4c6a6c1742ecdcd9c2bbfc41c0c06bd31'
NAME = 'LONGTERM_CONTROL_STATISTICS'
MARKER = NAME + '_NATIVE_JSON '
checks = []

def check(name, condition):
    if not condition:
        raise AssertionError(name)
    checks.append(name)

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

def git_source(relative):
    return subprocess.check_output(['git', 'show', BASE + ':' + relative], cwd=REPO)

def module_from_bytes(name, path, source):
    module = types.ModuleType(name)
    module.__file__ = str(path)
    sys.modules[name] = module
    exec(compile(source, str(path), 'exec'), module.__dict__)
    return module

def log_native(path):
    lines = [line[len(MARKER):] for line in Path(path).read_text().splitlines()
             if line.startswith(MARKER)]
    check('unique_native_marker:' + Path(path).as_posix(), len(lines) == 1)
    return json.loads(lines[0])

def main():
    transfer = read(EVIDENCE / 'EXACT_TRANSFER_MANIFEST.json')
    entries = transfer['files']
    names = [row['relative_path'] for row in entries]
    check('transfer_unique_45_records', len(names) == len(set(names)) == transfer['file_count'] == 45)
    current = {p.relative_to(EVIDENCE).as_posix() for p in EVIDENCE.rglob('*') if p.is_file()}
    check('transfer_exact_file_set', current == set(names) | {'EXACT_TRANSFER_MANIFEST.json'})
    for row in entries:
        path = (EVIDENCE / row['relative_path']).resolve()
        check('transfer_safe_path:' + row['relative_path'], path.is_relative_to(EVIDENCE.resolve()))
        check('transfer_bytes:' + row['relative_path'], path.stat().st_size == row['bytes'])
        check('transfer_sha:' + row['relative_path'], digest(path) == row['sha256'])
        check('transfer_original_path:' + row['relative_path'], row['original_path'] ==
              transfer['original_root'] + '/' + row['relative_path'])

    full_dir = EVIDENCE / 'full-build-04'
    receipt = read(full_dir / 'FULL_BUILD_RECEIPT.json')
    check('full_receipt_schema', receipt['schema'] == 'LONGTERM_ACTUAL_FULL_BUILD_V1')
    check('full_receipt_PASS', receipt['state'] == 'PASS' and receipt['full_build']['exit_code'] == 0)
    check('full_receipt_base', receipt['baseline_ref'] == BASE)
    check('full_receipt_hash', digest(full_dir / 'FULL_BUILD_RECEIPT.json') ==
          '61af3bc7bc9e840ed1240fed0809ec47cb027cf8ea8d1bd11491f27ca8785d02')
    identity = receipt['identity']
    check('full_source_fingerprint', identity['source_tree_sha256'] == SOURCE and identity['module_count'] == 678)
    core_paths = [CORE / 'UEOT.lean', *(CORE / 'UEOT').rglob('*.lean')]
    modules = {p.relative_to(CORE).with_suffix('').as_posix().replace('/', '.'): p for p in core_paths if p.is_file()}
    record_by_module = {r['module']: r for r in identity['source_files']}
    check('full_source_exact_set', set(modules) == set(record_by_module) and len(identity['source_files']) == 678)
    fingerprint = sha256()
    for module, path in sorted(modules.items()):
        data = path.read_bytes()
        fingerprint.update(module.encode()); fingerprint.update(b'\0')
        fingerprint.update(data); fingerprint.update(b'\0')
        r = record_by_module[module]
        check('full_source_file:' + module, r['path'] == path.relative_to(REPO).as_posix() and
              r['bytes'] == len(data) and r['sha256'] == sha256(data).hexdigest())
    check('independent_current_source_fingerprint', fingerprint.hexdigest() == SOURCE)
    for row in identity['environment_files']:
        check('environment_file:' + row['path'], digest(REPO / row['path']) == row['sha256'])
    manifest = read(CORE / 'lake-manifest.json')
    pins = {p['name']: p['rev'] for p in manifest['packages']}
    deps = identity['dependencies']
    check('nine_dependency_exact_names', len(deps) == 9 and {r['name'] for r in deps} == set(pins))
    for dep in deps:
        check('dependency_receipt:' + dep['name'], dep['manifest_rev'] == dep['actual_head'] == pins[dep['name']]
              and dep['clean'] is True and dep['status_porcelain'] == '')
    tools = identity['runtime_tools']
    check('pinned_toolchain', identity['toolchain'] == (CORE / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.1')
    check('runtime_version_receipts', all('4.33.1' in tools[x]['version'] and len(tools[x]['sha256']) == 64 for x in ('lake', 'lean')))
    check('full_actual_command', receipt['full_build']['command'] == [tools['lake']['executable'], 'build', 'UEOT'])
    check('full_actual_log_name', receipt['full_build']['log_name'] == 'full-build.log')
    check('full_actual_log_hash', digest(full_dir / 'full-build.log') == receipt['full_build']['log_sha256'])
    check('full_actual_log_success_marker', 'Build completed successfully' in (full_dir / 'full-build.log').read_text())
    protocol_dir = PACKET / 'longterm_control_statistics_v1/native_protocol'
    check('full_build_driver_hash', digest(protocol_dir / 'full_build.py') == receipt['driver_sha256'] ==
          '132b1c96d38a4462ef407ee31ed94378c2025996b2a7b603e297fd9d35cf86de')

    nd = EVIDENCE / 'native-02'
    status, pre = read(nd / 'STATUS.json'), read(nd / 'SOURCE_PREFLIGHT.json')
    native = read(nd / (NAME + '_NATIVE_V1.json'))
    raw = read(nd / (NAME + '_REUSE_OVERLAY_V1.json'))
    first = read(nd / 'observed_first_native.json')
    check('native_actual_PASS_state', status['state'] == 'PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION')
    check('native_base_agreement', status['baseline_ref'] == pre['baseline_ref'] == raw['baseline_ref'] == BASE)
    check('native_build_receipt_binding', status['build_receipt_sha256'] == raw['native_execution']['build_receipt_sha256'] == digest(full_dir / 'FULL_BUILD_RECEIPT.json'))
    check('native_actual_two_labels', [r['label'] for r in status['results']] == ['native_export', 'fixed_verifier'])
    for row, file in zip(status['results'], (NAME + '_NATIVE_EXPORT.lean', 'VERIFY_' + NAME + '_OVERLAY_TYPES.lean')):
        label = row['label']; log = nd / (label + '.log')
        check('native_exit_zero:' + label, row['exit_code'] == 0)
        check('native_command:' + label, row['command'] == [tools['lake']['executable'], 'env', tools['lean']['executable'], transfer['original_root'] + '/native-02/' + file])
        check('native_log_hash:' + label, digest(log) == row['log_sha256'])
        check('native_log_full_json:' + label, log_native(log) == native)
    check('first_fixed_json_equality', first == native)
    check('first_fixed_json_bytes_equal', (nd / 'observed_first_native.json').read_bytes() == (nd / (NAME + '_NATIVE_V1.json')).read_bytes())
    check('native_recorded_results_exact', raw['native_execution']['results'] == status['results'])
    check('native_evidence_sha', digest(nd / (NAME + '_NATIVE_V1.json')) == status['summary']['native_sha256'] == raw['native_export_evidence']['sha256'])
    check('native_fixed_verifier_sha', digest(nd / ('VERIFY_' + NAME + '_OVERLAY_TYPES.lean')) == status['summary']['verifier_sha256'] == raw['native_execution']['fixed_certificate_sha256'])
    check('native_raw_overlay_sha', digest(nd / (NAME + '_REUSE_OVERLAY_V1.json')) == status['summary']['overlay_sha256'])
    check('raw_has_no_registration_metadata', 'lexical_pr_preflight' not in raw and 'registration_provenance' not in raw)
    check('final_native_driver_sha', pre['integration_driver_sha256'] == digest(protocol_dir / 'integration_native.py') ==
          'd4708782bbb14360002f119715ba51f96c05e2e632694ba64c56c3d38ce8a924')
    check('current_pre_native_source', pre['source_tree_sha256'] == raw['native_execution']['source_tree_sha256'] == SOURCE)
    check('raw_source_checkpoint', raw['source_checkpoint'] == 'worktree-sha256:' + SOURCE)
    check('current_pre_source_count', pre['complete_source_modules'] == 678 and pre['base_snapshot_modules'] == 666 and pre['prior_overlay_count'] == 8)
    for row in pre['immutable_protocol_helpers']:
        source = git_source(row['path'])
        check('immutable_helper:' + row['path'], source == (REPO / row['path']).read_bytes() and sha256(source).hexdigest() == row['sha256'])
    check('identity_helper_receipt_binding', receipt['identity_helper_sha256'] == digest(PACKET / 'registered_interfaces/native_protocol/build_identity.py'))
    reuse_path = REUSE / 'fkrg_reuse.py'; rel = reuse_path.relative_to(REPO).as_posix()
    reuse_bytes = git_source(rel)
    check('base_consumer_hash', sha256(reuse_bytes).hexdigest() == pre['baseline_reuse_consumer']['sha256'])
    sys.path.insert(0, str(REUSE))
    reuse = module_from_bytes('independent_native_review_base_reuse', reuse_path, reuse_bytes)
    previous = reuse.load(verify_source=False)
    check('exact_prior_scope', len(previous['modules']) == 666 and len(previous['graph']) == 4147 and len(previous['overlays']) == 8)
    check('prior_overlay_binding', pre['prior_overlay'] == raw['prior_overlay'] == {
        'path': reuse.OVERLAY_PATHS[-1].relative_to(REPO).as_posix(), 'sha256': reuse.OVERLAY_SHA256S[-1]})
    check('new_modules_pre_raw_equal', pre['added_modules'] == raw['added_modules'] and len(raw['added_modules']) == 12)
    for row in raw['added_modules']:
        check('new_module_source:' + row['module'], digest(REPO / row['path']) == row['content_sha256'])
    for path, expected in raw['source_hash_overrides'].items():
        check('root_hash_override:' + path, digest(REPO / path) == expected)
    check('root_overrides_pre_raw_equal', raw['source_hash_overrides'] == pre['source_hash_overrides'])
    candidates = {r['name']: r for r in pre['public_source_candidates']}
    check('pre_unique_90_public', len(candidates) == len(pre['public_source_candidates']) == 90)
    rows = native['public_source_theorems']; public = {r['name']: r for r in rows}
    check('native_public_exact_names', set(public) == set(candidates) and len(rows) == 90)
    scope = native['all_native_theorem_constants']; owned = {r['name']: r for r in scope}
    check('native_owned_199_unique', len(scope) == len(owned) == 199)
    source_modules = [r['module'] for r in raw['added_modules']]
    check('native_owned_module_scope', native['native_audit_modules'] == source_modules and {r['source_module'] for r in scope} == set(source_modules))
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for row in scope:
        check('owned_axioms:' + row['name'], set(row['axioms']) <= allowed)
        check('owned_fields:' + row['name'], isinstance(row['is_private'], bool) and isinstance(row['type'], str) and bool(row['type']) and isinstance(row['level_parameters'], list))
        check('owned_direct_constants:' + row['name'], len(row['direct_constants']) == len(set(row['direct_constants'])) and set(row['direct_theorem_constants']) <= set(row['direct_constants']))
    all_names = set(previous['graph']) | set(public)
    edges = []
    for name, row in public.items():
        check('public_owner:' + name, row['source_module'] == candidates[name]['module'] == owned[name]['source_module'] and not owned[name]['is_private'])
        check('public_native_field_match:' + name, all(row[k] == owned[name][k] for k in ('type', 'level_parameters', 'direct_constants')))
        deps = sorted((set(row['direct_constants']) & all_names) - {name})
        check('independent_direct_edge_recount:' + name, sorted(row['source_theorem_deps']) == deps and len(row['source_theorem_deps']) == len(deps))
        edges.extend((name, target) for target in deps)
    raw_public = {r['name']: r for r in raw['public_theorems']}
    check('raw_public_exact_names', set(raw_public) == set(public) and len(raw['public_theorems']) == 90)
    for name, row in raw_public.items():
        check('raw_public_matches_observation:' + name, row['source_module'] == public[name]['source_module'] and
              row['source_theorem_deps'] == sorted(public[name]['source_theorem_deps']) and
              all(row[k] == candidates[name][k] for k in ('path', 'line', 'source_origin', 'registration_kind')))
    check('independent_edge_total_149', len(edges) == len(set(edges)) == 149 == status['summary']['registered_edges'])
    cert = raw['proof_dependency_certification']
    check('registered_edge_cert_exact', cert['status'] == 'PASS' and cert['registered_direct_edges'] == 149 and
          [(r['source'], r['target']) for r in cert['edges']] == edges)
    check('type_actual_cross_internal_counts', native['cross_isDefEq_comparisons'] == 90 * 4147 == 373230 and native['internal_isDefEq_comparisons'] == 90 * 89 // 2 == 4005)
    check('type_no_collisions', native['collisions'] == [] and raw['type_distinctness']['definitionally_equal_matches'] == 0)
    check('actual_zero_historical_repair', native['historical_public_repair_count'] == 0 and native['new_source_public_theorem_count'] == native['overlay_public_registration_count'] == 90 and
          all(r['registration_kind'] == 'new_source_public' for r in rows))
    scan = native['historical_repair_incoming_scan']
    check('actual_empty_historical_incoming_scan', scan == {'registered_theorems_scanned': 4147, 'historical_public_repair_targets': [], 'incoming_rows': []})
    check('zero_repair_comparison_partitions', native['new_source_to_registered_isDefEq_comparisons'] == 373230 and
          native['new_source_internal_isDefEq_comparisons'] == 4005 and all(native[k] == 0 for k in (
              'historical_repair_to_registered_isDefEq_comparisons', 'new_source_to_historical_repair_isDefEq_comparisons', 'historical_repair_internal_isDefEq_comparisons')))

    helper_path = PACKET / 'registered_interfaces/native_protocol/prepare_registered_interfaces_export.py'
    helper = module_from_bytes('independent_native_export_template', helper_path, helper_path.read_bytes())
    prior_names = [row['name'] for overlay in previous['overlays'] for row in overlay['public_theorems']]
    generated = helper.render_export(prior_names, pre['public_source_candidates'], pre['added_modules'], [])
    generated = generated.replace('REGISTERED_INTERFACES', NAME).replace('registered.length == 4094', 'registered.length == 4147').replace(
        'newNames.size == 53 && historicalRepairNames.size == 1 && sourceModules.size == 8',
        'newNames.size == 90 && historicalRepairNames.size == 0 && sourceModules.size == 12')
    check('exporter_exact_immutable_template_regeneration', generated.encode() == (nd / (NAME + '_NATIVE_EXPORT.lean')).read_bytes())
    check('exporter_preflight_hash', digest(nd / (NAME + '_NATIVE_EXPORT.lean')) == pre['exporter_sha256'])
    entries = ['    (`' + row['name'] + ', [' + ', '.join('`' + dep for dep in sorted(row['source_theorem_deps'])) + ']),' for row in rows]
    anchor = '  let mut nativeScope : Array Json := #[]'
    fixed = generated.replace(anchor, '  let expectedEdges : Array (Name × List Name) := #[\n' + '\n'.join(entries) + '\n  ]\n' + anchor)
    anchor = '    let deps := constants.filter fun dep => dep != name && allRegistered.contains dep'
    fixed = fixed.replace(anchor, anchor + '\n' +
        '    let some (_, expected) := expectedEdges.find? (fun pair => pair.1 == name)\n' +
        '      | throwError "LONGTERM_EXPECTED_EDGES_MISSING"\n' +
        '    unless deps.length == expected.length && expected.all (fun dep => deps.contains dep) do\n' +
        '      throwError s!"LONGTERM_FIXED_PROOF_DEPENDENCIES_MISMATCH {name}"')
    fixed = fixed.replace('  let mut cross := 0', '  unless nativeScope.size == 199 do\n' +
        '    throwError "LONGTERM_NATIVE_CENSUS_DRIFT"\n  let mut cross := 0')
    check('fixed_certificate_exact_observed_edge_regeneration', fixed.encode() == (nd / ('VERIFY_' + NAME + '_OVERLAY_TYPES.lean')).read_bytes())
    hints = read(OUT / 'REGISTRATION_LEXICAL_RECOMPUTATION.json')
    check('independent_all_90_lexical_hints_match', hints['all_hints'] == pre['lexical_reuse_hints'] == read(nd / 'development_lexical_reuse_hints.json'))
    check('independent_H_27', sum(bool(r['reuse_candidates']) for r in pre['lexical_reuse_hints']) == hints['H'] == 27)

    old_status = read(EVIDENCE / 'native-01/STATUS.json')
    old_pre = read(EVIDENCE / 'native-01/SOURCE_PREFLIGHT.json')
    old_native = log_native(EVIDENCE / 'native-01/native_export.log')
    check('native01_failure_preserved', old_status['state'] == 'FAILED' and old_status['results'][0]['exit_code'] != 0)
    check('native01_driver_snapshot_bound', digest(EVIDENCE / 'native-01/ACTUAL_DRIVER_SNAPSHOT.py') == old_pre['integration_driver_sha256'])
    expected_collision = {'UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceConditionedTerminalCheck.actual_survival_mass_at_zero',
                          'UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.actual_survival_zero'}
    check('native01_exact_real_collision_retained', len(old_native['collisions']) == 1 and set(old_native['collisions'][0]) == expected_collision)
    check('native01_completed_91_candidate_counts', old_native['new_source_public_theorem_count'] == 91 and old_native['cross_isDefEq_comparisons'] == 377377 and old_native['internal_isDefEq_comparisons'] == 4095 and len(old_native['all_native_theorem_constants']) == 202)
    prior_full = read(EVIDENCE / 'full-build-03/FULL_BUILD_RECEIPT.json')
    check('full03_failure_retained', prior_full['state'] == 'FAILED' and prior_full['full_build']['exit_code'] != 0 and
          digest(EVIDENCE / 'full-build-03/full-build.log') == prior_full['full_build']['log_sha256'])
    by_module = {}
    for module in source_modules:
        owned_rows = [r for r in scope if r['source_module'] == module]
        public_count = sum(r['source_module'] == module for r in rows)
        private_count = sum(r['is_private'] for r in owned_rows)
        by_module[module] = {'all_native_theorems': len(owned_rows), 'public_source_candidates': public_count,
                             'private_theorems': private_count, 'other_nonprivate_theorems': len(owned_rows) - public_count - private_count}
    private_count = sum(r['is_private'] for r in scope)
    check('raw_axiom_census_actual_counts', raw['native_axiom_census']['theorem_constants'] == 199 and
          raw['native_axiom_census']['private_theorem_constants'] == private_count and
          raw['native_axiom_census']['other_native_public_constants'] == 199 - 90 - private_count)
    return {'status': 'ACTUAL_EXECUTION_EVIDENCE_REVIEW_CLEAR', 'base': BASE, 'source_tree_sha256': SOURCE,
            'verified_transfer_files': 45, 'verified_transfer_bytes': sum(r['bytes'] for r in transfer['files']),
            'full_build': receipt['full_build'], 'full_receipt_sha256': digest(full_dir / 'FULL_BUILD_RECEIPT.json'),
            'native_runs': status['results'], 'native_summary': status['summary'],
            'actual_type_comparisons': {'cross': 373230, 'internal': 4005, 'collisions': 0},
            'actual_native_scope': {'total': 199, 'public_source_candidates': 90, 'private': private_count,
                                    'other_nonprivate': 199 - 90 - private_count, 'by_module': by_module,
                                    'axiom_union': sorted({a for r in scope for a in r['axioms']})},
            'actual_registered_direct_edges': 149, 'new_graph_total_nodes': 4237,
            'new_graph_total_edges': sum(len(json.loads(r['source_theorem_deps_json'])) for r in previous['graph'].values()) + 149,
            'lexical_H': 27, 'historical_repair_count': 0, 'failed_native01_collision': old_native['collisions'][0],
            'passed_checks': checks,
            'scope_limit': 'Independent read-only review of actual root-executed logs and transferred artifacts, not a third Lean execution. Registration/PR/canonical main acceptance remain separate.'}

try:
    result = main()
except Exception as error:
    result = {'status': 'ACTUAL_EXECUTION_REVIEW_BLOCKED', 'error': repr(error), 'passed_checks': checks}
    (OUT / 'ACTUAL_EXECUTION_REVIEW.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    raise
else:
    (OUT / 'ACTUAL_EXECUTION_REVIEW.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('passed_checks', 'actual_native_scope')}, ensure_ascii=False, indent=2))
    print(json.dumps(result['actual_native_scope'], ensure_ascii=False, indent=2))
