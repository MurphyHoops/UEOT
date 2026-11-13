#!/usr/bin/env python3
"""Bind edition 3.10 to actual reviewed artifacts; preserve old claim objects.

This is a publication metadata generator, not a mathematical verifier. It reads
the immutable 3.9 snapshot, actual new bindings, runtime and publication receipts.
An optional observed integration receipt upgrades remote state, never proof scope.
The independent verify_v3_10_increment.py gate must run after this script.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

BASELINE = 'cb17211653fde30aa50e0e9848798a6a5b3b3f12'
IDS = ['P-OPT-05', 'P-MICRO-06', 'P-MICRO-07', 'C-MICRO-03', 'P-ROB-04', 'P-ROB-05']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--integration', type=Path)
    args = parser.parse_args()
    root = args.repo_root.resolve()
    q = root / 'physics/qm'
    book = q / 'book'
    evidence = q / 'kernel/evidence/v31.13'
    publication = book / 'evidence/v3.10'
    audit = q / 'audits/SIMULTANEOUS_CUTOFF_v31.13'
    now = datetime.now(timezone.utc).isoformat()

    def read(path):
        return json.loads(path.read_text(encoding='utf-8'))

    def write(path, data):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

    def ident(path):
        data = path.read_bytes()
        return {'path': str(path.relative_to(root)), 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}

    def body(text, anchor):
        mark = f'<a id="{anchor}"></a>'
        start = text.index(mark)
        match = re.search(r'(?m)^<a id="(?:ch-\d+|appendix-[a-z])"></a>', text[start + len(mark):])
        end = start + len(mark) + match.start() if match else len(text)
        return text[start:end]

    runtime = read(evidence / 'runtime/execution_receipt.json')
    reuse = read(evidence / 'proof-reuse.json')
    acceptance = read(publication / 'local-acceptance.json')
    assert runtime['status'] == 'PASS' and runtime['inputs_stable_during_execution']
    assert acceptance['status'] == 'PASS_SCOPED' and not acceptance['new_hardware_data']
    assert len(runtime['inputs']) == 17 and len(runtime['commands']) == 9
    for item in runtime['inputs']:
        assert ident(root / item['path']) == {k: item[k] for k in ['path', 'sha256', 'bytes']}
    for item in acceptance['current_artifacts']:
        assert ident(root / item['path']) == {k: item[k] for k in ['path', 'sha256', 'bytes']}
    integration = {'state': 'LOCAL_VERIFIED_REMOTE_PENDING', 'research_entry_baseline': BASELINE,
                   'remote_verified': False}
    if args.integration:
        integration_path = args.integration if args.integration.is_absolute() else root / args.integration
        observed = read(integration_path)
        assert observed['status'] == 'PASS' and observed['scientific_main_verified'] is True
        integration = {'state': 'MAIN_SCIENTIFIC_SOURCE_AND_CI_VERIFIED', 'remote_verified': True,
                       'research_entry_baseline': BASELINE,
                       'scientific_source_head': observed['scientific_source_head'],
                       'verified_scientific_main': observed['verified_scientific_main'],
                       'tree': observed['tree'], 'pr': observed['pr'],
                       'pr_run': observed['pr_run'], 'main_run': observed['main_run'],
                       'integration_receipt': ident(integration_path)}
    state = integration['state']
    proof_identity = {
        'manifest': 'physics/qm/kernel/evidence/v31.11/source-manifest.json',
        'verification': 'physics/qm/kernel/evidence/v31.11/lean-verification.json',
        'source_count': 158, 'source_set_sha256': reuse['proof_source_set_sha256'],
        'scope': 'Inherited v31.11 machine execution with identical proof/configuration bytes; no Chapter69 machine coverage',
        'current_bytes_match_executed_bytes': True,
        'current_identity_check': 'physics/qm/kernel/evidence/v31.13/proof-reuse.json'}
    manifest_identity = ident(evidence / 'source-manifest.json')
    runtime_identity = {'receipt': ident(evidence / 'runtime/execution_receipt.json'), 'input_count': 17,
                        'scope': 'Nine actual commands; finite controls, exact certificates, one-input interval output and synthetic streams; no hardware or new Lean'}
    limits = [
        'Complex Hilbert/Born/tensor/CP, Fock representation, effective simultaneous controls and ideal calibration/filter/readout remain independent inputs.',
        'Finite classical control trees and finite untouched references only; arbitrary initial entanglement is allowed.',
        'True simultaneous evolution has infinite tails. The finite generator approximation is controlled, not exact hard support.',
        'The all-input theorem compares exact finite maps. The executed integer interval output certifies one specified entangled input only.',
        'Joint fixed-sample coverage controls false certificates under the declared calibration model, not model membership or post-admission coverage.',
        'No new Lean declarations, real device data, measured resource advantage, complete OPT reconstruction or full quantum/field/particle/gravity theory.']
    texts = {lang: (book / ('UEOT_PHYSICS' + suffix + '.md')).read_text(encoding='utf-8')
             for lang, suffix in [('zh', ''), ('en', '.en')]}
    sys.path.insert(0, str(book / 'build'))
    from verify_book import actual_claims
    parsed = {lang: actual_claims(text) for lang, text in texts.items()}
    binding_path = audit / 'chapter69_formal_bindings.json'
    binding = read(binding_path)
    assert [row['id'] for row in binding['results']] == IDS
    results = deepcopy(binding['results'])
    for row in results:
        assert row['title'] == next(item['title'] for item in parsed['zh'] if item['id'] == row['id'])
        row.update({'origin': 'NEW_IN_3_10', 'argument_status': ['N' if row['id'].startswith('C-') else 'P'],
                    'verification_scope': row['question_and_quantifiers'],
                    'runtime_receipt': 'physics/qm/kernel/evidence/v31.13/runtime/execution_receipt.json',
                    'formal_binding_detail': str(binding_path.relative_to(root)),
                    'status_axes': {'mathematical': row['mathematical_status'],
                                    'physical_selection': row['physical_selection_status'],
                                    'computational': 'SOURCE_BOUND_EXACT_INTERVAL_AND_FINITE_CONTROLS',
                                    'empirical': 'NOT_TESTED'}})
    prior = read(publication / 'prior/CHAPTER_DOSSIER.json')
    d = deepcopy(prior)
    d['chapters'].append({'number': 69, 'anchor': 'ch-69',
                          'title': re.search(r'^# 69\. (.+)$', texts['zh'], re.M).group(1),
                          'edition_status': 'NEW_IN_3_10', 'numbered_results': results,
                          'dependency_class': ['B', 'P', 'E', 'O'],
                          'verification_kind': ['analytic', 'exact_arithmetic', 'finite_floating_control', 'synthetic', 'directed_interval'],
                          'source_refs': [{'id': 'QM3113', 'locator': 'Chapter69 same-source analytic, calibration and numerical chain'}],
                          'whole_chapter_formalized': False, 'new_experimental_data': False})
    for chapter in d['chapters'] + d['appendices']:
        anchor = chapter['anchor']
        piece = body(texts['zh'], anchor)
        chapter['body_sha256'] = hashlib.sha256(piece.encode()).hexdigest()
        chapter['body_utf8_bytes'] = len(piece.encode())
        chapter['body_slice_convention'] = 'stable chapter/appendix anchor inclusive to next such anchor exclusive; final appendix through EOF; exact UTF-8 bytes'
        chapter['sections'] = [{'id': a, 'title': b} for a, b in re.findall(r'^## ((?:\d+|[A-F])\.\d+)\s+(.+)$', piece, re.M)]
        chapter['current_edition_action'] = 'NEW_IN_3_10' if anchor == 'ch-69' else 'SCIENTIFIC_BODY_PRESERVED_OR_NAVIGATION_METADATA_UPDATED_IN_3_10'
        chapter['publication_3_10'] = {lang: {'anchor': anchor, 'body_sha256': hashlib.sha256(body(text, anchor).encode()).hexdigest(),
                                                       'body_utf8_bytes': len(body(text, anchor).encode())} for lang, text in texts.items()}
        chapter['current_edition_verification'] = {'edition': '3.10', 'body_hash_checked': True, 'english_body_hash_checked': True,
                                                  'scope': 'Current source identity only; old numbered result objects and original evidence retain their exact identity'}
        if 'verification_responsibility' in chapter:
            chapter['verification_responsibility']['current_edition_acceptance_status'] = state
    for key, lang, suffix in [('canonical', 'zh', ''), ('canonical_english', 'en', '.en')]:
        d[key] = {**ident(book / ('UEOT_PHYSICS' + suffix + '.md')), 'status': state, 'chapters': 70,
                  'appendices': 6, 'numbered_results': 194, 'inherited_result_ids': 188, 'new_result_ids': 6,
                  'language': lang, 'identity_scope': 'Current exact source bytes'}
    derivatives = {'status': 'BUILT_AND_SCOPED_VISUALLY_VERIFIED', 'visual_review': ident(publication / 'visual-review.json')}
    for lang, suffix in [('zh', ''), ('en', '.en')]:
        build = read(publication / lang / 'pdf-build.json')
        derivatives[lang] = {'pdf': ident(book / ('UEOT_PHYSICS' + suffix + '.pdf')),
                             'latex': ident(book / ('UEOT_PHYSICS' + suffix + '.tex')),
                             'source_sha256': build['source_sha256'], 'build': ident(publication / lang / 'pdf-build.json')}
    revision = {'edition': '3.10', 'recorded_at_utc': now, 'scope': 'Six new Chapter69 results; old scientific bodies and all188 prior result objects preserved',
                'new_scientific_results_in_publication': 6, 'new_experimental_data': False,
                'prior_snapshot': ident(publication / 'prior/CHAPTER_DOSSIER.json'),
                'local_artifact_state': 'BUILT_AND_SCOPED_VISUALLY_VERIFIED', 'remote_publication': state,
                'review_identity_policy': 'Exactly three native AI research tasks and primary integration; not external human peer review'}
    if integration['remote_verified']:
        revision['observed_integration'] = integration['integration_receipt']
    d.update({'recorded_at_utc': now, 'edition': '3.10', 'editorial_status': state,
              'prior_complete_dossier': ident(publication / 'prior/CHAPTER_DOSSIER.json'), 'current_release_stage': state,
              'current_remote_code_identity': integration, 'unified_source_identity': proof_identity,
              'publication_source_identity': proof_identity, 'increment_source_identity': manifest_identity,
              'runtime_source_identity': runtime_identity, 'derivatives': derivatives,
              'verified_inventory': {'proof_reuse': ident(evidence / 'proof-reuse.json'), 'new_runtime': runtime_identity['receipt'],
                                     'new_lean': False, 'new_hardware_data': False},
              'validation': {'status': 'LOCAL_PUBLICATION_AND_SOURCE_IDENTITIES_VERIFIED', 'numbered_result_count': 194,
                             'all188_prior_result_objects_exactly_preserved': True, 'all111_prior_ledger_objects_exactly_preserved': True,
                             'all_body_hashes_verified': True, 'whole_physics_formalized': False, 'new_experimental_data': False,
                             'remote_verified': integration['remote_verified']},
              'completion_boundary': limits,
              'release_acceptance': {'new_lean': 'NOT_ADDED; HISTORICAL_SOURCE_REUSE_ONLY', 'new_runtime': 'PASS',
                                     'current_proof_inputs_match': True, 'current_runtime_inputs_outputs_logs_match': True,
                                     'current_publication_matches_visual_review': True, 'old_numbered_results': 'EXACTLY_PRESERVED',
                                     'publication_receipt': str((publication / 'local-acceptance.json').relative_to(root)),
                                     'remote_integration': integration},
              'next_execution_contract': 'physics/qm/UEOT_QM_EXECUTION_v31.13.md', 'publication_revision': revision,
              'historical_metadata_scope': 'All188 old numbered result objects retain historical identity. Current_edition fields describe3.10; nested old fields do not constitute new executions.'})
    for kind in ['finite_floating_control', 'directed_interval']:
        if kind not in d['status_axes']['verification_kind']:
            d['status_axes']['verification_kind'].append(kind)
    d['edition_history'].append({'edition': '3.10', 'date': now[:10], 'new_results': 6, 'prior_dossier': ident(publication / 'prior/CHAPTER_DOSSIER.json')})
    d['source_catalog']['QM3113'] = {'manifest_entry_id': 'QM3113', 'path': 'physics/qm/UEOT_QM_KERNEL_v31.13.md',
                                    'identity': 'ACTUAL_SOURCE_BOUND_ANALYTIC_EXACT_INTERVAL_AND_SYNTHETIC_INCREMENT',
                                    'use': 'Chapter69; no new Lean or real device data'}
    m = read(publication / 'prior/SOURCE_MANIFEST.json')
    old_entry_count = len(m['entries'])
    m['entries'].append({'id': 'QM3113', 'name': 'Simultaneous Galerkin bridge, joint calibration and complete numerical prediction',
                        'path': 'physics/qm/UEOT_QM_KERNEL_v31.13.md',
                        'evidence_level': 'PAPER_EXACT_INTERVAL_AND_SYNTHETIC_NO_NEW_LEAN',
                        'use': 'Six Chapter69 results; exact finite-map all-input theorem separated from one-input numerical certification'})
    m.update({'recorded_at_utc': now, 'edition': '3.10', 'prior_complete_manifest': ident(publication / 'prior/SOURCE_MANIFEST.json'),
              'current_code_baseline': integration.get('verified_scientific_main', BASELINE),
              'current_code_baseline_role': 'Research entry until actual remote verification; original inherited proof execution separately identified',
              'current_code_identity': proof_identity, 'canonical_identity': d['canonical'], 'canonical_english_identity': d['canonical_english'],
              'unified_source_identity': proof_identity, 'publication_source_identity': proof_identity,
              'current_remote_code_identity': integration, 'current_release_stage': state,
              'remote_metadata_completion': {'state': state, 'metadata_followup_is_not_a_new_scientific_execution': True},
              'local_release_receipt': str((publication / 'local-acceptance.json').relative_to(root)),
              'local_release_receipt_scope': 'Book3.10 publication, not a scientific proof',
              'scientific_execution_partition': {'new_proof': 'PAPER_ONLY_NO_NEW_LEAN', 'new_runtime': runtime_identity['receipt']['path'],
                                                  'historical_reuse': 'physics/qm/kernel/evidence/v31.13/proof-reuse.json', 'real_data': False},
              'original_entry_preservation': {'entry_count': old_entry_count, 'all_entry_records_identical_to_v3_9': True,
                                             'prior_manifest': ident(publication / 'prior/SOURCE_MANIFEST.json')},
              'publication_revision': revision, 'increment_source_identity': manifest_identity, 'runtime_source_identity': runtime_identity})
    write(book / 'SOURCE_MANIFEST.json', m)
    d['book_source_manifest'] = ident(book / 'SOURCE_MANIFEST.json')
    write(book / 'CHAPTER_DOSSIER.json', d)
    old_ledger = read(q / 'status/CLAIM_LEDGER_v31.12.json')
    ledger = {k: deepcopy(v) for k, v in old_ledger.items() if k not in ['claims', 'verification', 'inheritance', 'nonclaims']}
    claims = []
    for row in results:
        claims.append({'id': 'QMK-' + row['id'], 'claim': row['title'], 'book_result': row['id'], 'layers': row['dependency_class'],
                       'status_axes': row['status_axes'], 'machine_status': row['machine_status'], 'premises': row['premises'],
                       'witnesses': [], 'paper_only': row['paper_only'], 'verification_scope': row['verification_scope'],
                       'formal_binding_detail': row['formal_binding_detail'], 'runtime_receipt': row['runtime_receipt'],
                       'new_hardware_data': False, 'remote_status': state})
    ledger.update({'date': now[:10], 'version': 'v31.13-kernel1.13', 'previous_ledger': 'physics/qm/status/CLAIM_LEDGER_v31.12.json',
                   'research_baseline': BASELINE, 'claim_count': 117, 'new_claim_count': 6, 'claims': old_ledger['claims'] + claims,
                   'verification': {'state': state, 'new_lean': False, 'inherited_proof_reuse': 'physics/qm/kernel/evidence/v31.13/proof-reuse.json',
                                    'runtime': runtime_identity['receipt']['path'], 'increment_source_manifest': manifest_identity,
                                    'remote_integration': integration},
                   'inheritance': {'inherited_claims': 111, 'all_objects_exactly_preserved': True, 'historical_status_words_not_relabelled_as_new_execution': True},
                   'nonclaims': old_ledger['nonclaims'] + limits, 'metadata_updated_at_utc': now})
    write(q / 'status/CLAIM_LEDGER_v31.13.json', ledger)
    current = {'schema': 'ueot-qm-current/6', 'date': now[:10], 'version': 'v31.13', 'kernel_version': '1.13',
               'scientific_version': 'v31.13 / Kernel 1.13', 'research_baseline': BASELINE,
               'kernel': 'physics/qm/UEOT_QM_KERNEL_v31.13.md', 'execution_contract': 'physics/qm/UEOT_QM_EXECUTION_v31.13.md',
               'runtime_entrypoint': 'physics/qm/simultaneous_cutoff/README.md', 'formalization': 'formalization/ueot-qm/README.md',
               'roadmap': 'physics/qm/ROADMAP.md', 'claim_ledger': 'physics/qm/status/CLAIM_LEDGER_v31.13.json',
               'previous_claim_ledger': 'physics/qm/status/CLAIM_LEDGER_v31.12.json', 'verification_state': state,
               'local_checkpoint_state': 'PASS', 'status_axes': {'mathematical': 'DECLARED_MODEL_ANALYTIC_PROOFS_AND_COUNTEREXAMPLE',
                   'physical_selection': 'COMPLEX_MODEL_AND_EFFECTIVE_CONTROL_CALIBRATION_INPUTS_REMAIN_INDEPENDENT',
                   'computational': 'EXACT_BOUND_AND_ONE_INPUT_INTERVAL_OUTPUT; SYNTHETIC_TESTERS', 'empirical': 'UNTESTED_NO_REAL_DEVICE_DATA'},
               'source_identity': proof_identity, 'proof_receipt': proof_identity['verification'],
               'proof_reuse_receipt': 'physics/qm/kernel/evidence/v31.13/proof-reuse.json', 'source_manifest': proof_identity['manifest'],
               'increment_source_manifest': manifest_identity['path'], 'runtime_receipt': runtime_identity['receipt']['path'],
               'integration': integration, 'local_verification': {'new_lean': False, 'new_runtime': 'PASS', 'proof_inputs_match': True,
                   'old_runtime_inputs_match': True, 'publication_matches_visual_review': True, 'historical_heavy_suites_rerun_locally': False},
               'completed_in_this_delivery': IDS, 'book': {'edition': '3.10', 'chapters': 70, 'appendices': 6, 'numbered_results': 194,
                   'inherited_numbered_results': 188, 'new_numbered_results': 6, 'canonical': d['canonical']['path'],
                   'english': d['canonical_english']['path'], 'dossier': ident(book / 'CHAPTER_DOSSIER.json'),
                   'whole_book_formalized': False, 'local_acceptance': str((publication / 'local-acceptance.json').relative_to(root))},
               'historical_current_checkpoint': ident(publication / 'prior/CURRENT.json'),
               'historical_claim_scope': 'All111 prior claim objects and188 prior result objects retain exact historical identity',
               'scope_limits': limits, 'next_execution': {'theory': 'Finite Gaussian bath or regulated free-field mode deletion under identical intervention slots; persistent-memory countercontrol',
                   'operations': 'Complete finiteTest quotient, finite-precision reconstruction and independent complex-sector selection remain separate',
                   'data': 'Real ordered source/drive calibration, shared-gate/filter/readout bias and energy tests, full failed records and actual resources'},
               'new_hardware_data': False, 'metadata_updated_at_utc': now,
               'metadata_scope': 'Publication and execution identity binding; no proof generated or empirical claim added by this script'}
    if integration['remote_verified']:
        current['integration_receipt'] = integration['integration_receipt']['path']
    write(q / 'status/CURRENT.json', current)
    print(json.dumps({'status': 'METADATA_WRITTEN_REQUIRES_INDEPENDENT_CHECK', 'chapters': len(d['chapters']),
                      'results': sum(len(ch.get('numbered_results', [])) for ch in d['chapters']), 'claims': len(ledger['claims']),
                      'remote': integration['remote_verified']}))


if __name__ == '__main__':
    main()
