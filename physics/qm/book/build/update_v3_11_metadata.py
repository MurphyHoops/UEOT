#!/usr/bin/env python3
"""Bind the persistent-bath edition to observed sources and evidence.

This publishes metadata, not proofs. Historical result and claim objects are
copied exactly; the independent increment gate must run after this script.
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

IDS = {'C-QSEL-02', 'P-TOM-01', 'P-MICRO-08', 'P-MICRO-09',
       'C-QMEM-01', 'P-NUM-01', 'P-QMEM-02', 'P-ROB-06', 'P-ROB-07'}
BASELINE = 'ee7fb2793a1dbb519703bba05f535f0d962d9e56'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo-root', type=Path, default=Path(__file__).resolve().parents[4])
    ap.add_argument('--integration', type=Path)
    args = ap.parse_args()
    root = args.repo_root.resolve()
    q = root / 'physics/qm'
    book = q / 'book'
    pub = book / 'evidence/v3.11'
    prior = pub / 'prior'
    ev = q / 'kernel/evidence/v31.14'
    audit = q / 'audits/PERSISTENT_BATH_v31.14'
    now = datetime.now(timezone.utc).isoformat()

    def read(p):
        return json.loads(p.read_text())

    def write(p, obj):
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n')

    def ident(p):
        b = p.read_bytes()
        return {'path': str(p.relative_to(root)), 'sha256': hashlib.sha256(b).hexdigest(), 'bytes': len(b)}

    def body(text, anchor):
        start = text.index(f'<a id="{anchor}"></a>')
        m = re.search(r'(?m)^<a id="(?:ch-\d+|appendix-[a-z])"></a>', text[start+len(anchor)+16:])
        end = start+len(anchor)+16+m.start() if m else len(text)
        return text[start:end]

    # Do not silently erase an observed same-edition remote acceptance during
    # a later metadata-only invocation. Supplying its existing receipt is an
    # ordinary continuation, not a new user-approval requirement.
    existing_path = q / 'status/CURRENT.json'
    if existing_path.is_file():
        existing = read(existing_path)
        same_edition_verified = (existing.get('version') == 'v31.14' and
            (existing.get('integration', {}).get('remote_verified') is True or
             existing.get('verification_state') == 'MAIN_SCIENTIFIC_SOURCE_AND_CI_VERIFIED'))
        if same_edition_verified and not args.integration:
            raise RuntimeError('Refusing to downgrade verified v31.14 to local pending; '
                               'pass the existing verified --integration receipt for this continuation.')

    sys.path.insert(0, str(book / 'build'))
    from verify_book import inspect_book
    texts = {lang: (book / f'UEOT_PHYSICS{suffix}.md').read_text()
             for lang, suffix in [('zh', ''), ('en', '.en')]}
    inspected = {lang: inspect_book(text) for lang, text in texts.items()}
    assert all(x['chapters'] == 71 and x['numbered_results'] == 203 for x in inspected.values())
    parsed = [x for x in inspected['zh']['claims'] if x['chapter'] == 70]
    assert {x['id'] for x in parsed} == IDS
    bindings = read(audit / 'chapter70_formal_bindings.json')['results']
    by_id = {x['id']: x for x in bindings}
    assert set(by_id) == IDS
    rows = []
    for item in parsed:
        row = deepcopy(by_id[item['id']])
        assert row['title'] == item['title']
        row.update({'origin': 'NEW_IN_3_11', 'machine_status': 'PAPER_AND_EXECUTABLE_EVIDENCE_NO_NEW_LEAN',
                    'runtime_receipt': 'physics/qm/kernel/evidence/v31.14/runtime/execution_receipt.json',
                    'formal_binding_detail': 'physics/qm/audits/PERSISTENT_BATH_v31.14/chapter70_formal_bindings.json'})
        rows.append(row)

    runtime = read(ev / 'runtime/execution_receipt.json')
    acceptance = read(pub / 'local-acceptance.json')
    assert runtime['status'] == 'PASS' and runtime['inputs_stable_during_execution']
    accounting = runtime['data_accounting']
    assert accounting['new_synthetic_shots_this_run'] == 0
    assert accounting['hardware_shots_this_run'] == 0 and accounting['new_Lean_runs_this_run'] == 0
    assert acceptance['status'] == 'PASS_SCOPED' and not acceptance['new_hardware_data']
    mutable_targets = {'physics/qm/book/SOURCE_MANIFEST.json', 'physics/qm/book/CHAPTER_DOSSIER.json',
                       'physics/qm/status/CURRENT.json', 'physics/qm/status/CLAIM_LEDGER_v31.14.json'}
    source_inventory = read(ev / 'source-manifest.json')
    for record in source_inventory['files']:
        assert record['path'] not in mutable_targets | {'physics/qm/kernel/evidence/v31.14/source-manifest.json'}
        assert ident(root / record['path']) == {k: record[k] for k in ('path', 'sha256', 'bytes')}
    required_artifacts = {f'physics/qm/book/UEOT_PHYSICS{suffix}.{extension}'
                          for suffix in ('', '.en') for extension in ('md', 'tex', 'pdf')}
    assert required_artifacts <= {r['path'] for r in acceptance['current_artifacts']}
    for record in acceptance['current_artifacts']:
        assert record['path'] not in mutable_targets | {'physics/qm/book/evidence/v3.11/local-acceptance.json'}
        assert ident(root / record['path']) == record
    assert acceptance['visual_review'] == ident(pub / 'visual-review.json')
    visual = read(pub / 'visual-review.json')
    assert visual['edition'] == '3.11' and visual['status'] == 'PASS_SCOPED'
    assert visual.get('independent_human_peer_review') is False
    for lang, suffix in [('zh', ''), ('en', '.en')]:
        reviewed = visual['languages'][lang]
        assert reviewed['source'] == ident(book / f'UEOT_PHYSICS{suffix}.md')
        assert reviewed['pdf'] == ident(book / f'UEOT_PHYSICS{suffix}.pdf')
        assert reviewed['build'] == ident(pub / lang / 'pdf-build.json')
        assert reviewed['required_pages'] and set(reviewed['required_pages']) <= set(reviewed['physical_pages'])
        assert all(isinstance(p, int) and 1 <= p <= reviewed['page_count'] for p in reviewed['physical_pages'])
        assert reviewed['review_reports']
        for report in reviewed['review_reports']:
            assert report['path'] not in mutable_targets | {
                'physics/qm/book/evidence/v3.11/visual-review.json',
                'physics/qm/book/evidence/v3.11/local-acceptance.json',
                'physics/qm/kernel/evidence/v31.14/source-manifest.json'}
            assert report == ident(root / report['path'])
    integration = {'state': 'LOCAL_VERIFIED_REMOTE_PENDING', 'remote_verified': False,
                   'research_entry_baseline': BASELINE}
    if args.integration:
        path = args.integration if args.integration.is_absolute() else root / args.integration
        observed = read(path)
        assert observed['status'] == 'PASS' and observed['scientific_main_verified']
        integration.update({'state': 'MAIN_SCIENTIFIC_SOURCE_AND_CI_VERIFIED', 'remote_verified': True,
                            'scientific_source_head': observed['scientific_source_head'],
                            'verified_scientific_main': observed['verified_scientific_main'],
                            'tree': observed['tree'], 'pr': observed['pr'],
                            'pr_run': observed['pr_run'], 'main_run': observed['main_run'],
                            'integration_receipt': ident(path)})
    state = integration['state']
    proof = deepcopy(read(prior / 'CURRENT.json')['source_identity'])
    proof.update({'scope': 'Historical v31.11 proof execution only; 158 unchanged inputs; no new Chapter69 or Chapter70 Lean coverage',
                  'current_identity_check': 'physics/qm/kernel/evidence/v31.14/proof-reuse.json'})
    reuse = read(ev / 'proof-reuse.json')
    assert reuse['proof_reuse_eligible'] and not reuse['errors'] and reuse['proof_input_count'] == 158
    assert reuse['proof_source_set_sha256'] == proof['source_set_sha256']
    assert reuse['new_lean_execution'] is False
    axes = {'mathematical': 'DECLARED_MODEL_PAPER_PROOFS_AND_SCOPED_NONIMPLICATIONS',
            'physical_selection': 'GLOBAL_COMPLEX_SELECTION_OPEN; REACHABLE_SECTOR_OBSTRUCTION_PROVED',
            'computational': 'ALL_INPUT_INTERVAL_CHOI_AND_RATIONAL_CP_TP_MAP; SYNTHETIC_CALIBRATION_HOLDOUT',
            'empirical': 'MATCHED_DEVICE_NOT_CERTIFIED; EXTERNAL_PROCESSED_OBSERVABLE_REPRODUCED',
            'method_gain': 'EQUIVALENT_NO_ADDED_GAIN_AGAINST_STRONG_STANDARD_PROCESS'}
    limits = [
        'Complex Hilbert, tensor/Born/CP, Fock modes, frequencies, relative couplings and vacuum preparation remain independent physical inputs.',
        'The executed model is a fixed three-slot qubit source with two persistent modes, complete failure records and arbitrary untouched finite references.',
        'General Gaussian formulas preserve correlations, but the calibrated and numerical certificate uses the frozen vacuum family only.',
        'Fixed-policy external-channel tomography and repaired terminal Choi maps do not certify every alternative intermediate intervention.',
        'Calibration assumes stationary independent trials, known preparation and controls, error-free records and one shared symmetric detector visibility.',
        'Synthetic coverage and heldout non-rejection do not establish device membership; external processed data do not supply missing matched raw shots.',
        'No new Lean declarations, extra natural prediction, strong-baseline gain, global complex-sector selection, QFT, gravity or cosmological closure is claimed.'
    ]
    runtime_identity = {'receipt': ident(ev / 'runtime/execution_receipt.json'),
                        'scope': 'Actual production replay over unchanged authored synthetic rows; no new sampling, Lean or hardware. Original author runs retain their own identities.',
                        'source_file_count': len(runtime['source_files']),
                        'unique_archived_synthetic_rows': accounting['total_unique_archived_synthetic_rows'],
                        'new_synthetic_shots_this_replay': 0}
    derivatives = {'status': 'BUILT_AND_SCOPED_VISUALLY_VERIFIED', 'visual_review': ident(pub / 'visual-review.json')}
    for lang, suffix in [('zh', ''), ('en', '.en')]:
        derivatives[lang] = {'pdf': ident(book / f'UEOT_PHYSICS{suffix}.pdf'),
                             'latex': ident(book / f'UEOT_PHYSICS{suffix}.tex'),
                             'source_sha256': ident(book / f'UEOT_PHYSICS{suffix}.md')['sha256'],
                             'build': ident(pub / lang / 'pdf-build.json')}
    revision = {'edition': '3.11', 'recorded_at_utc': now,
                'scope': 'Nine Chapter70 results; all194 inherited result objects and117 inherited claim objects retained exactly',
                'new_scientific_results_in_publication': 9, 'new_experimental_data': False,
                'prior_snapshot': ident(prior / 'CHAPTER_DOSSIER.json'),
                'local_artifact_state': 'BUILT_AND_SCOPED_VISUALLY_VERIFIED', 'remote_publication': state,
                'review_identity_policy': 'Exactly three native AI research agents plus primary adjudication; not external human peer review'}

    m = deepcopy(read(prior / 'SOURCE_MANIFEST.json'))
    m['entries'].append({'id': 'QM3114', 'name': 'Persistent Gaussian source, fixed-policy testers, exact physical prediction and identifiable calibration',
                         'path': 'physics/qm/UEOT_QM_KERNEL_v31.14.md',
                         'evidence_level': 'PAPER_EXACT_INTERVAL_SYNTHETIC_AND_EXTERNAL_PROCESSED_REPRODUCTION_NO_NEW_LEAN',
                         'use': 'Nine scoped Chapter70 results; no matched-device certification or global physical selection'})
    m.update({'edition': '3.11', 'recorded_at_utc': now, 'prior_complete_manifest': ident(prior / 'SOURCE_MANIFEST.json'),
              'current_code_baseline': BASELINE, 'current_code_baseline_role': 'Recovered Chapter69 scientific main',
              'current_code_identity': proof, 'current_remote_code_identity': integration,
              'current_release_stage': state,
              'remote_metadata_completion': {'state': state, 'metadata_followup_is_not_a_new_scientific_execution': True},
              'canonical_identity': {**ident(book / 'UEOT_PHYSICS.md'), 'status': state, 'language': 'zh',
                                     'chapters': 71, 'appendices': 6, 'numbered_results': 203,
                                     'inherited_result_ids': 194, 'new_result_ids': 9, 'identity_scope': 'Current exact source bytes'},
              'canonical_english_identity': {**ident(book / 'UEOT_PHYSICS.en.md'), 'status': state, 'language': 'en',
                                             'chapters': 71, 'appendices': 6, 'numbered_results': 203,
                                             'inherited_result_ids': 194, 'new_result_ids': 9, 'identity_scope': 'Current exact source bytes'},
              'unified_source_identity': deepcopy(proof), 'publication_source_identity': deepcopy(proof),
              'current_code_manifest_scope': 'Historical v31.11 Lean inputs only; current scientific increment is separately bound below',
              'current_publication_code_manifest': '../kernel/evidence/v31.14/source-manifest.json',
              'current_increment_code_manifest': '../kernel/evidence/v31.14/source-manifest.json',
              'increment_source_identity': ident(ev / 'source-manifest.json'),
              'runtime_source_identity': runtime_identity, 'publication_revision': revision,
              'local_release_receipt': ident(pub / 'local-acceptance.json'),
              'local_release_receipt_scope': 'Book3.11 actual scoped publication; not a new scientific proof or full-book visual claim',
              'scientific_execution_partition': {'new_proof': 'PAPER_AND_SCOPED_EXECUTABLE_EVIDENCE_NO_NEW_LEAN',
                                                 'new_runtime': 'physics/qm/kernel/evidence/v31.14/runtime/execution_receipt.json',
                                                 'historical_reuse': 'physics/qm/kernel/evidence/v31.14/proof-reuse.json',
                                                 'new_device_data': False, 'external_processed_observable_reproduced': True,
                                                 'new_synthetic_shots_this_replay': 0},
              'original_entry_preservation': 'All prior source entries preserved exactly; current edition keys do not rename historical executions'})
    write(book / 'SOURCE_MANIFEST.json', m)

    d = deepcopy(read(prior / 'CHAPTER_DOSSIER.json'))
    d['chapters'].append({'number': 70, 'anchor': 'ch-70',
                          'title': re.search(r'^# 70\. (.+)$', texts['zh'], re.M).group(1),
                          'edition_status': 'NEW_IN_3_11', 'numbered_results': rows,
                          'dependency_class': ['B', 'P', 'E', 'O'],
                          'verification_kind': ['analytic', 'exact_arithmetic', 'directed_interval', 'finite_floating_control', 'synthetic'],
                          'source_refs': [{'id': 'QM3114', 'locator': 'Chapter70 and persistent-bath evidence'}],
                          'whole_chapter_formalized': False, 'new_experimental_data': False})
    for chapter in d['chapters'] + d['appendices']:
        piece = body(texts['zh'], chapter['anchor'])
        chapter.update({'body_sha256': hashlib.sha256(piece.encode()).hexdigest(),
                        'body_utf8_bytes': len(piece.encode()),
                        'sections': [{'id': a, 'title': b} for a, b in re.findall(r'^## ((?:\d+|[A-F])\.\d+)\s+(.+)$', piece, re.M)],
                        'publication_3_11': {lang: {'anchor': chapter['anchor'],
                                                  'body_sha256': hashlib.sha256(body(text, chapter['anchor']).encode()).hexdigest(),
                                                  'body_utf8_bytes': len(body(text, chapter['anchor']).encode())}
                                             for lang, text in texts.items()},
                        'current_edition_verification': {'edition': '3.11', 'body_hash_checked': True, 'english_body_hash_checked': True,
                                                        'scope': 'Current body identity; historical result objects retain their execution scope'}})
    for key, suffix, lang in [('canonical', '', 'zh'), ('canonical_english', '.en', 'en')]:
        d[key] = {**ident(book / f'UEOT_PHYSICS{suffix}.md'), 'status': state, 'language': lang,
                  'chapters': 71, 'appendices': 6, 'numbered_results': 203,
                  'inherited_result_ids': 194, 'new_result_ids': 9}
    d.update({'edition': '3.11', 'recorded_at_utc': now, 'editorial_status': state,
              'current_release_stage': state, 'current_remote_code_identity': integration,
              'prior_complete_dossier': ident(prior / 'CHAPTER_DOSSIER.json'),
              'book_source_manifest': ident(book / 'SOURCE_MANIFEST.json'), 'derivatives': derivatives,
              'unified_source_identity': proof, 'publication_source_identity': proof,
              'increment_source_identity': ident(ev / 'source-manifest.json'),
              'runtime_source_identity': runtime_identity, 'publication_revision': revision,
              'historical_metadata_scope': 'All194 inherited result objects and117 inherited claim objects retain exact historical identity. publication_3_11/current top-level fields describe3.11; older nested edition fields do not constitute new executions.',
              'verified_inventory': {'proof_reuse': ident(ev / 'proof-reuse.json'),
                                     'new_runtime': runtime_identity['receipt'],
                                     'increment_source_manifest': ident(ev / 'source-manifest.json'),
                                     'new_lean': False, 'new_hardware_data': False,
                                     'external_processed_observable_reproduced': True,
                                     'new_synthetic_shots_this_replay': 0},
              'completion_boundary': limits,
              'validation': {'status': 'LOCAL_PUBLICATION_AND_SOURCE_IDENTITIES_VERIFIED',
                             'numbered_result_count': 203, 'all194_prior_result_objects_exactly_preserved': True,
                             'all117_prior_ledger_objects_exactly_preserved': True, 'all_body_hashes_verified': True,
                             'whole_physics_formalized': False, 'new_experimental_data': False,
                             'remote_verified': integration['remote_verified']},
              'release_acceptance': {'new_lean': False, 'new_runtime': 'PASS', 'publication_receipt': ident(pub / 'local-acceptance.json'),
                                     'remote_integration': integration},
              'next_execution_contract': 'physics/qm/UEOT_QM_EXECUTION_v31.14.md'})
    d['source_catalog']['QM3114'] = m['entries'][-1]
    d['edition_history'].append({'edition': '3.11', 'date': '2026-11-14', 'new_results': 9,
                                 'prior_dossier': ident(prior / 'CHAPTER_DOSSIER.json')})
    write(book / 'CHAPTER_DOSSIER.json', d)

    ledger = deepcopy(read(prior / 'CLAIM_LEDGER_v31.13.json'))
    assert len(ledger['claims']) == 117
    for row in rows:
        ledger['claims'].append({'id': 'QMK-'+row['id'], 'book_result': row['id'], 'claim': row['title'],
                                 'layers': row['dependency_class'], 'status_axes': row['status_axes'],
                                 'machine_status': row['machine_status'], 'premises': row['premises'],
                                 'paper_only': [row['question_and_quantifiers']],
                                 'verification_scope': row['question_and_quantifiers'],
                                 'formal_binding_detail': row['formal_binding_detail'],
                                 'runtime_receipt': row['runtime_receipt'], 'new_hardware_data': False,
                                 'remote_status': state})
    ledger.update({'version': 'v31.14', 'date': '2026-11-14', 'metadata_updated_at_utc': now,
                   'previous_ledger': 'physics/qm/status/CLAIM_LEDGER_v31.13.json',
                   'research_baseline': BASELINE, 'claim_count': 126, 'new_claim_count': 9,
                   'inheritance': {'prior_claim_count': 117, 'prior_objects_exact': True,
                                   'prior_ledger': ident(prior / 'CLAIM_LEDGER_v31.13.json')},
                   'verification': {'state': state, 'runtime': runtime_identity, 'new_lean': False},
                   'canonical_monograph': 'physics/qm/book/UEOT_PHYSICS.md', 'nonclaims': limits})
    write(q / 'status/CLAIM_LEDGER_v31.14.json', ledger)
    current = {'schema': 'ueot-qm-current/7', 'date': '2026-11-14', 'version': 'v31.14', 'kernel_version': '1.14',
               'scientific_version': 'v31.14 / Kernel 1.14', 'research_baseline': BASELINE,
               'kernel': 'physics/qm/UEOT_QM_KERNEL_v31.14.md',
               'execution_contract': 'physics/qm/UEOT_QM_EXECUTION_v31.14.md',
               'runtime_entrypoint': 'physics/qm/persistent_bath/README.md',
               'formalization': 'formalization/ueot-qm/README.md', 'roadmap': 'physics/qm/ROADMAP.md',
               'claim_ledger': 'physics/qm/status/CLAIM_LEDGER_v31.14.json',
               'previous_claim_ledger': 'physics/qm/status/CLAIM_LEDGER_v31.13.json',
               'verification_state': state, 'local_checkpoint_state': 'PASS', 'status_axes': axes,
               'source_identity': proof, 'proof_receipt': 'physics/qm/kernel/evidence/v31.11/lean-verification.json',
               'proof_reuse_receipt': 'physics/qm/kernel/evidence/v31.14/proof-reuse.json',
               'increment_source_manifest': 'physics/qm/kernel/evidence/v31.14/source-manifest.json',
               'runtime_receipt': 'physics/qm/kernel/evidence/v31.14/runtime/execution_receipt.json',
               'integration': integration, 'completed_in_this_delivery': [r['id'] for r in rows],
               'book': {'edition': '3.11', 'chapters': 71, 'appendices': 6, 'numbered_results': 203,
                        'inherited_numbered_results': 194, 'new_numbered_results': 9,
                        'canonical': 'physics/qm/book/UEOT_PHYSICS.md', 'english': 'physics/qm/book/UEOT_PHYSICS.en.md',
                        'dossier': ident(book / 'CHAPTER_DOSSIER.json'), 'whole_book_formalized': False,
                        'local_acceptance': 'physics/qm/book/evidence/v3.11/local-acceptance.json'},
               'historical_current_checkpoint': ident(prior / 'CURRENT.json'),
               'scope_limits': limits, 'new_hardware_data': False, 'metadata_updated_at_utc': now,
               'next_execution': {'theory': 'Correlated nonvacuum bath with controlled finite prediction or a bounded mode-deletion contract',
                                  'selection': 'Independent access-completeness/minimality principle or an explicit nonimplication',
                                  'data': 'Matched ordered raw shots, SPAM/leakage/preparation/control/readout evidence and full physical costs'}}
    write(q / 'status/CURRENT.json', current)
    print(json.dumps({'status': state, 'results': 203, 'claims': 126, 'old_results_preserved': 194}))


if __name__ == '__main__':
    main()
