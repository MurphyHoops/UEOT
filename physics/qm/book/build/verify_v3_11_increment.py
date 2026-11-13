#!/usr/bin/env python3
"""Read-only source, preservation and evidence gate for edition 3.11.

This gate does not import the metadata writer and does not claim to prove the
paper theorems or validate a device. It checks their declared execution scope.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import sys

NEW_IDS = {'C-QSEL-02', 'P-TOM-01', 'P-MICRO-08', 'P-MICRO-09',
           'C-QMEM-01', 'P-NUM-01', 'P-QMEM-02', 'P-ROB-06', 'P-ROB-07'}
SHARED_SHA = '685d373bb5a70a677fd4d110cb81c6624260de95ea39cc60070a8f4bd9f19668'
PROOF_SET_SHA = 'f9ea1e3e9bc695e3916d764e8f005d98556e4541653d439a60e57a5fb8c4cacf'
MUTABLE_METADATA = {
    'physics/qm/book/SOURCE_MANIFEST.json', 'physics/qm/book/CHAPTER_DOSSIER.json',
    'physics/qm/status/CURRENT.json', 'physics/qm/status/CLAIM_LEDGER_v31.14.json',
}
REQUIRED_ARTIFACTS = {f'physics/qm/book/UEOT_PHYSICS{suffix}.{extension}'
                      for suffix in ('', '.en') for extension in ('md', 'tex', 'pdf')}


def repository_path(root, name):
    """Resolve a current repository identity, never an old absolute scratch path."""
    relative = Path(name)
    if relative.is_absolute() or '..' in relative.parts:
        raise AssertionError('Expected repository-relative identity: ' + str(name))
    path = (root / relative).resolve()
    if not path.is_relative_to(root):
        raise AssertionError('Identity escapes repository: ' + str(name))
    return path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_identity(root, row, check, *, path=None):
    path = path or repository_path(root, row['path'])
    label = path.relative_to(root).as_posix()
    check('hash ' + label, sha(path) == row['sha256'])
    check('bytes ' + label, path.stat().st_size == row['bytes'])
    return path


def verify_runtime(root, runtime, check):
    """Rebind the three recorded execution roots to this checkout by role.

    Absolute paths in the immutable receipt remain historical observations.
    This mapping makes copied evidence portable without claiming that a moved
    checkout was the process's original working directory.
    """
    ev = root / 'physics/qm/kernel/evidence/v31.14'
    out = ev / 'runtime'
    source = root / 'physics/qm/persistent_bath'
    mappings = [(Path(runtime[key]), target) for key, target in (
        ('source_dir', source), ('authored_evidence_dir', ev / 'authored'), ('output_dir', out))]
    mappings.sort(key=lambda pair: len(pair[0].parts), reverse=True)

    def rebase(name, *, output_only=False):
        old = Path(name)
        for recorded, target in mappings:
            if output_only and target != out:
                continue
            if old.is_relative_to(recorded):
                relative = old.relative_to(recorded)
                return repository_path(root, (target / relative).relative_to(root))
        raise AssertionError('Unmapped recorded execution path: ' + str(name))

    check('runtime receipt schema', runtime['schema'] == 'ueot.persistent_bath.portable_verification.v1')
    check('actual runtime complete', runtime['status'] == 'PASS' and runtime['inputs_stable_during_execution'] is True)
    verify_identity(root, runtime['runner'], check, path=source / 'run_verification.py')
    expected_sources = {
        'finite_operations.py', 'verify_a.py', 'review_b.py', 'dynamics.py', 'verify_dynamics.py',
        'interval_certificate.py', 'build_certificates.py', 'certify_memory_witness.py',
        'physical_prediction.py', 'common_c.py', 'calibrate.py', 'generate_synthetic.py',
        'interval_source.py', 'verify_generation.py', 'evaluate_holdout.py',
        'finalize_certificate.py', 'reproduce_external_observable.py',
    }
    check('runtime complete scientific source inventory', set(runtime['source_files']) == expected_sources)
    for name, row in runtime['source_files'].items():
        path = rebase(row['path'])
        check('runtime source role ' + name, path == source / name)
        verify_identity(root, row, check, path=path)
    for name, row in runtime['copied_inputs'].items():
        origin = rebase(row['source']['path'])
        working = rebase(row['working_copy'], output_only=True)
        verify_identity(root, row['source'], check, path=origin)
        verify_identity(root, row['source'], check, path=working)
        check('copied input identity ' + name, row['sha256'] == row['source']['sha256'])
    check('runtime copied source completeness',
          {Path(k).name for k in runtime['copied_inputs'] if k.startswith('source/')} == expected_sources)
    for name, row in runtime['output_files'].items():
        path = repository_path(root, (out.relative_to(root) / name))
        check('runtime output has no self binding ' + name, path not in (out / 'runtime.json', out / 'execution_receipt.json'))
        verify_identity(root, row, check, path=path)
    expected_commands = {
        'A_verify', 'B_dynamics', 'B_eight_interval_certificates', 'B_strict_memory_event',
        'A_independent_B_review', 'C_optional_calibration_readback', 'C_generation_probability_audit',
        'C_frozen_holdout', 'C_final_exact_certificate', 'C_external_processed_observable',
    }
    check('runtime ten required commands', len(runtime['commands']) == 10 and
          {row['name'] for row in runtime['commands']} == expected_commands)
    for command in runtime['commands']:
        check('command success ' + command['name'], command['returncode'] == 0)
        rebase(command['cwd'], output_only=True)
        for stream in ('stdout', 'stderr'):
            path = repository_path(root, out.relative_to(root) / command[stream])
            check(command['name'] + ' ' + stream + ' hash', sha(path) == command[stream + '_sha256'])
    checkpoints = runtime['immutability_checkpoints']
    check('all execution immutability checkpoints', bool(checkpoints) and
          all(row['files_checked'] > 0 and row['changed'] == [] for row in checkpoints))
    counts = runtime['data_accounting']
    check('runtime reused complete frozen rows', counts['calibration']['reused_rows'] == 400000 and
          counts['holdout']['reused_rows'] == 1200000 and counts['total_unique_archived_synthetic_rows'] == 1600000)
    check('runtime no new samples Lean or hardware', counts['new_synthetic_shots_this_run'] == 0 and
          counts['hardware_shots_this_run'] == 0 and counts['new_Lean_runs_this_run'] == 0)
    for family in ('calibration', 'holdout'):
        row = counts[family]['historical_generation_receipt']
        verify_identity(root, row, check, path=rebase(row['path'], output_only=True))
    check('frozen nominal retained', runtime['original_nominal_sha256'] == sha(out / 'work_c/NOMINAL_MODEL.json'))
    check('frozen holdout plan retained', runtime['original_holdout_plan_sha256'] == sha(out / 'work_c/FROZEN_HOLDOUT_PLAN.json'))
    readback = runtime['calibration_readback']
    check('isolated calibration readback scope', readback['enabled'] is True and readback['different_fields'] == [] and
          readback['holdout_or_truth_copied_to_estimator_directory'] is False and readback['readback_used_for_holdout'] is False)
    check('calibration readback output bound', readback['new_readback_output_sha256'] == sha(out / 'calibration_readback/NOMINAL_MODEL.json'))
    check('no truth or heldout rows in estimator directory', not (out / 'calibration_readback/SYNTHETIC_TRUTH.json').exists() and
          not (out / 'calibration_readback/holdout_shots.npz').exists())
    check('execution receipt is an unchanged byte copy', (out / 'runtime.json').read_bytes() == (out / 'execution_receipt.json').read_bytes())


def verify_final_bounds(final, nominal, heldout, check):
    """Check final scientific budgets using rational arithmetic, not float formatting."""
    F = Fraction
    lo, hi = map(F, nominal['lambda_projection_outer'])
    eta_lo, eta_hi = map(F, nominal['eta_projection_outer'])
    lam, eta = F(nominal['lambda_hat']), F(nominal['eta_hat'])
    parameter = F(51, 10) * max(lam - lo, hi - lam)
    visibility = max(eta - eta_lo, eta_hi - eta) / 2
    check('parameter budget exact Fraction', F(final['parameter_error_exact']) == parameter)
    check('terminal detector budget exact Fraction', F(final['terminal_visibility_error_exact']) == visibility)
    check('analytic truncation and physical repair budgets', F(final['truncation_error_exact']) == F('0.00001344') and
          F(final['physical_numerical_repair_error_exact']) == F('0.00000001'))
    quantum = parameter + F(final['truncation_error_exact']) + F(final['physical_numerical_repair_error_exact'])
    check('quantum budget exact sum', F(final['quantum_complete_CQ_bound_exact']) == quantum)
    check('measured budget exact sum', F(final['fixed_complete_terminal_tester_bound_exact']) == quantum + visibility)
    for exact, upper in [('parameter_error_exact', 'parameter_error_upper'),
                         ('terminal_visibility_error_exact', 'terminal_visibility_error_upper'),
                         ('quantum_complete_CQ_bound_exact', 'quantum_complete_CQ_upper'),
                         ('fixed_complete_terminal_tester_bound_exact', 'fixed_complete_terminal_tester_upper')]:
        check('outward display ' + upper, F(final[exact]) <= F(final[upper]) < F(final[exact]) + F('1e-12'))
    check('certified numerical targets', F(final['target']) == F(1, 20) and
          quantum + visibility <= F(final['fixed_complete_terminal_tester_upper']) < F(final['target']))
    check('separate calibration and holdout failure budgets', F(final['calibration_coverage_failure_upper']) == F(1, 100) and
          F(final['holdout_simultaneous_failure_upper']) == F(1, 100))
    expected = {'deployment': 'NOT_REJECTED_FROZEN_HOLDOUT', 'changed_intervals': 'NOT_REJECTED_FROZEN_HOLDOUT',
                'detector_violation': 'REJECTED_MODEL_CONTRACT'}
    check('all three corrected holdout families', set(final['corrected_heldout_displays']) == set(expected))
    for name, family in final['corrected_heldout_displays'].items():
        old = heldout['families'][name]
        check(name + ' frozen classifier unchanged', family['status'] == old['status'] == expected[name])
        check(name + ' four complete terminal testers', len(family['settings']) == len(old['settings']) == 4 and
              {row['observable'] for row in family['settings']} == {'XX', 'XY', 'YZ', 'ZZ'})
        rejected = False
        for new, previous in zip(family['settings'], old['settings']):
            check(name + ' observable ordering', new['observable'] == previous['observable'])
            for target, source in [('model_envelope_outward', 'calibration_prediction_envelope'),
                                   ('data_interval_outward', 'empirical_event_intervals')]:
                check(name + ' complete eight event intervals ' + target, len(new[target]) == len(previous[source]) == 8)
                for updated, frozen in zip(new[target], previous[source]):
                    a, b = map(F, updated)
                    x, y = map(F, frozen)
                    check(name + ' outward event interval ' + target,
                          0 <= a <= max(F(0), x - F('1e-12')) <= min(F(1), y + F('1e-12')) <= b <= 1)
            disjoint = [i for i, (p, q) in enumerate(zip(new['model_envelope_outward'], new['data_interval_outward']))
                        if F(p[1]) < F(q[0]) or F(q[1]) < F(p[0])]
            check(name + ' disjoint event decision', new['disjoint_events'] == disjoint)
            rejected |= bool(disjoint)
        check(name + ' corrected classifier readback', rejected == (family['status'] == 'REJECTED_MODEL_CONTRACT'))
    check('all original decisions retained', final['all_original_decisions_unchanged'] is True)
    check('certificate scope not upgraded', final['source_certificate_status'] == 'CERTIFIED_CONDITIONAL_SYNTHETIC_SOURCE' and
          final['hardware_status'] == 'NOT_CERTIFIED' and final['method_gain'] == 'EQUIVALENT_NO_ADDED_GAIN')


def verify_visual(root, visual, check):
    book = root / 'physics/qm/book'
    pub = book / 'evidence/v3.11'
    check('visual review declared scope', visual['edition'] == '3.11' and visual['status'] == 'PASS_SCOPED' and
          visual['independent_human_peer_review'] is False and bool(visual['scope']))
    for lang, suffix in [('zh', ''), ('en', '.en')]:
        row = visual['languages'][lang]
        for key, expected in [('source', book / f'UEOT_PHYSICS{suffix}.md'),
                              ('pdf', book / f'UEOT_PHYSICS{suffix}.pdf'), ('build', pub / lang / 'pdf-build.json')]:
            path = verify_identity(root, row[key], check)
            check(lang + ' visual role ' + key, path == expected)
        check(lang + ' visual physical pages valid', type(row['page_count']) is int and row['page_count'] > 0 and
              bool(row['physical_pages']) and all(type(p) is int and 1 <= p <= row['page_count'] for p in row['physical_pages']))
        check(lang + ' required visual pages actually covered', bool(row['required_pages']) and
              set(row['required_pages']) <= set(row['physical_pages']))
        check(lang + ' actual review reports supplied', bool(row['review_reports']))
        for report in row['review_reports']:
            verify_identity(root, report, check)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo-root', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--require-complete', action='store_true',
                   help='Compatibility flag; this gate always requires complete evidence.')
    args = p.parse_args()
    root = args.repo_root.resolve()
    book = root / 'physics/qm/book'
    pub = book / 'evidence/v3.11'
    prior = pub / 'prior'
    ev = root / 'physics/qm/kernel/evidence/v31.14'
    checks = []

    def read(path):
        return json.loads(path.read_text())

    def check(name, value):
        if not value:
            raise AssertionError(name)
        checks.append(name)

    def identity(row):
        return verify_identity(root, row, check)

    def blocks(text):
        ms = list(re.finditer(r'(?m)^<a id="(ch-\d+|appendix-[a-z])"></a>', text))
        return {m.group(1): text[m.start():ms[i+1].start() if i+1<len(ms) else len(text)] for i,m in enumerate(ms)}

    try:
        sys.path.insert(0, str(book / 'build'))
        from verify_book import inspect_book
        texts = {lang: (book / f'UEOT_PHYSICS{suffix}.md').read_text()
                 for lang, suffix in [('zh', ''), ('en', '.en')]}
        structure = {lang: inspect_book(text) for lang, text in texts.items()}
        for lang, data in structure.items():
            check(lang+' complete book', data['chapters']==71 and data['appendices']==6 and data['numbered_results']==203)
            check(lang+' exact new ID set', {x['id'] for x in data['claims'] if x['chapter']==70} == NEW_IDS)
        check('bilingual IDs and chapters', [(x['id'],x['chapter']) for x in structure['zh']['claims']]
              == [(x['id'],x['chapter']) for x in structure['en']['claims']])
        current_blocks = {lang: blocks(text) for lang,text in texts.items()}
        for lang,suffix in [('zh',''),('en','.en')]:
            old = blocks((prior / f'UEOT_PHYSICS{suffix}.md').read_text())
            for i in range(70):
                if i in (0,48):
                    continue  # the exact current-state/navigation edits are reviewed separately
                check(f'{lang} chapter {i} scientific body preserved', old[f'ch-{i}'].strip() == current_blocks[lang][f'ch-{i}'].strip())
        navigation = read(pub/'navigation-edit-review.json')
        check('actual navigation and appendix review', navigation['status'] == 'PASS_SCOPED')
        for lang, suffix in [('zh', ''), ('en', '.en')]:
            row = navigation['languages'][lang]
            check(lang + ' navigation prior source role', identity(row['prior_source']) == prior/f'UEOT_PHYSICS{suffix}.md')
            check(lang + ' navigation current source role', identity(row['current_source']) == book/f'UEOT_PHYSICS{suffix}.md')
            old = blocks((prior/f'UEOT_PHYSICS{suffix}.md').read_text())
            candidates = {'ch-0', 'ch-48'} | {key for key in old if key.startswith('appendix-')}
            changed = {key for key in candidates if old[key].strip() != current_blocks[lang][key].strip()}
            check(lang + ' navigation complete actual changed blocks', len(row['edits']) == len(changed) and
                  {edit['anchor'] for edit in row['edits']} == changed)
            for edit in row['edits']:
                anchor = edit['anchor']
                check(lang + ' reviewed navigation block ' + anchor,
                      edit['prior_body_sha256'] == hashlib.sha256(old[anchor].encode()).hexdigest() and
                      edit['current_body_sha256'] == hashlib.sha256(current_blocks[lang][anchor].encode()).hexdigest() and
                      isinstance(edit['allowed_changes'], str) and bool(edit['allowed_changes'].strip()))
            check(lang + ' historical fenced code preservation reviewed', row['historical_fenced_code_preserved'] is True)
        display = {lang: re.findall(r'(?ms)^\$\$\s*\n(.*?)^\$\$\s*$', b['ch-70']) for lang,b in current_blocks.items()}
        check('new bilingual display mathematics exact', display['zh'] == display['en'] and len(display['zh'])>10)
        section_ids = {lang: re.findall(r'^## (70\.\d+)\b', b['ch-70'],re.M) for lang,b in current_blocks.items()}
        check('new bilingual numbered sections', section_ids['zh']==section_ids['en'])
        check('shared source unchanged', sha(root/'physics/qm/persistent_bath/SHARED_MODEL.json') == SHARED_SHA)
        snapshots = read(prior/'SNAPSHOT.json')
        for row in snapshots['files']:
            check('prior snapshot '+row['origin_path'], sha(root/row['snapshot_path']) == row['sha256'])

        dossier = read(book/'CHAPTER_DOSSIER.json')
        old_dossier = read(prior/'CHAPTER_DOSSIER.json')
        check('historical author retained', dossier['author'] == old_dossier['author'] == '钱德桂（Degui Qian）')
        old_rows = [r for ch in old_dossier['chapters'] for r in ch['numbered_results']]
        rows = [r for ch in dossier['chapters'] for r in ch['numbered_results']]
        check('all194 historical result objects exact', len(old_rows)==194 and rows[:194]==old_rows)
        check('new result object count', len(rows)==203 and {r['id'] for r in rows[194:]}==NEW_IDS)
        check('no new Lean claim', all('NO_NEW_LEAN' in r['machine_status'] for r in rows[194:]))
        for ch in dossier['chapters'] + dossier['appendices']:
            for lang in ('zh','en'):
                b = current_blocks[lang][ch['anchor']].encode()
                pin = ch['publication_3_11'][lang]
                check(lang+' body '+ch['anchor'], hashlib.sha256(b).hexdigest()==pin['body_sha256'] and len(b)==pin['body_utf8_bytes'])
        ledger = read(root/'physics/qm/status/CLAIM_LEDGER_v31.14.json')
        old_ledger = read(prior/'CLAIM_LEDGER_v31.13.json')
        check('all117 historical claim objects exact', len(old_ledger['claims'])==117 and ledger['claims'][:117]==old_ledger['claims'])
        check('126 claims', len(ledger['claims'])==ledger['claim_count']==126)
        manifest = read(book/'SOURCE_MANIFEST.json')
        old_manifest = read(prior/'SOURCE_MANIFEST.json')
        check('historical source entries exact', manifest['entries'][:-1]==old_manifest['entries'])

        current = read(root/'physics/qm/status/CURRENT.json')
        check('current edition and counts', current['version']=='v31.14' and current['book']['edition']=='3.11'
              and current['book']['numbered_results']==203)
        check('device status not upgraded', not current['new_hardware_data']
              and 'NOT_CERTIFIED' in current['status_axes']['empirical'])
        identity(current['book']['dossier'])
        identity(dossier['book_source_manifest'])
        expected_reuse = 'physics/qm/kernel/evidence/v31.14/proof-reuse.json'
        expected_runtime = 'physics/qm/kernel/evidence/v31.14/runtime/execution_receipt.json'
        proof = current['source_identity']
        old_proof = read(prior/'CURRENT.json')['source_identity']
        check('historical Lean execution identity retained', all(proof[k] == old_proof[k]
              for k in ('manifest', 'verification', 'source_count', 'source_set_sha256')))
        check('explicit no Chapter69 or Chapter70 new Lean scope',
              'no new Chapter69 or Chapter70 Lean coverage' in proof['scope'])
        check('current proof reuse binding', proof['current_identity_check'] == current['proof_reuse_receipt'] == expected_reuse)
        for owner, obj in [('manifest', manifest), ('dossier', dossier)]:
            check(owner + ' current proof aliases', obj['unified_source_identity'] == obj['publication_source_identity'] == proof)
            check(owner + ' current publication scope', obj['edition'] == obj['publication_revision']['edition'] == '3.11')
            identity(obj['runtime_source_identity']['receipt'])
            identity(obj['increment_source_identity'])
            check(owner + ' current runtime alias', obj['runtime_source_identity']['receipt']['path'] == expected_runtime)
            canonical_keys = ('canonical_identity', 'canonical_english_identity') if owner == 'manifest' else ('canonical', 'canonical_english')
            for key, suffix, lang in [(canonical_keys[0], '', 'zh'), (canonical_keys[1], '.en', 'en')]:
                row = obj[key]
                identity(row)
                check(owner + ' canonical scope ' + lang, row['language'] == lang and row['chapters'] == 71 and
                      row['appendices'] == 6 and row['numbered_results'] == 203 and
                      row['path'] == f'physics/qm/book/UEOT_PHYSICS{suffix}.md')
        partition = manifest['scientific_execution_partition']
        check('current scientific execution partition', partition['new_runtime'] == expected_runtime and
              partition['historical_reuse'] == expected_reuse and partition['new_device_data'] is False and
              partition['new_synthetic_shots_this_replay'] == 0)
        check('metadata followup is not scientific rerun', manifest['remote_metadata_completion']['metadata_followup_is_not_a_new_scientific_execution'] is True)
        check('current release receipt scope', 'Book3.11' in manifest['local_release_receipt_scope'])
        check('current publication code inventory alias', manifest['current_publication_code_manifest'] ==
              manifest['current_increment_code_manifest'] == '../kernel/evidence/v31.14/source-manifest.json')
        check('current dossier inventory', dossier['verified_inventory']['proof_reuse']['path'] == expected_reuse and
              dossier['verified_inventory']['new_runtime']['path'] == expected_runtime)
        reuse = read(ev/'proof-reuse.json')
        check('current proof reuse eligible without new Lean', reuse['proof_reuse_eligible'] is True and reuse['errors'] == [] and
              reuse['proof_input_count'] == 158 and reuse['proof_source_set_sha256'] == PROOF_SET_SHA and
              reuse['new_lean_execution'] is False and reuse['new_lean_theorems'] == 0)
        executed_inputs = read(repository_path(root, proof['manifest']))
        check('158 historical executed inputs', len(executed_inputs['sources']) == executed_inputs['source_count'] == 158)
        check('historical source set identity', hashlib.sha256(json.dumps(executed_inputs['sources'], sort_keys=True,
              separators=(',', ':')).encode()).hexdigest() == executed_inputs['source_set_sha256'] == PROOF_SET_SHA)
        for row in executed_inputs['sources']:
            identity(row)
        runtime = read(ev/'runtime/execution_receipt.json')
        verify_runtime(root, runtime, check)
        final_path = ev/'runtime/work_c/FINAL_CERTIFICATE.json'
        final = read(final_path)
        nominal = read(ev/'runtime/work_c/NOMINAL_MODEL.json')
        heldout = read(ev/'runtime/work_c/HOLDOUT_RESULTS.json')
        verify_final_bounds(final, nominal, heldout, check)
        for field, filename in [('nominal_sha256_unchanged', 'NOMINAL_MODEL.json'),
                                ('heldout_results_sha256_unchanged', 'HOLDOUT_RESULTS.json'),
                                ('calibration_shots_sha256', 'calibration_shots.npz'),
                                ('holdout_shots_sha256', 'holdout_shots.npz'),
                                ('generator_probability_check_sha256', 'GENERATOR_PROBABILITY_CHECK.json')]:
            check('final certificate source ' + field, final[field] == sha(ev/'runtime/work_c'/filename))
        check('four exact physical predictor bindings', len(final['exact_repaired_prediction_certificate_bindings']) == 4)
        for filename, digest in final['exact_repaired_prediction_certificate_bindings'].items():
            check('physical prediction certificate ' + filename, digest == sha(ev/'runtime/work_b'/filename))
        for key in ('source_certificate_status', 'quantum_complete_CQ_upper', 'fixed_complete_terminal_tester_upper', 'method_gain', 'hardware_status'):
            check('runtime scientific summary ' + key, runtime['scientific_outputs'][key] == final[key])
        for lang in ('zh', 'en'):
            chapter = current_blocks[lang]['ch-70']
            for key in ('quantum_complete_CQ_upper', 'fixed_complete_terminal_tester_upper'):
                check(lang + ' published outward bound ' + key,
                      re.search(r'(?<![\d.])' + re.escape(final[key]) + r'(?!\d)', chapter) is not None)
        for row in rows[194:]:
            for evidence in row['proof_and_evidence']:
                check(row['id'] + ' evidence ' + evidence['path'], sha(repository_path(root, evidence['path'])) == evidence['sha256'])
        published_robust = next(row for row in rows[194:] if row['id'] == 'P-ROB-07')
        displayed = {Fraction(token) for token in re.findall(r'(?<![\d.])(?:0)?\.\d+', published_robust['question_and_quantifiers'])}
        check('robust result metadata uses final upward bounds',
              all(Fraction(final[key]) in displayed for key in ('quantum_complete_CQ_upper', 'fixed_complete_terminal_tester_upper')))
        source_manifest = read(ev/'source-manifest.json')
        source_paths = [row['path'] for row in source_manifest['files']]
        forbidden = {repository_path(root, name) for name in MUTABLE_METADATA} | {
            ev/'source-manifest.json', args.output.resolve()}
        check('source inventory has unique entries', len(source_paths) == len(set(source_paths)))
        for row in source_manifest['files']:
            check('source inventory has no mutable or self dependency ' + row['path'], repository_path(root, row['path']) not in forbidden)
            identity(row)
        check('navigation review in current evidence inventory', 'physics/qm/book/evidence/v3.11/navigation-edit-review.json' in source_paths)
        acceptance = read(pub/'local-acceptance.json')
        check('publication accepted in actual scope', acceptance['status']=='PASS_SCOPED' and not acceptance['new_hardware_data'])
        artifact_paths = [row['path'] for row in acceptance['current_artifacts']]
        check('six current bilingual publication artifacts', REQUIRED_ARTIFACTS <= set(artifact_paths))
        check('unique publication artifacts', len(artifact_paths) == len(set(artifact_paths)))
        for row in acceptance['current_artifacts']:
            check('acceptance has no mutable or self dependency ' + row['path'], repository_path(root, row['path']) not in
                  forbidden | {pub/'local-acceptance.json'})
            identity(row)
        check('acceptance visual role', identity(acceptance['visual_review']) == pub/'visual-review.json')
        visual = read(pub/'visual-review.json')
        verify_visual(root, visual, check)
        for lang,suffix in [('zh',''),('en','.en')]:
            build = read(pub/lang/'pdf-build.json')
            check(lang+' source build bound', build['source_sha256']==sha(book/f'UEOT_PHYSICS{suffix}.md'))
            check(lang+' TeX build bound', build['tex_sha256']==sha(book/f'UEOT_PHYSICS{suffix}.tex'))
            check(lang+' PDF build bound', build['pdf_sha256']==sha(book/f'UEOT_PHYSICS{suffix}.pdf'))
            build_language = {'zh': 'zh-CN', 'en': 'en'}[lang]
            check(lang+' build edition and inventory', build['edition']=='3.11' and build['language']==build_language and
                  build['chapters']==71 and build['appendices']==6)
            for field, path in [('builder_sha256', book/'build/build_pdf.py'),
                                ('header_sha256', book/f'build/header{suffix}.tex'),
                                ('tables_filter_sha256', book/'build/tables.lua')]:
                check(lang+' current build dependency '+field, build[field] == sha(path))
            check(lang+' no layout warnings', not build['layout_warnings'])
        result = {'schema':'ueot-physics-edition3.11-verification/1','status':'PASS',
                  'created_at_utc':datetime.now(timezone.utc).isoformat(),'check_count':len(checks),'checks':checks,
                  'chapters':71,'results':203,'prior_results_exact':194,'prior_claims_exact':117,
                  'new_lean':False,'new_hardware_data':False,
                  'scope':'Source identities, preservation and actual declared evidence; not a substitute for the paper proofs or device validation'}
        code = 0
    except Exception as error:
        result = {'schema':'ueot-physics-edition3.11-verification/1','status':'FAIL',
                  'created_at_utc':datetime.now(timezone.utc).isoformat(),'checks_completed':checks,
                  'error':str(error)}
        code = 1
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','check_count','error') if k in result}))
    raise SystemExit(code)


if __name__ == '__main__':
    main()
