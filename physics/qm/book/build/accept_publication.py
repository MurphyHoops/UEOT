#!/usr/bin/env python3
"""Bind edition 3.7's actual artifacts to scoped reviews and executed receipts.

This collects publication gates. It neither executes the physics kernel nor
converts an internal scientific review into experimental or external acceptance.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

BOOK = Path(__file__).resolve().parents[1]
REPO = BOOK.parents[2]
EVIDENCE = BOOK / 'evidence/v3.7'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(name):
    return json.loads((EVIDENCE / name).read_text())


def result_objects(dossier):
    return [r for ch in dossier['chapters'] for r in ch['numbered_results']]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    sources = {lang: sha(BOOK / ('UEOT_PHYSICS' + ('.en' if lang == 'en' else '') + '.md'))
               for lang in ('zh', 'en')}
    artifacts = {}
    for lang in ('zh', 'en'):
        stem = 'UEOT_PHYSICS' + ('.en' if lang == 'en' else '')
        for ext in ('md', 'tex', 'pdf'):
            p = BOOK / (stem + '.' + ext)
            artifacts[p.name] = {'sha256': sha(p), 'bytes': p.stat().st_size}
        structure = read('book-structure.' + lang + '.json')
        assert structure['status'] == 'PASS' and structure['source_sha256'] == sources[lang]
        assert (structure['chapters'], structure['appendices'], structure['numbered_results']) == (67, 6, 173)
        build = read('pdf-' + lang + '/pdf-build.json')
        assert build['source_sha256'] == sources[lang]
        assert build['tex_sha256'] == artifacts[stem + '.tex']['sha256']
        assert build['pdf_sha256'] == artifacts[stem + '.pdf']['sha256']
        assert build['builder_sha256'] == sha(BOOK / 'build/build_pdf.py')
        assert build['tables_filter_sha256'] == sha(BOOK / 'build/tables.lua')
        assert build['header_sha256'] == sha(BOOK / ('build/header.en.tex' if lang == 'en' else 'build/header.tex'))
        assert not build['layout_warnings'] and not build['rerun_warnings']
        assert build['last_two_auxiliary_files_identical']
        for log in build['compile_passes']:
            assert log['exit_code'] == 0 and log['sha256'] == sha(EVIDENCE / ('pdf-' + lang) / log['file'])

    fidelity = read('bilingual-fidelity.json')
    assert fidelity['status'] == 'PASS' and fidelity['source_sha256'] == sources
    assert fidelity['stable_result_count'] == 173 and not fidelity['numbering_migrations']
    inline = read('inline_math_fidelity.json')
    assert inline['status'] == 'PASS'
    # The theory closure explicitly binds the independently read manuscripts.
    theory = read('theory_review_closure.json')
    assert theory['status'] == 'PASS'
    assert {Path(f['path']).name: f['sha256'] for f in theory['files']} == {
        'UEOT_PHYSICS.md': sources['zh'], 'UEOT_PHYSICS.en.md': sources['en']}
    empirical = read('PUBLICATION_3_7_EMPIRICAL_CLOSEOUT.json')
    assert empirical['status'] == 'PASS_SOURCE_INCREMENT'
    assert {k: v['sha256'] for k, v in empirical['accepted_sources'].items()} == sources
    editorial = read('EDITORIAL_REVIEW_CLOSEOUT_3_7.json')
    assert editorial['review_status'] == 'PASS_WITH_RECORDED_REPAIRS'
    assert editorial['manuscript_sha256'] == sources
    visual = read('pdf-visual-review.json')
    technical = read('pdf-technical-check.json')
    assert visual['status'] == 'PASS_WITH_STATED_SCOPE' and technical['status'] == 'PASS'
    for lang in ('zh', 'en'):
        stem = 'UEOT_PHYSICS' + ('.en' if lang == 'en' else '')
        assert visual['editions'][lang]['source_sha256'] == sources[lang]
        assert visual['editions'][lang]['pdf_sha256'] == artifacts[stem + '.pdf']['sha256']
        assert technical['editions'][lang]['pdf_sha256'] == artifacts[stem + '.pdf']['sha256']
        assert technical['editions'][lang]['all_fonts_embedded']
    for report in visual['reviewer_reports']:
        assert sha(BOOK / report['path']) == report['sha256']

    manifest = json.loads((BOOK / 'SOURCE_MANIFEST.json').read_text())
    dossier = json.loads((BOOK / 'CHAPTER_DOSSIER.json').read_text())
    assert str(manifest['edition']) == str(dossier['edition']) == '3.7'
    assert manifest['entries'] == read('source-manifest-prior-v3.6.json')['entries']
    assert len(manifest['entries']) == 12
    assert result_objects(dossier) == result_objects(read('dossier-prior-v3.6.json'))
    assert len(result_objects(dossier)) == 173
    assert dossier['source_catalog'] == read('dossier-prior-v3.6.json')['source_catalog']
    reuse = read('source-reuse.json')
    assert reuse['status'] == 'PASS' and reuse['distinct_input_count'] == 164
    assert reuse['tracked_core_blob_count_unchanged'] == 5033 and not reuse['protected_paths_modified']
    assert not reuse['lean_or_kernel_rerun'] and not reuse['new_hardware_data']
    for name in ('record-example-check.json', 'EMPIRICAL_NUMBER_CHECK.json',
                 'axiom_inventory_v31_10_identity.json'):
        assert read(name)['status'] == 'PASS'
    changed = subprocess.check_output(['git', 'diff', '--name-only', 'HEAD'], cwd=REPO, text=True).splitlines()
    untracked = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], cwd=REPO, text=True).splitlines()
    assert all(p.startswith('physics/qm/book/') for p in changed + untracked)
    receipt_paths = sorted(p for p in EVIDENCE.rglob('*') if p.is_file()
                           and p.resolve() != args.output.resolve()
                           and p.name not in ('remote-delivery.json', 'local-acceptance.json'))
    receipt_paths += [BOOK / 'CHAPTER_DOSSIER.json', BOOK / 'SOURCE_MANIFEST.json',
                     BOOK / 'PHYSICS_RESULT_MAPPING.md', BOOK / 'PUBLICATION_RIGHTS.md']
    receipt_paths += sorted((BOOK / 'review').glob('*.md'))
    report = {
        'schema': 'ueot_physics.local_publication_acceptance.v1',
        'status': 'PASS_WITH_DECLARED_SCIENTIFIC_AND_REVIEW_SCOPE',
        'recorded_at_utc': datetime.now(timezone.utc).isoformat(),
        'edition': '3.7', 'research_release': 'v31.10 / Kernel 1.10',
        'publication_base': '925e3a8a411c0b1bab99dd9150bf005893656140',
        'artifacts': artifacts,
        'gates': {
            'complete_bilingual_body': 'PASS: 67 chapters, six appendices each',
            'stable_results': 'PASS: 173 IDs, no numbering migration',
            'formula_fidelity': 'PASS: literal display/inline audits with individually declared language exceptions',
            'scientific_claims_and_assumptions': 'PASS_WITH_SCOPE: internal theory review; OPEN obligations retained',
            'standard_physics_and_ueot_contribution_separation': 'PASS_WITH_SCOPE: source-resolved claim matrix',
            'empirical_and_falsifiability_review': 'PASS_WITH_SCOPE: real primary sources; no new hardware evidence',
            'numerical_and_source_identity': 'PASS: new narrow checks; 164 exact reused inputs; 5033 Core blobs unchanged',
            'three_assigned_internal_reviews': 'PASS: source-bound closures and documented independent reading scopes',
            'actual_tex_and_pdf_build': 'PASS: three real passes per language; stable auxiliaries; no layout/missing-glyph/reference warnings',
            'actual_visual_inspection': 'PASS_WITH_SCOPE: 579 overview pages and 65 distinct full pages; exact Chinese image transfer',
            'historical_contracts_and_rights': 'PASS: 173 result objects, 12 manifest entries and source catalog preserved; historical lawful grants retained',
            'write_scope': 'PASS: physics/qm/book only',
        },
        'publication_remote_acceptance': 'SEPARATE: see remote-delivery.json after actual GitHub observations',
        'local_heavy_science_reexecuted': False,
        'new_hardware_experiments': False,
        'external_human_peer_review': False,
        'nonblocking_typesetting_note': visual['nonblocking_documentation_erratum'],
        'evidence': [{'path': str(p.relative_to(BOOK)), 'sha256': sha(p), 'bytes': p.stat().st_size}
                     for p in receipt_paths],
        'scope': 'Publication acceptance does not prove a new universal physical theory or erase the stated OPEN mechanisms. This receipt does not claim PR CI or main merge before observing them.',
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'artifacts': len(artifacts),
                      'gates': len(report['gates']), 'bound_evidence_files': len(receipt_paths)}, indent=2))


if __name__ == '__main__':
    main()
