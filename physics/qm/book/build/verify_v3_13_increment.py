#!/usr/bin/env python3
"""Verify Edition 3.13 (Chapter 72 / v31.16) manuscripts, metadata, preservation, and optional print artifacts."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

from verify_book import inspect_book

ROOT = Path(__file__).resolve().parents[4]
QM = Path('physics/qm')
BOOK = QM / 'book'
PRIOR_BOOK_COMMIT = 'cc5670d5f2ac96f88270c0f38ae6fb6f77e26093'
RESEARCH_BASELINE = 'a93209c58eef71b0eac489758bd46e38b975848a'

# Sealed during Stage B once CI builds and visual inspection succeed:
PRINT_SOURCE = 'c4d0a7b474bfc98a72e41d399510c87fc0217e77'
PRINT_RUN = 45320237937
PR_NUMBER = 492

PRINT_EVIDENCE = BOOK / 'evidence/v3.13'
IDS = [
    'C-QSEL-05',
    'C-LR-CONE-01',
    'C-GPT-RECON-02',
    'C-MATH42-BRIDGE-01',
    'P-HORIZON-CLOCK-01',
    'P-ADM-ALLHARM-02',
    'P-FLAT-DIRAC-03',
    'P-DISCRETE-QG-01',
    'P-LORENTZ-QG-07',
    'P-CHIRAL-CLOCK-02',
    'P-NONABELIAN-CHIRAL-08',
    'C-CORE-CONST-01',
    'P-GUT-DESERT-02',
    'P-UNIMODULAR-LAMBDA-09',
    'P-MESO-BMV-06',
    'P-PHIL31-OMEGA-01',
    'P-PHIL31-REALIZ-02',
    'P-PHIL31-LAKATOS-03',
    'C-UNIFIED-SYNTH-10',
]

FROZEN_FROM_BASELINE = [
    'physics/qm/status/CURRENT.json',
    'physics/qm/README.md',
    'physics/qm/ROADMAP.md',
    'physics/qm/status/CLAIM_LEDGER_v31.15.json',
    '.github/workflows/ueot-physics-source-response.yml',
    'physics/qm/kernel/evidence/v31.14/source-manifest.json',
    'physics/qm/kernel/evidence/v31.11/source-manifest.json',
]

ALLOWED_CH72_PREFIXES = (
    '../null_source/',
    '../../unification/',
    '../../../formalization/ueot-physics-unification/',
    '../../../validation/physics_unification/',
    '../../interfaces/',
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read_json(rel_path):
    return json.loads((ROOT / rel_path).read_text(encoding='utf-8'))


def git_show(commit, rel_path):
    return subprocess.check_output(['git', 'show', f'{commit}:{rel_path}'], cwd=ROOT)


def check_identity(record):
    path = Path(record['path'])
    require(not path.is_absolute() and '..' not in path.parts, f'Invalid source path {path}')
    blob = (ROOT / path).read_bytes()
    require(len(blob) == record['bytes'] and hashlib.sha256(blob).hexdigest() == record['sha256'],
            f'Source identity changed at {path}')


def blocks(text):
    anchors = list(re.finditer(r'^<a id="(ch-\d+|appendix-[a-f])"></a>', text, re.M))
    return {
        m[1]: text[m.start(): anchors[i + 1].start() if i + 1 < len(anchors) else len(text)]
        for i, m in enumerate(anchors)
    }


def check_print_build(lang, suffix):
    receipt = read_json(PRINT_EVIDENCE / f'{lang}-build.json')
    stem = 'UEOT_PHYSICS' + suffix
    source = BOOK / (stem + '.md')
    require(receipt['edition'] == '3.13' and receipt['language'] == ('zh-CN' if lang == 'zh' else 'en')
            and receipt['source_name'] == source.name and receipt['chapters'] == 73 and receipt['appendices'] == 6,
            lang + ' build edition or language mismatch')
    paths = {
        'source': source,
        'tex': BOOK / (stem + '.tex'),
        'pdf': BOOK / (stem + '.pdf'),
        'header': BOOK / f'build/header{suffix}.tex',
        'builder': BOOK / 'build/build_pdf.py',
        'tables_filter': BOOK / 'build/tables.lua',
    }
    for name, path in paths.items():
        digest = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        require(digest == receipt[name + '_sha256'], f'{lang} build hash mismatch: {path}')
        if name not in ('tex', 'pdf'):
            built = git_show(PRINT_SOURCE, str(path))
            require(hashlib.sha256(built).hexdigest() == digest, f'{path} differs from CI build source {PRINT_SOURCE}')
    passes = receipt['compile_passes']
    require(len(passes) == 3 and all(row['exit_code'] == 0 for row in passes)
            and receipt['last_two_auxiliary_files_identical'] is True
            and passes[-1]['auxiliary_sha256'] == passes[-2]['auxiliary_sha256']
            and not receipt['layout_warnings'] and not receipt['rerun_warnings'],
            lang + ' incomplete print build')
    return receipt


def verify_print(current, manifest, dossier):
    require(bool(PRINT_SOURCE) and PRINT_RUN > 0 and PR_NUMBER > 0, 'Stage B print metadata not sealed yet')
    revision = manifest['publication_revision']
    printed = dossier['derivatives']
    review_path = PRINT_EVIDENCE / 'reading-review.json'
    review = read_json(review_path)
    require(current['verification_state'] == 'PASS_SCOPED' and current['book']['status'] == 'PASS_SCOPED'
            and current['physical_unification'] == 'OPEN' and current['device_certified'] is False
            and current['integration']['pr'] == PR_NUMBER
            and manifest['current_remote_code_identity'] == dossier['current_remote_code_identity'] == current['integration'],
            'Incorrect Stage B current/PR scope')
    require(revision == dossier['publication_revision'] and revision['print_source_commit'] == PRINT_SOURCE
            and revision['local_artifact_state'] == printed['status'] == current['book']['pdf_acceptance'] == 'PASS_SCOPED'
            and current['book']['checked_in_pdf_edition'] == printed['checked_in_edition'] == review['edition'] == '3.13',
            'Wrong print edition or acceptance scope')
    require(printed['previous_edition_commit'] == PRIOR_BOOK_COMMIT
            and printed['previous_edition_artifacts'] == json.loads(git_show(PRIOR_BOOK_COMMIT, str(BOOK / 'CHAPTER_DOSSIER.json')))['derivatives'],
            'Historical 3.12 print metadata mismatch')
    binding = printed['visual_review']
    require(binding['path'] == str(review_path) and binding == revision['visual_review']
            and binding == current['book']['visual_review'], 'Wrong visual review binding')
    check_identity(binding)
    require(review['source_commit'] == PRINT_SOURCE and review['pr'] == PR_NUMBER
            and review['build_run_id'] == revision['build_run_id'] == PRINT_RUN and review['status'] == 'PASS_SCOPED'
            and bool(review['scope'].strip()) and review['independent_human_peer_review'] is False
            and set(review['languages']) == {'zh', 'en'}, 'Invalid review scope or build identity')
    for lang, suffix in [('zh', ''), ('en', '.en')]:
        receipt = check_print_build(lang, suffix)
        row = review['languages'][lang]
        pin = printed[lang]
        stem = 'UEOT_PHYSICS' + suffix
        for key, path in [('pdf', BOOK / (stem + '.pdf')), ('tex', BOOK / (stem + '.tex')),
                          ('build', PRINT_EVIDENCE / f'{lang}-build.json')]:
            artifact = pin['latex' if key == 'tex' else key]
            require(artifact['path'] == str(path) and artifact['sha256'] == row[key + '_sha256'],
                    f'{lang} review refers to a different {key}')
            check_identity(artifact)
        require(pin['source_sha256'] == receipt['source_sha256'], lang + ' printed manuscript identity')
        pdf = ROOT / pin['pdf']['path']
        info = subprocess.check_output(['pdfinfo', str(pdf)], text=True)
        page_count = int(re.search(r'^Pages:\s+(\d+)$', info, re.M)[1])
        pages = row['reviewed_pages']
        require(row['page_count'] == page_count and pages and all(type(n) is int and 1 <= n <= page_count for n in pages)
                and len(pages) == len(set(pages)) and row['observations'].strip(), lang + ' visual review pages')

        listing = subprocess.check_output(['pdfinfo', '-dests', str(pdf)], text=True)
        dest = {name: int(page) for page, name in re.findall(r'(?m)^\s*(\d+)\s+\[[^\n]*\]\s+"([^"]+)"', listing)}
        headings = sorted((int(name.split('.')[-1]), page) for name, page in dest.items()
                          if re.fullmatch(r'chapter\*\.\d+', name))
        anchors = [f'ch-{n}' for n in range(73)] + [f'appendix-{c}' for c in 'abcdef']
        require(len(headings) == 80 and [dest[a] for a in anchors] == [page for _, page in headings[1:]]
                and row['destinations_matching_bookmarks'] == len(anchors), lang + ' stable destination pages')
        first, last = dest['ch-72'], dest['appendix-a'] - 1
        require(row['chapter_72_pdf_pages'] == [first, last] and first <= last and set(range(first, last + 1)) <= set(pages),
                lang + ' Chapter 72 review coverage')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manuscript-only', action='store_true', help='Skip Stage B sealed PDF/build/review checks')
    args = ap.parse_args()

    # 1. Verify frozen baseline files untouched
    for rel_path in FROZEN_FROM_BASELINE:
        require((ROOT / rel_path).read_bytes() == git_show(RESEARCH_BASELINE, rel_path),
                f'Frozen file modified: {rel_path}')

    # 2. Verify metadata, ledger, manifest, and dossier bindings
    dossier_path = BOOK / 'CHAPTER_DOSSIER.json'
    manifest_path = BOOK / 'SOURCE_MANIFEST.json'
    prev_ledger_rel = QM / 'status/CLAIM_LEDGER_v31.15.json'
    ledger_rel = QM / 'status/CLAIM_LEDGER_v31.16.json'
    current_rel = Path('physics/status/CURRENT_v31.16.json')

    current = read_json(current_rel)
    dossier = read_json(dossier_path)
    manifest = read_json(manifest_path)
    old_dossier = json.loads(git_show(PRIOR_BOOK_COMMIT, str(dossier_path)))
    old_manifest = json.loads(git_show(PRIOR_BOOK_COMMIT, str(manifest_path)))
    old_qm_current = read_json(QM / 'status/CURRENT.json')

    require(current['frozen_qm_current']['sha256'] == hashlib.sha256((ROOT / QM / 'status/CURRENT.json').read_bytes()).hexdigest(),
            'Frozen QM current digest mismatch')
    require(dossier['publication_source_identity'] == manifest['publication_source_identity'] == old_qm_current['source_identity'],
            'Historical proof identity changed')
    require(manifest['entries'][:-1] == old_manifest['entries'] and manifest['entries'][-1]['id'] == 'QM3116',
            'Source manifest registry mismatch')
    require(dossier['author'] == old_dossier['author'], 'Historical author changed')
    require(current['book']['dossier']['path'] == str(dossier_path)
            and current['book']['source_manifest']['path'] == str(manifest_path)
            and dossier['book_source_manifest']['path'] == str(manifest_path),
            'Metadata path mismatch')
    check_identity(current['book']['dossier'])
    check_identity(current['book']['source_manifest'])
    check_identity(dossier['book_source_manifest'])

    require(current['physical_unification'] == 'OPEN' and current['device_certified'] is False
            and current['new_hardware_data'] is False, 'Honest frontier flags violated in CURRENT_v31.16.json')

    old_rows = [r for ch in old_dossier['chapters'] for r in ch['numbered_results']]
    rows = [r for ch in dossier['chapters'] for r in ch['numbered_results']]
    require(len(old_rows) == 210 and rows[:210] == old_rows and [r['id'] for r in rows[210:]] == IDS,
            'Historical or new result objects mismatch')

    ledger = read_json(ledger_rel)
    prev_ledger = read_json(prev_ledger_rel)
    require(ledger['claims'][:133] == prev_ledger['claims'] and len(ledger['claims']) == ledger['claim_count'] == 152,
            'Claim ledger prefix or count mismatch')
    require(ledger['new_lean'] is True and ledger['new_hardware_data'] is False
            and ledger['physical_unification'] == 'OPEN' and ledger['device_certified'] is False,
            'Honest flags violated in CLAIM_LEDGER_v31.16.json')
    for r, claim in zip(rows[210:], ledger['claims'][133:]):
        require(claim['id'] == 'QMK-' + r['id'] and claim['book_result'] == r['id']
                and claim['verification_scope'] == r['question_and_quantifiers']
                and claim['premises'] == r['premises'] and claim['proof_and_evidence'] == r['proof_and_evidence']
                and r['premises'] and r['new_lean'] is True and r['new_hardware_data'] is False,
                'Incorrect claim scope for ' + r['id'])
        require(len(r['proof_and_evidence']) >= 2, 'Missing result evidence for ' + r['id'])
        for item in r['proof_and_evidence']:
            check_identity(item)

    # 3. Verify manuscripts, byte-identical unchanged chapters, publication_3_13 hashes, and Ch. 72 parity
    chapters = {}
    for lang, suffix in [('zh', ''), ('en', '.en')]:
        path = BOOK / f'UEOT_PHYSICS{suffix}.md'
        text = (ROOT / path).read_text(encoding='utf-8')
        require('/Users/' not in text and '/private/tmp/' not in text, lang + ' local host path leak')
        source = inspect_book(text)
        require((source['chapters'], source['appendices'], source['numbered_results']) == (73, 6, 229), lang + ' structure')
        old_text = git_show(PRIOR_BOOK_COMMIT, str(path)).decode('utf-8')
        require(source['claims'][:210] == inspect_book(old_text)['claims'], lang + ' inherited titles and anchors')
        for r, parsed in zip(rows[210:], source['claims'][210:]):
            require((parsed['id'], parsed['chapter'], parsed['title']) == (r['id'], 72, r['title' if lang == 'zh' else 'title_en']),
                    lang + ' result binding ' + r['id'])
        current_blocks = blocks(text)
        for name, body in blocks(old_text).items():
            if name not in {'ch-0', 'ch-48', 'appendix-b', 'appendix-c', 'appendix-e', 'appendix-f'}:
                require(current_blocks[name] == body, lang + ' prior body changed at ' + name)
        for ch in dossier['chapters'] + dossier['appendices']:
            body = current_blocks[ch['anchor']].encode('utf-8')
            pin = ch['publication_3_13'][lang]
            require(pin['body_sha256'] == hashlib.sha256(body).hexdigest() and pin['body_utf8_bytes'] == len(body),
                    lang + ' publication_3_13 body mismatch at ' + ch['anchor'])
        for obj, key in [(dossier, 'canonical'), (manifest, 'canonical_identity')]:
            if lang == 'en':
                key = 'canonical_english' if obj is dossier else 'canonical_english_identity'
            require(obj[key]['path'] == str(path), lang + ' canonical path')
            check_identity(obj[key])
        chapter = chapters[lang] = current_blocks['ch-72']
        for value in ('2048/9375', '7/12', '0.153021391482', '2.829147', '3.197065', '0.467832', '0.467833', '83'):
            require(value in chapter, f'{lang} ch-72 missing key value {value}')
        for target in re.findall(r'\]\((?!https?://|#)([^ )]+)\)', chapter):
            require(target.startswith(ALLOWED_CH72_PREFIXES) and (ROOT / BOOK / target).is_file(),
                    f'{lang} invalid ch-72 link target: {target}')

    for pattern in (r'(?ms)^\$\$\n(.*?)\n\$\$', r'(?m)^## (72\.\d+)', r'\]\((?!https?://|#)([^ )]+)\)'):
        zh_items, en_items = [re.findall(pattern, chapters[k]) for k in ('zh', 'en')]
        require(zh_items and zh_items == en_items, f'Bilingual formula, section, or link mismatch for {pattern}')

    # 4. Stage B print & review verification unless --manuscript-only
    if not args.manuscript_only:
        verify_print(current, manifest, dossier)
        print(f'PASS Edition 3.13 / v31.16 complete candidate (Stage B): 229 results, 152 claims, PDF/TeX/visual review sealed for PR #{PR_NUMBER}.')
    else:
        print('PASS Edition 3.13 / v31.16 manuscript & preservation gate (--manuscript-only): 73 chapters, 6 appendices, 229 results, 152 claims.')


if __name__ == '__main__':
    main()
