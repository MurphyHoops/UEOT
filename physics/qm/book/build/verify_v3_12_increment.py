#!/usr/bin/env python3
"""Verify the Chapter 71 manuscript against the merged Chapter 70 edition."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import subprocess

from verify_book import inspect_book

ROOT = Path(__file__).resolve().parents[4]
QM = Path('physics/qm')
BOOK = QM / 'book'
SCIENCE = QM / 'correlated_bath'
BASE = 'a3f95dc1a6821978e173e23015f026994fb60c65'
IDS = ['C-QSEL-03', 'C-QSEL-04', 'P-MICRO-10', 'C-QMEM-02', 'P-QMEM-03', 'P-ROB-08', 'P-FIELD-01']
# These edition-specific files deliberately change. The historical gate runs
# in its own checkout and still checks every one of its original identities.
REPLACED = {'.github/workflows/ueot-qm.yml', 'physics/status/CURRENT.md',
            'physics/qm/ROADMAP.md', 'physics/qm/book/README.md',
            'physics/qm/book/PHYSICS_RESULT_MAPPING.md', 'physics/qm/book/build/verify_book.py'}
for suffix in ('', '.en'):
    REPLACED.update({str(BOOK / f'UEOT_PHYSICS{suffix}.md'), str(BOOK / f'build/header{suffix}.tex')})


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads((ROOT / path).read_bytes())


def previous(path):
    return subprocess.check_output(['git', 'show', f'{BASE}:{path}'], cwd=ROOT)


def check_identity(record):
    path = Path(record['path'])
    require(not path.is_absolute() and '..' not in path.parts, f'Invalid source path {path}')
    blob = (ROOT / path).read_bytes()
    require(len(blob) == record['bytes'] and hashlib.sha256(blob).hexdigest() == record['sha256'],
            f'Source identity changed at {path}')


def blocks(text):
    anchors = list(re.finditer(r'^<a id="(ch-\d+|appendix-[a-f])"></a>', text, re.M))
    return {m[1]: text[m.start():anchors[i+1].start() if i+1 < len(anchors) else len(text)]
            for i, m in enumerate(anchors)}


def historical_inputs():
    inventories = (QM / 'kernel/evidence/v31.14/source-manifest.json',
                   QM / 'kernel/evidence/v31.11/source-manifest.json')
    count = 0
    for path, field in zip(inventories, ('files', 'sources')):
        raw = previous(path)
        require((ROOT / path).read_bytes() == raw, f'Historical inventory changed at {path}')
        for record in json.loads(raw)[field]:
            if record['path'] not in REPLACED:
                check_identity(record)
                count += 1
    return count


def main():
    count = historical_inputs()
    dossier_path = BOOK / 'CHAPTER_DOSSIER.json'
    manifest_path = BOOK / 'SOURCE_MANIFEST.json'
    prev_ledger = QM / 'status/CLAIM_LEDGER_v31.14.json'
    current = read(QM / 'status/CURRENT.json')
    dossier, manifest = read(dossier_path), read(manifest_path)
    old_dossier = json.loads(previous(dossier_path))
    proof = json.loads(previous(QM / 'status/CURRENT.json'))['source_identity']
    require(current['source_identity'] == proof and dossier['publication_source_identity'] == proof
            and manifest['publication_source_identity'] == proof, 'Historical proof identity changed')
    require(manifest['entries'][:-1] == json.loads(previous(manifest_path))['entries'], 'Source registry prefix changed')
    require(manifest['entries'][-1]['id'] == 'QM3115', 'Missing Chapter 71 source')
    require(dossier['author'] == old_dossier['author'], 'Historical author changed')
    require(current['book']['dossier']['path'] == str(dossier_path)
            and dossier['book_source_manifest']['path'] == str(manifest_path), 'Publication metadata path mismatch')
    check_identity(current['book']['dossier'])
    check_identity(dossier['book_source_manifest'])
    prior_run = read(QM / 'kernel/evidence/v31.14/integration-verification.json')
    check_identity(current['previous_main_lean_rebuild'])
    require(prior_run['verified_scientific_main'] == BASE and prior_run['main_run'] == 44318642942
            and prior_run['pr'] == 466 and prior_run['scientific_main_verified'], 'Wrong previous main run')
    jobs = {job['name']: job for job in prior_run['jobs']}
    require(all(jobs[j]['conclusion'] == 'success' for j in ('lean', 'runtime'))
            and {'Build all QM proofs', 'Audit theorem axioms', 'Verify retained finite and quantum Lean witnesses'}
            <= set(jobs['lean']['successful_steps']), 'Incomplete previous main rebuild')
    require(current['integration']['remote_verified'] is False and current['book']['checked_in_pdf_edition'] == '3.11'
            and current['book']['pdf_acceptance'] == 'PENDING' and current['verification_state'] == 'MANUSCRIPT_CANDIDATE',
            'Manuscript promoted without acceptance')
    old_rows = [r for ch in old_dossier['chapters'] for r in ch['numbered_results']]
    rows = [r for ch in dossier['chapters'] for r in ch['numbered_results']]
    require(len(old_rows) == 203 and rows[:203] == old_rows and [r['id'] for r in rows[203:]] == IDS,
            'Historical or new result objects mismatch')
    require((ROOT / prev_ledger).read_bytes() == previous(prev_ledger), 'Previous ledger bytes changed')
    ledger = read(QM / 'status/CLAIM_LEDGER_v31.15.json')
    require(ledger['claims'][:126] == read(prev_ledger)['claims'] and len(ledger['claims']) == ledger['claim_count'] == 133,
            'Claim ledger prefix or count mismatch')
    for r, claim in zip(rows[203:], ledger['claims'][126:]):
        require(claim['id'] == 'QMK-'+r['id'] and claim['book_result'] == r['id']
                and claim['verification_scope'] == r['question_and_quantifiers']
                and claim['premises'] == r['premises'] and claim['proof_and_evidence'] == r['proof_and_evidence']
                and r['premises'] and r['new_lean'] is False and r['new_hardware_data'] is False,
                'Incorrect claim scope for '+r['id'])
        require(len(r['proof_and_evidence']) >= 2, 'Missing result evidence for '+r['id'])
        for item in r['proof_and_evidence']:
            check_identity(item)

    certificate = read(SCIENCE / 'certificate/joint-result.json')['results']
    require([r['timing'] for r in certificate] == [['2/3','3/4','1/2'], ['3/4','2/3','1/2']], 'Timing order')
    bounds = [('0.033892297103','0.046090140885','0.046090140889'),
              ('0.035357047207','0.047554890989','0.047554890993')]
    for values, r in zip(bounds, certificate):
        complete, analog, digitized = map(Fraction,values)
        require([complete, analog, digitized] == [Fraction(r[k]) for k in ('complete_upper','terminal_upper','terminal_digitized_upper')]
                and r['cells'] == 4 and r['distinct_vertices'] == 18, 'Certificate or geometry changed')
        exact = analog + Fraction(4,2**40)
        require(Fraction(r['sampler_tv_allowance']) == Fraction(4,2**40)
                and exact <= digitized < exact + Fraction(1,10**12) and digitized < Fraction(r['target']),
                'Invalid outward sampling allowance')
    for name, n in [('calibration',720000), ('holdout',408000)]:
        receipt = read(SCIENCE / f'inference/{name}_receipt.json')
        require(receipt['shots'] == n and receipt['raw_sha256'] == hashlib.sha256(
            (ROOT/SCIENCE/f'inference/{name}.npz').read_bytes()).hexdigest(), 'Frozen sample identity '+name)
    held = read(SCIENCE / 'inference/holdout_results.json')
    require(held['families'] == {'independent_break':'NOT_REJECTED','original':'NOT_REJECTED',
            'swap':'NOT_REJECTED','readout_challenge':'REJECTED'} and len(held['failed_cells']['readout_challenge']) == 4
            and held['device'] == 'NOT_CERTIFIED' and held['strong_baseline'] == 'EQUIVALENT_NO_ADDED_GAIN',
            'Frozen inference scope changed')
    chapters = {}
    for lang, suffix in [('zh',''),('en','.en')]:
        path = BOOK / f'UEOT_PHYSICS{suffix}.md'
        text = (ROOT/path).read_text()
        source = inspect_book(text)
        require((source['chapters'], source['appendices'], source['numbered_results']) == (72,6,210), lang+' structure')
        old = previous(path).decode()
        require(source['claims'][:203] == inspect_book(old)['claims'], lang+' inherited titles and anchors')
        for r, parsed in zip(rows[203:],source['claims'][203:]):
            require((parsed['id'],parsed['chapter'],parsed['title']) == (r['id'],71,r['title' if lang=='zh' else 'title_en']),
                    lang+' result binding '+r['id'])
        current_blocks = blocks(text)
        for name, body in blocks(old).items():
            if name not in {'ch-0','ch-48','appendix-b','appendix-c','appendix-e','appendix-f'}:
                require(current_blocks[name] == body, lang+' prior body '+name)
        for ch in dossier['chapters'] + dossier['appendices']:
            body = current_blocks[ch['anchor']].encode()
            pin = ch['publication_3_12'][lang]
            require(pin['body_sha256'] == hashlib.sha256(body).hexdigest() and pin['body_utf8_bytes'] == len(body),
                    lang+' chapter identity '+ch['anchor'])
        for obj, key in [(dossier,'canonical'),(manifest,'canonical_identity')]:
            if lang == 'en':
                key = 'canonical_english' if obj is dossier else 'canonical_english_identity'
            require(obj[key]['path'] == str(path), lang+' canonical path')
            check_identity(obj[key])
        chapter = chapters[lang] = current_blocks['ch-71']
        table = [tuple(re.findall(r'0\.\d{12}', line)) for line in chapter.splitlines() if re.match(r'^\|.*0\.\d{12}',line)]
        require(table == bounds, lang+' three scopes and outward bounds')
        for target in re.findall(r'\]\(([^ )]+)\)',chapter):
            require(target.startswith('../correlated_bath/') and (ROOT/BOOK/target).is_file(), lang+' source link '+target)
        require('/Users/' not in chapter and '/private/tmp/' not in chapter, lang+' local path')
    for pattern in (r'(?ms)^\$\$\n(.*?)\n\$\$$', r'(?m)^## (71\.\d+)', r'\]\(([^ )]+)\)'):
        zh, en = [re.findall(pattern, chapters[k]) for k in ('zh','en')]
        require(zh and zh == en, 'Bilingual formula, section or source mismatch')
    print(f'PASS Chapter 71 source candidate: 210 results, 133 claims, {count} inherited input records. PDF acceptance pending.')


if __name__ == '__main__':
    main()
