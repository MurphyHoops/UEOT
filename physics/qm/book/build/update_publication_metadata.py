#!/usr/bin/env python3
"""Upgrade only UEOT Physics publication metadata to bilingual edition 3.7.

Default: validate and report without touching the book directory. --output-dir
writes an explicitly labelled preview outside the book directory. --write
installs the SOURCE_MANIFEST first, then the dossier, only after both builds and
the scoped visual receipt bind the actual six installed artifacts.

No scientific source, result object, source-catalog object, prior receipt, or
historical snapshot is edited. This script runs no Lean, numerical experiment,
PDF build, or visual inspection. A downstream local-acceptance receipt is only
referenced by path, so it can bind this metadata without a hash cycle.
"""
from __future__ import annotations
import argparse
import copy
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

# Reading the maintained verifier must not create __pycache__ in its worktree.
sys.dont_write_bytecode = True

EDITION = '3.7'
BASELINE = '925e3a8a411c0b1bab99dd9150bf005893656140'
GENERATOR = 'ueot-physics-bilingual-publication-metadata-3.7'
BOOK_REL = Path('physics/qm/book')
EXPECTED_ANCHORS = [f'ch-{i}' for i in range(67)] + [f'appendix-{x}' for x in 'abcdef']
BODY_RULE = 'stable chapter/appendix anchor inclusive to next such anchor exclusive; final appendix through EOF; exact UTF-8 bytes'
ROW_MUTATIONS = {'body_sha256', 'body_utf8_bytes', 'body_slice_convention',
                 'sections', 'body_revision_history', 'current_edition_action',
                 'current_edition_verification', 'publication_3_7'}
VISUAL_PASS = {'PASS', 'PASS_WITH_STATED_SCOPE', 'PASS_SCOPED_REVIEW'}

class MetadataError(RuntimeError):
    pass

def require(condition, message):
    if not condition:
        raise MetadataError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def packed(obj):
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode('utf-8')

def render(obj):
    return (json.dumps(obj, ensure_ascii=False, indent=2) + '\n').encode('utf-8')

def object_identity(obj):
    return {'canonical_json_sha256': sha(packed(obj)), 'scope': 'JSON values, including all historical status fields; not source-file whitespace'}

def git_bytes(repo, commit, path):
    return subprocess.check_output(['git', '-C', str(repo), 'show', f'{commit}:{path}'])

class Reader:
    def __init__(self, repo):
        self.repo = repo
        self.observed = {}

    def label(self, path):
        try:
            return path.resolve().relative_to(self.repo).as_posix()
        except ValueError:
            return str(path.resolve())

    def read(self, path):
        path = Path(path).resolve()
        data = path.read_bytes()
        self.observed[path] = sha(data)
        return data

    def identity(self, path):
        path = Path(path).resolve()
        data = self.read(path)
        return {'path': self.label(path), 'sha256': sha(data), 'bytes': len(data)}

    def json(self, path):
        return json.loads(self.read(path).decode('utf-8'))

    def unchanged(self):
        for path, expected in self.observed.items():
            require(path.exists() and sha(path.read_bytes()) == expected,
                    f'Input changed while metadata was being prepared: {path}')


def slices(raw):
    matches = list(re.finditer(rb'^<a id="(ch-\d+|appendix-[a-f])"></a>\r?$', raw, re.M))
    names = [m.group(1).decode() for m in matches]
    require(names == EXPECTED_ANCHORS, 'Expected the exact ordered 67 chapter and six appendix anchors')
    return {name: raw[matches[i].start():matches[i+1].start() if i+1 < len(matches) else len(raw)]
            for i, name in enumerate(names)}


def sections(raw):
    # The maintained dossier's primary section index uses ## headers. F.3.n
    # audit-list subdivisions remain within the full byte-bound appendix.
    return [{'id': m.group(1), 'title': m.group(2)}
            for m in re.finditer(r'^## ((?:\d+|[A-F])\.\d+)\.?\s+(.+)$', raw.decode('utf-8'), re.M)]


def heading(raw):
    m = re.search(r'^# (.+)$', raw.decode('utf-8'), re.M)
    require(m is not None, 'No chapter/appendix heading in an anchored slice')
    return m.group(1)


def python_blocks(raw):
    """Exact fenced Python payloads only; does not equate edited Appendix D prose."""
    lines = raw.splitlines(keepends=True)
    blocks, i = [], 0
    while i < len(lines):
        m = re.fullmatch(rb'([~`]{3,})\s*(?:python|python3|py)\s*\r?\n?', lines[i])
        if not m:
            i += 1
            continue
        marker = m.group(1)
        require(len(set(marker)) == 1, 'Mixed code fence')
        content = []
        i += 1
        closing = re.compile(rb'\s*' + re.escape(marker[:1]) + rb'{' + str(len(marker)).encode() + rb',}\s*\r?\n?')
        while i < len(lines) and not closing.fullmatch(lines[i]):
            content.append(lines[i])
            i += 1
        require(i < len(lines), 'Unclosed Python code fence')
        blocks.append(b''.join(content))
        i += 1
    return blocks


def all_results(dossier):
    return [r for c in dossier['chapters'] for r in c.get('numbered_results', [])]


def preserve_guard(current_m, current_d, prior_m, prior_d):
    require(len(prior_m['entries']) == 12, 'Prior manifest must contain exactly 12 entries')
    require(len(all_results(prior_d)) == 173, 'Prior dossier must contain exactly 173 results')
    require(current_m['entries'] == prior_m['entries'], 'Current manifest entry objects differ from the immutable 3.6 snapshot')
    require(all_results(current_d) == all_results(prior_d), 'Current numbered_results objects differ from the immutable 3.6 snapshot')
    require(current_d['source_catalog'] == prior_d['source_catalog'], 'Current source_catalog differs from the immutable 3.6 snapshot')
    require([c['number'] for c in prior_d['chapters']] == list(range(67)), 'Prior chapter sequence is incomplete')
    require([a['id'] for a in prior_d['appendices']] == list('ABCDEF'), 'Prior appendix sequence is incomplete')
    ids = [r['id'] for r in all_results(prior_d)]
    require(len(set(ids)) == 173, 'Prior result IDs are not unique')


def bound_build(reader, book, language, assets, pending):
    location = book / f'evidence/v3.7/pdf-{language}/pdf-build.json'
    if not location.exists():
        pending.append(f'Missing {reader.label(location)}')
        return {'path': reader.label(location), 'status': 'PENDING', 'bound_to_installed_artifacts': False}
    receipt = reader.json(location)
    checks = {
        'source_sha256': assets['markdown'].get('sha256'),
        'tex_sha256': assets['latex'].get('sha256'),
        'pdf_sha256': assets['pdf'].get('sha256'),
    }
    issues = [f'{key} does not match installed bytes' for key, value in checks.items()
              if value is None or receipt.get(key) != value]
    if receipt.get('edition') != EDITION:
        issues.append('build edition is not 3.7')
    if receipt.get('language') not in ({'zh', 'zh-CN'} if language == 'zh' else {'en'}):
        issues.append('build language does not match')
    if receipt.get('chapters') != 67 or receipt.get('appendices') != 6:
        issues.append('build chapter/appendix counts do not match')
    passes = receipt.get('compile_passes', [])
    if len(passes) != 3 or any(x.get('exit_code') != 0 for x in passes):
        issues.append('three successful compile passes are not recorded')
    if receipt.get('internal_links_valid') is not True:
        issues.append('internal-link validation is not recorded as true')
    if receipt.get('layout_warnings') != []:
        issues.append('layout_warnings are absent or nonempty')
    if receipt.get('rerun_warnings', []) != []:
        issues.append('unresolved rerun warnings')
    if receipt.get('last_two_auxiliary_files_identical') is not True:
        issues.append('last two auxiliary-file identities are not recorded as equal')
    for issue in issues:
        pending.append(f'{reader.label(location)}: {issue}')
    result = {**reader.identity(location), 'status': 'PASS_BOUND_THREE_PASSES' if not issues else 'PENDING_OR_MISMATCH',
              'bound_to_installed_artifacts': not issues, 'issues': issues,
              'scope': 'Read existing build receipt and matched actual Markdown, TeX and PDF bytes; this updater did not compile'}
    return result


def bound_visual(reader, book, assets, pending):
    location = book / 'evidence/v3.7/pdf-visual-review.json'
    if not location.exists():
        pending.append(f'Missing {reader.label(location)}')
        return {'path': reader.label(location), 'status': 'PENDING', 'bound_to_installed_artifacts': False}
    receipt = reader.json(location)
    issues = []
    if receipt.get('status') not in VISUAL_PASS:
        issues.append('visual receipt does not record an accepted scoped PASS status')
    views = receipt.get('editions', {})
    for lang in ('zh', 'en'):
        v = views.get(lang, {})
        if v.get('pdf_sha256') != assets[lang]['pdf'].get('sha256'):
            issues.append(f'{lang} PDF identity mismatch')
        if v.get('source_sha256') != assets[lang]['markdown'].get('sha256'):
            issues.append(f'{lang} Markdown identity mismatch')
        if not isinstance(v.get('pages'), int) or v.get('pages', 0) <= 0:
            issues.append(f'{lang} positive page count missing')
        for key in ('overview_pages_viewed', 'selected_full_pages_viewed'):
            if key not in v:
                issues.append(f'{lang} actual visual scope field missing: {key}')
    for issue in issues:
        pending.append(f'{reader.label(location)}: {issue}')
    return {**reader.identity(location), 'status': receipt.get('status', 'UNKNOWN'),
            'bound_to_installed_artifacts': not issues, 'issues': issues,
            'editions': copy.deepcopy(views), 'reviewer_reports': copy.deepcopy(receipt.get('reviewer_reports', [])),
            'scope': copy.deepcopy(receipt.get('scope')),
            'review_performed_by_metadata_updater': False,
            'pixel_equivalence_or_actual_viewing_responsibility': 'As stated by the visual reviewer in this receipt; not independently inferred by this metadata updater'}


def artifact_identity(reader, path, pending):
    if not path.exists():
        pending.append(f'Missing installed artifact {reader.label(path)}')
        return {'path': reader.label(path), 'status': 'MISSING'}
    return {**reader.identity(path), 'status': 'BYTES_IDENTIFIED'}


def atomic_write(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, temp = tempfile.mkstemp(prefix=path.name + '.', suffix='.tmp', dir=path.parent)
    try:
        with os.fdopen(handle, 'wb') as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temp, path)
    finally:
        if os.path.exists(temp):
            os.unlink(temp)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--book-dir', type=Path, required=True)
    p.add_argument('--repo-root', type=Path)
    p.add_argument('--baseline-commit', default=BASELINE)
    p.add_argument('--expected-zh-sha256')
    p.add_argument('--expected-en-sha256')
    p.add_argument('--recorded-at', help='Explicit ISO timestamp; otherwise retain an existing generated 3.7 timestamp or use current UTC')
    mode = p.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true', help='Install into the official book directory after all artifact/receipt gates match')
    mode.add_argument('--output-dir', type=Path, help='Write preview JSON files only to a separate directory; missing build/visual gates remain PENDING')
    p.add_argument('--report', type=Path, help='External metadata identity receipt; must not be either metadata file or local-acceptance.json')
    args = p.parse_args()
    book = args.book_dir.resolve()
    repo = (args.repo_root or book.parents[2]).resolve()
    require(book == repo / BOOK_REL, 'book-dir must be repo-root/physics/qm/book')
    if args.output_dir:
        require(args.output_dir.resolve() != book, '--output-dir must be separate from the official book directory; use --write explicitly')
    require(bool(args.expected_zh_sha256) == bool(args.expected_en_sha256), 'Supply both expected manuscript hashes, or neither')
    reader = Reader(repo)
    current_paths = {'manifest': book/'SOURCE_MANIFEST.json', 'dossier': book/'CHAPTER_DOSSIER.json'}
    current_m, current_d = reader.json(current_paths['manifest']), reader.json(current_paths['dossier'])
    prior_publication_remote = current_d.get('publication_revision', {}).get('remote_publication', {})
    require(prior_publication_remote.get('status') in (None, 'PENDING'), 'Publication remote acceptance has already advanced; refuse to downgrade it to PENDING')
    require(not any(prior_publication_remote.get(k) is not None for k in ('pr','source_commit','pr_ci','merged_main_commit','main_ci')), 'Existing publication PR/CI identities require an explicit metadata continuation; this pre-PR updater will not erase them')
    prior_paths = {'manifest': book/'evidence/v3.7/source-manifest-prior-v3.6.json',
                   'dossier': book/'evidence/v3.7/dossier-prior-v3.6.json'}
    prior_m, prior_d = reader.json(prior_paths['manifest']), reader.json(prior_paths['dossier'])
    require(prior_m.get('edition') == prior_d.get('edition') == '3.6', 'Immutable input snapshots must be research edition 3.6')
    for kind, rel in [('manifest', 'SOURCE_MANIFEST.json'), ('dossier', 'CHAPTER_DOSSIER.json')]:
        expected = git_bytes(repo, args.baseline_commit, str(BOOK_REL/rel))
        require(reader.read(prior_paths[kind]) == expected, f'Immutable prior {kind} snapshot does not match the stated baseline commit')
    preserve_guard(current_m, current_d, prior_m, prior_d)
    require(prior_m['current_code_identity']['status'] == 'MAIN_VERIFIED', 'Research status is not the expected MAIN_VERIFIED; do not invent acceptance')
    inventory = prior_d['verified_inventory']
    for key, expected in [('public_modules',49),('public_explicit_theorems',959),('public_named_axiom_reports',1285),
                          ('semantic_runtime_tests',19),('exact_symbolic_checks',95)]:
        require(inventory.get(key) == expected, f'Research inventory mismatch: {key}')
    pending = []
    raw = {lang: reader.read(book/name) for lang,name in [('zh','UEOT_PHYSICS.md'),('en','UEOT_PHYSICS.en.md')]}
    for lang, expected in [('zh',args.expected_zh_sha256),('en',args.expected_en_sha256)]:
        if expected:
            require(re.fullmatch(r'[0-9a-f]{64}', expected) and sha(raw[lang]) == expected, f'{lang} frozen manuscript identity mismatch')
        require(re.search(r'^version:\s*["\']?3\.7["\']?\s*$', raw[lang].decode(), re.M), f'{lang} frontmatter is not edition 3.7')
    verifier_path = book/'build/verify_book.py'
    spec = importlib.util.spec_from_file_location('ueot_publication_structure', verifier_path)
    require(spec is not None and spec.loader is not None, 'Cannot load the maintained book structure verifier')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    verifier_identity = reader.identity(verifier_path)
    structure = {lang:module.inspect_book(data.decode('utf-8')) for lang,data in raw.items()}
    expected_ids = [r['id'] for r in all_results(prior_d)]
    for lang in raw:
        require([c['id'] for c in structure[lang]['claims']] == expected_ids, f'{lang} result sequence differs from prior 173 objects')
    parts = {lang:slices(data) for lang,data in raw.items()}
    for anchor in EXPECTED_ANCHORS:
        require([s['id'] for s in sections(parts['zh'][anchor])] == [s['id'] for s in sections(parts['en'][anchor])], f'Section correspondence mismatch at {anchor}')
    assets = {}
    for lang,stem in [('zh','UEOT_PHYSICS'),('en','UEOT_PHYSICS.en')]:
        assets[lang] = {kind:artifact_identity(reader,book/(stem+ext),pending)
                        for kind,ext in [('markdown','.md'),('latex','.tex'),('pdf','.pdf')]}
    builds = {lang:bound_build(reader,book,lang,assets[lang],pending) for lang in ('zh','en')}
    visual = bound_visual(reader,book,assets,pending)
    prior_raw = git_bytes(repo,args.baseline_commit,str(BOOK_REL/'UEOT_PHYSICS.md'))
    require(sha(prior_raw) == prior_m['canonical_identity']['sha256'], 'Prior Markdown does not match prior canonical identity')
    previous_d = slices(prior_raw)['appendix-d']
    prior_programs = python_blocks(previous_d)
    require(len(prior_programs) == 3, 'Expected three original Python program blocks in Appendix D')
    for lang in ('zh','en'):
        require(python_blocks(parts[lang]['appendix-d']) == prior_programs, f'{lang} Appendix D Python blocks changed')
    prior_ids = {kind:reader.identity(path) for kind,path in prior_paths.items()}
    previous_layer = current_d.get('publication_revision', {})
    timestamp = args.recorded_at or (previous_layer.get('recorded_at_utc') if previous_layer.get('generator') == GENERATOR else None) or datetime.now(timezone.utc).isoformat()
    remote_publication = {'status':'PENDING','pr':None,'source_commit':None,'pr_ci':None,'merged_main_commit':None,'main_ci':None,
                          'scope':'The new bilingual publication PR; research PR450/main acceptance is separate and remains inherited MAIN_VERIFIED'}
    local_acceptance_path = str(BOOK_REL/'evidence/v3.7/local-acceptance.json')
    update_receipt_path = str(BOOK_REL/'evidence/v3.7/publication-metadata-update.json')
    # A terminal receipt may hash this metadata. Never import its hash or status
    # back into either document, including on reruns.
    terminal = repo/local_acceptance_path
    terminal_observation = {'path':local_acceptance_path,'exists':terminal.exists(),'scope':'Downstream only; not embedded into either metadata object'}
    if terminal.exists():
        observed = json.loads(terminal.read_bytes())
        terminal_observation['recorded_status'] = observed.get('status')
    review_files = []
    review_dir = book/'review'
    if review_dir.exists():
        for path in sorted(review_dir.rglob('*')):
            if path.is_file() and path.suffix in {'.md','.json','.py'}:
                require(not path.is_symlink(), f'Review artifact symlink requires explicit inspection: {path}')
                review_files.append(reader.identity(path))
    for location in [book/'evidence/v3.7/review-integration.json']:
        if location.exists():
            review_files.append(reader.identity(location))
    evidence_names = [
        'source-reuse.json', 'v31.10-remote-observation.json',
        'book-structure.zh.json', 'book-structure.en.json', 'bilingual-fidelity.json',
        'inline_math_fidelity.json', 'theory_review_closure.json',
        'axiom_inventory_v31_10_identity.json', 'ch66_source_bindings.json',
        'ch66_translation_fidelity.json', 'claim_matrix_increment_identity.json',
        'inherited_formal_source_v31_10_identity.json', 'review-integration.json',
        'A_FINAL_DELIVERABLES.json', 'PUBLICATION_3_7_EMPIRICAL_CLOSEOUT.json',
        'EDITORIAL_REVIEW_CLOSEOUT_3_7.json', 'EMPIRICAL_NUMBER_CHECK.json',
        'INCREMENTAL_EDITORIAL_MECHANICAL_QA_3_7.json',
        'WHOLE_BOOK_DISPLAY_LABEL_FIDELITY_3_7.json', 'CHAPTER_66_FIDELITY_QA.json',
        'record-example-check.json', 'build-environment.json', 'pdf-technical-check.json',
    ]
    publication_evidence = [reader.identity(book/'evidence/v3.7'/name)
                            for name in evidence_names if (book/'evidence/v3.7'/name).exists()]
    preservation = {'numbered_results':{'count':173,'all_objects_exactly_preserved':True,**object_identity(all_results(prior_d))},
                    'manifest_entries':{'count':12,'all_objects_exactly_preserved':True,**object_identity(prior_m['entries'])},
                    'source_catalog':{'entry_count':len(prior_d['source_catalog']),'exactly_preserved':True,**object_identity(prior_d['source_catalog'])},
                    'appendix_d_programs':{'count':3,'both_languages_exact_payload_bytes':True,
                        'sha256':[sha(x) for x in prior_programs],
                        'whole_appendix_bytes_equal_prior':{lang:parts[lang]['appendix-d']==previous_d for lang in ('zh','en')},
                        'scope':'Python fenced payloads only; surrounding prose and receipt descriptions were edited; no historical programs rerun'}}
    science = {'research_version':'v31.10-kernel1.10','research_book_edition':'3.6','status':'MAIN_VERIFIED',
               'status_source':'Inherited exact research metadata/receipts; not a new remote observation by this updater',
               'publication_baseline':args.baseline_commit,'local_heavy_science_rerun_for_publication':False,
               'kernel_or_lean_modified_by_updater':False,'new_hardware_data':False,
               'reused_inventory':copy.deepcopy(inventory),
               'historical_counts':{'757':'Three inherited Appendix D programs: actual edition-3.0 execution, later byte reuse',
                                    '1123':'Historical v31.9 named-axiom prefix, not current total; v31.10 total is 1285'},
               'remote_identity':copy.deepcopy(prior_d['current_remote_code_identity'])}
    layer = {'edition':EDITION,'generator':GENERATOR,'recorded_at_utc':timestamp,
             'scope':'Publication metadata and bilingual correspondence only; all scientific result/source objects retain their historical responsibility',
             'local_artifact_state':'BOUND_TO_ACTUAL_BUILD_AND_SCOPED_VISUAL_RECEIPTS' if not pending else 'PENDING_ARTIFACT_RECEIPTS',
             'pending_gates':pending,'remote_publication':remote_publication,'scientific_reuse':science,
             'prior_snapshots':prior_ids,'preservation':preservation,'artifacts':assets,'build_receipts':builds,
             'visual_review':visual,'local_acceptance_receipt':{'path':local_acceptance_path,'direction':'Downstream terminal acceptance; path only to avoid circular hashes'},
             'metadata_update_receipt':{'path':update_receipt_path,'direction':'Downstream; path only'},
             'review_materials':review_files,'publication_evidence':publication_evidence,
             'publication_evidence_scope':'Exact installed receipt identities, retaining each receipt\'s own scope and historical/current distinction; the A handoff inventory is not a byte-identity assertion for adapted integrated reports',
             'review_identity_policy':'Current installed report bytes are identified here. Original A handoff manifest describes pre-integration copies; relative-link adaptation is separately recorded and is not falsely treated as byte identity.',
             'hash_direction':'MD/TeX/PDF, independent build/visual receipts and immutable prior snapshots -> SOURCE_MANIFEST -> CHAPTER_DOSSIER -> external metadata-update receipt -> terminal local-acceptance; no reverse hashes',
             'structure_verifier':verifier_identity,
             'new_scientific_results_in_publication':0,'renumbered_or_withdrawn_results':[],
             'not_inferred':['external peer review','new Lean execution','new runtime/experimental execution','new publication PR or main acceptance']}
    manifest = copy.deepcopy(current_m)
    dossier = copy.deepcopy(current_d)
    # Exact old fields are preserved in full snapshots and copied here for
    # locally reviewable transitions; numbered objects are never rebuilt.
    manifest_changed = ['edition','recorded_at_utc','canonical_identity','prior_complete_manifest','current_release_stage',
                        'local_release_receipt','local_release_receipt_scope','legacy_program_reuse']
    dossier_changed = ['edition','recorded_at_utc','editorial_status','canonical','derivatives','prior_complete_dossier',
                       'current_release_stage','book_source_manifest','validation','release_acceptance']
    def inherited_fields(prior, keys):
        return {k:copy.deepcopy(prior[k]) for k in keys if k in prior}
    manifest_layer = copy.deepcopy(layer)
    manifest_layer['prior_current_fields'] = inherited_fields(prior_m,manifest_changed)
    dossier_layer = copy.deepcopy(layer)
    dossier_layer['prior_current_fields'] = inherited_fields(prior_d,dossier_changed)
    def canonical(lang):
        return {**assets[lang]['markdown'],'chapters':67,'appendices':6,'numbered_results':173,
                'inherited_result_ids':173,'new_result_ids':0,'identity_scope':'ACTUAL_LOCAL_BILINGUAL_SOURCE_BYTES',
                'installation_status':'LOCAL_BYTES_IDENTIFIED_PUBLICATION_REMOTE_PENDING','language':'zh-CN' if lang=='zh' else 'en'}
    for doc in (manifest,dossier):
        doc['edition'] = EDITION
        doc['recorded_at_utc'] = timestamp
        doc['current_release_stage'] = 'PUBLICATION_PR_PENDING'
    manifest['canonical_identity'] = canonical('zh')
    manifest['canonical_english_identity'] = canonical('en')
    manifest['prior_complete_manifest'] = prior_ids['manifest']
    manifest['local_release_receipt'] = local_acceptance_path
    manifest['local_release_receipt_scope'] = 'Terminal publication acceptance, to be issued or refreshed after metadata identities are final; not the v31.10 research execution gate'
    legacy = copy.deepcopy(prior_m['legacy_program_reuse'])
    legacy.update(reexecuted_this_edition=False,appendix_d_exact_bytes_unchanged=preservation['appendix_d_programs']['whole_appendix_bytes_equal_prior']['zh'],
                  program_blocks_exact_bytes_unchanged=True,program_blocks=preservation['appendix_d_programs'],
                  scope='3.7 preserves the three exact program payloads in both languages; Appendix D prose is edited. The older preservation_receipt and historical_receipt below keep their original scope.',
                  publication_preservation_receipt=update_receipt_path)
    manifest['legacy_program_reuse'] = legacy
    manifest['publication_revision'] = manifest_layer
    dossier['canonical'] = canonical('zh')
    dossier['canonical_english'] = canonical('en')
    dossier['prior_complete_dossier'] = prior_ids['dossier']
    dossier['editorial_status'] = 'LOCAL_PUBLICATION_REVIEWED_REMOTE_PENDING' if not pending else 'PUBLICATION_ARTIFACTS_PENDING'
    derivatives = {}
    for lang in ('zh','en'):
        group = {}
        for kind in ('pdf','latex'):
            group[kind] = {**assets[lang][kind],
                'source_sha256':assets[lang]['markdown']['sha256'] if builds[lang]['bound_to_installed_artifacts'] else None,
                'status':'LOCAL_BUILD_IDENTITY_VERIFIED' if builds[lang]['bound_to_installed_artifacts'] else 'PENDING_BUILD_BINDING',
                'actual_build_receipt':builds[lang],'remote_publication_status':'PENDING'}
            if kind == 'pdf' and visual['bound_to_installed_artifacts']:
                group[kind]['pages'] = visual['editions'][lang]['pages']
        if lang == 'zh':
            derivatives.update(group)
        else:
            derivatives['english'] = group
    derivatives['visual_review'] = visual
    dossier['derivatives'] = derivatives
    claims_by_lang = {lang:{x['id']:x for x in structure[lang]['claims']} for lang in ('zh','en')}
    for group_name in ('chapters','appendices'):
        require(len(dossier[group_name]) == len(prior_d[group_name]), f'Unexpected {group_name} length')
        for row, prior_row in zip(dossier[group_name],prior_d[group_name]):
            anchor = prior_row['anchor']
            require(row['anchor'] == anchor, f'Row identity changed at {anchor}')
            previous = {k:copy.deepcopy(prior_row[k]) for k in ROW_MUTATIONS-{'body_revision_history','publication_3_7'} if k in prior_row}
            history = copy.deepcopy(row.get('body_revision_history', []))
            marker = {'edition':'3.6','exact_prior_record':prior_ids['dossier']['path'],'anchor':anchor,
                      'prior_dossier_sha256':prior_ids['dossier']['sha256'],'prior_publication_fields':previous}
            if marker not in history:
                history.append(marker)
            row['body_revision_history'] = history
            row['body_sha256'] = sha(parts['zh'][anchor])
            row['body_utf8_bytes'] = len(parts['zh'][anchor])
            row['body_slice_convention'] = BODY_RULE
            row['sections'] = sections(parts['zh'][anchor])
            row['current_edition_action'] = 'BILINGUAL_PUBLICATION_REVIEWED_IN_3_7'
            row['current_edition_verification'] = {'edition':EDITION,'body_hash_checked':True,'english_body_hash_checked':True,
                'scope':'Exact bilingual text and stable-ID correspondence only; inherited numbered-result proof and experimental fields are unchanged, including their historical statuses',
                'publication_remote_status':'PENDING'}
            row['publication_3_7'] = {'zh':{'path':assets['zh']['markdown']['path'],'anchor':anchor,'heading':heading(parts['zh'][anchor]),
                                           'body_sha256':row['body_sha256'],'body_utf8_bytes':row['body_utf8_bytes']},
                'en':{'path':assets['en']['markdown']['path'],'anchor':anchor,'heading':heading(parts['en'][anchor]),
                      'body_sha256':sha(parts['en'][anchor]),'body_utf8_bytes':len(parts['en'][anchor]),'sections':sections(parts['en'][anchor])},
                'result_correspondence':[{'id':claim['id'],'anchor':claim['anchor'],
                    'zh_title':claims_by_lang['zh'][claim['id']]['title'],'en_title':claims_by_lang['en'][claim['id']]['title']}
                    for claim in prior_row.get('numbered_results',[])],
                'scope':'Publication view; does not amend the scientific result objects or declare a new proof/experiment'}
            for key in set(row)|set(prior_row):
                if key not in ROW_MUTATIONS:
                    require(row.get(key) == prior_row.get(key), f'Attempted non-publication row change: {anchor}.{key}')
    # Keep the earlier edition_history entries byte-equivalent as JSON values.
    history = copy.deepcopy(current_d.get('edition_history', []))
    marker = {'edition':'3.6','complete_dossier':prior_ids['dossier'],'canonical':copy.deepcopy(prior_d['canonical']),
              'historical_scope':'Complete original v31.10 research publication, MAIN_VERIFIED; scientific source objects and old statuses remain unchanged in that snapshot'}
    if marker not in history:
        history.append(marker)
    dossier['edition_history'] = history
    dossier['publication_revision'] = dossier_layer
    dossier['validation'] = {'status':'PASS_PUBLICATION_IDENTITY_CHECKS' if not pending else 'PUBLICATION_IDENTITY_CHECKS_PASS_ARTIFACT_GATES_PENDING',
        'canonical_sha256_checked':True,'english_canonical_sha256_checked':True,
        'chapter_numbers':list(range(67)),'appendix_ids':list('ABCDEF'),'numbered_result_count':173,
        'all173_prior_result_objects_exactly_preserved':True,'source_catalog_exactly_preserved':True,
        'manifest_12_entry_objects_exactly_preserved':True,'body_slices_rehashed':73,'english_body_slices_rehashed':73,
        'all_body_hashes_verified':True,'numbered_section_count':sum(len(sections(x)) for x in parts['zh'].values()),
        'main_numbered_section_count':structure['zh']['numbered_sections'],'stable_anchor_count':structure['zh']['stable_anchors'],
        'remote_verified':False,'remote_status':'PENDING','remote_status_scope':'New bilingual publication only',
        'research_status':'MAIN_VERIFIED_REUSED_SOURCE_BOUND_V31_10','whole_physics_formalized':False,
        'new_experimental_data':False,'historical_programs_reexecuted':False,'local_heavy_science_reexecuted':False,
        'current_dossier_hash_receipt':update_receipt_path,'hash_direction':layer['hash_direction'],
        'prior_research_validation':{'path':prior_ids['dossier']['path'],'json_pointer':'/validation'}}
    dossier['release_acceptance'] = {'scope':'3.7 publication; inherited research gates remain separate',
        'unified_lean':'REUSED_SOURCE_BOUND_V31_10_MAIN_VERIFIED','public_axiom_audit':'REUSED_SOURCE_BOUND_V31_10_MAIN_VERIFIED',
        'new_runtime':'NONE_EXECUTED_FOR_PUBLICATION; REUSED_19_SEMANTIC_AND_95_EXACT_RESEARCH_CHECKS',
        'canonical_structure':'PASS_BOTH_LANGUAGES','old_numbered_results':'ALL_173_OBJECTS_EXACTLY_PRESERVED',
        'program_appendix':'THREE_PYTHON_PAYLOADS_EXACT; SURROUNDING_PROSE_EDITED',
        'pdf_build':'PASS_BOUND_THREE_PASSES_BOTH_LANGUAGES' if all(b['bound_to_installed_artifacts'] for b in builds.values()) else 'PENDING',
        'pdf_visual_review':visual['status'] if visual['bound_to_installed_artifacts'] else 'PENDING',
        'local_acceptance_receipt':local_acceptance_path,'source_pr_ci':'PENDING_PUBLICATION_PR','merged_main_ci':'PENDING_PUBLICATION_MAIN'}
    preserve_guard(manifest,dossier,prior_m,prior_d)
    # Scientific metadata outside the explicitly current publication aliases is
    # retained literally, including old MAIN_VERIFIED and older pending states.
    for key in ['source_catalog','verified_inventory','unified_source_identity','publication_source_identity','current_remote_code_identity','completion_boundary','next_execution_contract','status_axes','governance']:
        require(dossier[key] == prior_d[key], f'Scientific dossier field changed: {key}')
    for key in ['entries','current_code_identity','current_code_baseline','current_code_manifest','current_publication_code_manifest',
                'unified_source_identity','publication_source_identity','current_remote_code_identity','remote_metadata_completion','scientific_execution_partition']:
        require(manifest[key] == prior_m[key], f'Scientific manifest field changed: {key}')
    manifest_bytes = render(manifest)
    manifest_id = {'path':str(BOOK_REL/'SOURCE_MANIFEST.json'),'sha256':sha(manifest_bytes),'bytes':len(manifest_bytes)}
    dossier['book_source_manifest'] = manifest_id
    dossier_bytes = render(dossier)
    dossier_id = {'path':str(BOOK_REL/'CHAPTER_DOSSIER.json'),'sha256':sha(dossier_bytes),'bytes':len(dossier_bytes)}
    require(args.report is None or args.report.resolve() not in {current_paths['manifest'],current_paths['dossier'],terminal}, 'Report must be a separate downstream file, not metadata or terminal acceptance')
    require(args.report is None or args.report.resolve() not in reader.observed, 'Report path would overwrite a read input')
    reader.unchanged()
    if args.write:
        require(not pending, 'Publication installation blocked until actual artifact receipts are complete: '+'; '.join(pending))
        destination = book
    else:
        destination = args.output_dir.resolve() if args.output_dir else None
    report = {'schema':'ueot_physics.publication_metadata_update.v1','edition':EDITION,
        'status':'PASS_INSTALLED_METADATA' if args.write else ('PREVIEW_PENDING_ARTIFACT_GATES' if pending else 'PREVIEW_READY'),
        'recorded_at_utc':timestamp,'baseline_commit':args.baseline_commit,'manuscripts':{lang:assets[lang]['markdown'] for lang in assets},
        'candidate_metadata':{'source_manifest':manifest_id,'chapter_dossier':dossier_id},'preservation':preservation,
        'prior_snapshots':prior_ids,'pending_gates':pending,'scientific_execution':'NOT_RERUN; EXISTING_SOURCE_BOUND_RESEARCH_RECEIPTS_REUSED',
        'research_status':'MAIN_VERIFIED','publication_pr_status':'PENDING','local_acceptance_observation':terminal_observation,
        'terminal_acceptance_action':'Issue or refresh local-acceptance.json after these exact metadata hashes are final; do not feed its hash/status back into the metadata',
        'review_materials_identified_from_installed_bytes':len(review_files),'hash_direction':layer['hash_direction'],
        'generator':{'path':str(Path(__file__).resolve()),'sha256':sha(Path(__file__).read_bytes())}}
    if destination:
        # All validation completed before the first mutation. Install in the
        # one-way hash order; the dossier never determines the manifest hash.
        atomic_write(destination/'SOURCE_MANIFEST.json',manifest_bytes)
        require(sha((destination/'SOURCE_MANIFEST.json').read_bytes()) == manifest_id['sha256'], 'Manifest write identity mismatch')
        atomic_write(destination/'CHAPTER_DOSSIER.json',dossier_bytes)
        require(sha((destination/'CHAPTER_DOSSIER.json').read_bytes()) == dossier_id['sha256'], 'Dossier write identity mismatch')
    report_path = args.report.resolve() if args.report else ((book/'evidence/v3.7/publication-metadata-update.json') if args.write else ((destination/'publication-metadata-update.json') if destination else None))
    if report_path:
        atomic_write(report_path,render(report))
    print(json.dumps({'status':report['status'],'destination':str(destination) if destination else None,
                      'metadata':report['candidate_metadata'],'preserved_results':173,'preserved_manifest_entries':12,
                      'preserved_source_catalog':True,'pending_gates':pending,'report':str(report_path) if report_path else None},ensure_ascii=False,indent=2))
    return 0

if __name__ == '__main__':
    try:
        sys.exit(main())
    except (MetadataError,OSError,ValueError,subprocess.CalledProcessError) as error:
        print(json.dumps({'status':'BLOCKED_NO_METADATA_ACCEPTANCE','error':str(error)},ensure_ascii=False),file=sys.stderr)
        sys.exit(1)
