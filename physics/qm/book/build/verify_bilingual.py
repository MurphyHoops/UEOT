#!/usr/bin/env python3
"""Verify bilingual structure, stable IDs, display algebra and literal code blocks.

The result map is a derived index of the books and existing chapter dossier.
It is not another scientific claim ledger. Inline mathematics has a separate
strict AST audit in verify_inline_math.py; prose correctness needs actual review.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

from verify_book import inspect_book

BOOK = Path(__file__).resolve().parents[1]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def ast_items(source):
    ast = json.loads(subprocess.run(['pandoc','-f','markdown+tex_math_dollars','-t','json'],
        input=source, text=True, capture_output=True, check=True).stdout)
    display, code = [], []
    def walk(node):
        if isinstance(node, dict):
            if node.get('t') == 'Math' and node['c'][0]['t'] == 'DisplayMath':
                display.append(node['c'][1])
            if node.get('t') == 'CodeBlock':
                code.append(node['c'])
            for val in node.values():
                walk(val)
        elif isinstance(node,list):
            for val in node:
                walk(val)
    walk(ast['blocks'])
    return display,code


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--map-output',type=Path,required=True)
    args = p.parse_args()
    sources = {lang:(BOOK/name).read_text() for lang,name in
               [('zh','UEOT_PHYSICS.md'),('en','UEOT_PHYSICS.en.md')]}
    structure = {k:inspect_book(v) for k,v in sources.items()}
    labels = json.loads((BOOK/'build/translation_display_labels.json').read_text())
    allowed = {x['zero_based_block_index']:x for x in labels}
    display,code = {},{}
    for lang,source in sources.items():
        display[lang],code[lang] = ast_items(source)
    assert len(display['zh']) == len(display['en']) == 726
    changes = []
    for index,(zh,en) in enumerate(zip(display['zh'],display['en'])):
        if zh == en:
            assert index not in allowed, f'Stale translation exception {index}'
            continue
        assert index in allowed, f'Unexplained display difference {index}'
        label = allowed[index]
        changed = zh
        for z,e in zip(label['zh_text_fragments'],label['en_text_fragments']):
            a,b = r'\text{'+z+'}',r'\text{'+e+'}'
            assert changed.count(a) == 1 and en.count(b) == 1, (index,a,b)
            changed = changed.replace(a,b,1)
        assert changed == en, f'Algebra differs after exact label substitution {index}'
        changes.append({'zero_based_block_index':index,'zh_sha256':sha(zh.encode()),
                        'en_sha256':sha(en.encode()),'label_pairs':list(zip(
                            label['zh_text_fragments'],label['en_text_fragments']))})
    assert len(changes) == 11
    assert code['zh'] == code['en'] and len(code['zh']) == 32
    section_ids = {k:re.findall(r'^## ((?:\d+|[A-F])\.\d+)\b',v,re.M)
                   for k,v in sources.items()}
    assert section_ids['zh'] == section_ids['en'] and len(section_ids['zh']) == 393
    anchors = {k:re.findall(r'<a id="([^"]+)"></a>',v) for k,v in sources.items()}
    assert anchors['zh'] == anchors['en'] and len(anchors['zh']) == 246
    dossier = json.loads((BOOK/'CHAPTER_DOSSIER.json').read_text())
    dossier_ids = [x['id'] for ch in dossier['chapters'] for x in ch['numbered_results']]
    assert [x['id'] for x in structure['zh']['claims']] == dossier_ids
    assert [x['id'] for x in structure['en']['claims']] == dossier_ids
    prior = json.loads((BOOK/'evidence/v3.7/dossier-prior-v3.6.json').read_text())
    prior_claims = [x for ch in prior['chapters'] for x in ch['numbered_results']]
    current_claims = [x for ch in dossier['chapters'] for x in ch['numbered_results']]
    assert current_claims == prior_claims, 'Historical claim objects must remain exact'
    rows=[]
    for z,e in zip(structure['zh']['claims'],structure['en']['claims']):
        assert z['id'] == e['id'] and z['chapter'] == e['chapter']
        rows.append({'id':z['id'],'anchor':z['id'].lower(),'chapter':z['chapter'],
                     'zh_title':z['title'],'en_title':e['title']})
    old = subprocess.check_output(['git','show',
        '3d443ec29eb17af1fc00699a74e2d42d73516d81:physics/qm/book/UEOT_PHYSICS.md'],cwd=BOOK).decode()
    _,old_code=ast_items(old)
    assert len(old_code)==31 and len(code['zh'])==32
    old_code_diffs=[i for i,(a,b) in enumerate(zip(old_code,code['zh'][:31])) if a != b]
    assert old_code_diffs==[4,11], old_code_diffs
    assert 'canonical_source' in old_code[4][1] and 'canonical_source' in code['zh'][4][1]
    assert 'build_pdf.py' in old_code[11][1] and 'build_pdf.py' in code['zh'][11][1]
    names=re.findall(r'^\s*#print\s+axioms\s+(\S+)\s*$',
                     (BOOK.parents[2]/'formalization/ueot-qm/scripts/AxiomAudit.lean').read_text(),re.M)
    assert len(names)==1285
    assert code['zh'][31][1].splitlines()==names[1123:]
    book_names=[line for _,block in code['zh'] for line in block.splitlines()
                if line.startswith('UEOTQM.')]
    assert book_names==names
    report={'schema':'ueot_physics.bilingual_fidelity.v1','status':'PASS',
            'executed_at_utc':datetime.now(timezone.utc).isoformat(),
            'source_sha256':{k:sha(v.encode()) for k,v in sources.items()},
            'chapters_per_language':67,'appendices_per_language':6,
            'main_numbered_sections_per_language':367,'all_numbered_sections_per_language':393,
            'stable_anchors_per_language':246,'stable_result_count':173,
            'historical_numbered_result_objects_preserved':True,'numbering_migrations':[],
            'display_math':{'blocks_per_language':726,'byte_identical':715,
                            'exact_linguistic_substitutions':changes,'unexplained_differences':[]},
            'code_blocks':{'per_language':32,'bilingual_byte_identical':True,
                           'changed_from_prior_edition_zero_based_indices':old_code_diffs,
                           'historical_executable_code_and_audit_list':'unchanged',
                           'non_scientific_changes':['chapter 48 displayed publication-maintenance YAML','Appendix E bilingual build commands'],
                           'new_block':'162 v31.10 audit names copied exactly; full 1285-name inventory bound to current AxiomAudit.lean'},
            'result_map':rows,'inline_math_receipt':'INLINE_MATH_FIDELITY.json',
            'limits':'This verifies textual/algebraic fidelity and identities, not natural truth, novelty, all prose semantics, new Lean execution, or new hardware data.'}
    args.output.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    text=['# Stable result mapping / 稳定结果双语映射','',
          'Derived from the two complete books and `CHAPTER_DOSSIER.json`. All 173 inherited IDs and their dossier claim objects are preserved; there are no numbering migrations. This index makes no new claim of originality or experimental confirmation.','',
          f"Chinese SHA-256: `{report['source_sha256']['zh']}`  ",
          f"English SHA-256: `{report['source_sha256']['en']}`",'',
          '| Stable ID | Chapter | 中文标题 | English title |','|---|---:|---|---|']
    for row in rows:
        z=row['zh_title'].replace('|',r'\|');e=row['en_title'].replace('|',r'\|')
        text.append(f"| [{row['id']}](UEOT_PHYSICS.md#{row['anchor']}) / [EN](UEOT_PHYSICS.en.md#{row['anchor']}) | {row['chapter']} | {z} | {e} |")
    args.map_output.write_text('\n'.join(text)+'\n')
    print(json.dumps({k:report[k] for k in ['status','chapters_per_language','stable_result_count','numbering_migrations']}))


if __name__ == '__main__':
    main()
