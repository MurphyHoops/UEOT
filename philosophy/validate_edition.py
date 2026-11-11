#!/usr/bin/env python3
"""Validate the concrete bilingual edition, without claiming semantic/visual proof.

Requires PyMuPDF and Poppler pdffonts. No additional general software licence
is granted; historical and dependency terms remain in force (root LICENSE).
"""
from __future__ import annotations
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import fitz

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
REVIEW = HERE/'review/BILINGUAL_EDITION_2026-11-11'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    failures = []
    def check(ok, message):
        if not ok:
            failures.append(message)
        return bool(ok)

    report = {
        'edition': '3.0', 'scope': 'Reproducible structural and PDF checks only; actual page-image review and philosophical review are separate.',
        'documents': {}, 'protected_baseline_files': [],
    }
    manuscript_anchors = []
    manuscript_calls = []
    for lang, suffix in [('zh',''), ('en','.en')]:
        stem = HERE/('UEOT_PHILOSOPHY'+suffix)
        md, tex, pdf = [Path(str(stem)+ext) for ext in ('.md','.tex','.pdf')]
        text, latex = md.read_text(), tex.read_text()
        receipt = json.loads((HERE/('BUILD'+suffix+'.json')).read_text())
        hashes = {str(p.relative_to(REPO)):sha(p) for p in (md,tex,pdf)}
        for kind,p in [('source',md),('latex',tex),('pdf',pdf)]:
            check(receipt[kind+'_sha256']==sha(p), f'{lang}: build receipt differs for {kind}')
        for category in ('shared_inputs','edition_inputs'):
            for path,expected in receipt[category].items():
                check(sha(REPO/path)==expected, f'{lang}: build input changed: {path}')
        for field in ('overfull_hbox_warnings','overfull_vbox_warnings','undefined_reference_warnings'):
            check(receipt[field]==0, f'{lang}: nonzero {field}')

        anchors = re.findall(r'<a id="([^"]+)"',text)
        definitions = re.findall(r'^\[\^([^\]]+)\]:',text,re.M)
        nondefinitions = re.sub(r'^\[\^[^\]]+\]:.*$', '', text, flags=re.M)
        calls = re.findall(r'\[\^([^\]]+)\]',nondefinitions)
        parts = re.findall(r'^# (?:第.*?编|Part [IVX]+:)',text,re.M)
        chapters = re.findall(r'^## (?:第.*?章|Chapter \d+:)',text,re.M)
        appendices = re.findall(r'^# (?:附录|Appendix) [A-D]',text,re.M)
        check(len(parts)==6 and len(chapters)==30 and len(appendices)==4, f'{lang}: incomplete structure')
        check(len(anchors)==len(set(anchors))==47, f'{lang}: incorrect/duplicate anchors')
        check(len(definitions)==len(set(definitions))==68, f'{lang}: incorrect/duplicate notes')
        check(len(calls)==78 and set(calls)==set(definitions), f'{lang}: note call mismatch')
        check(latex.count('\\footnote{')==68, f'{lang}: typeset note definitions differ')
        check(len(re.findall(r'\\textsuperscript\{\\hyperlink\{ph-note-',latex))==10, f'{lang}: repeated-note backlinks differ')
        check(not re.search(r'(?im)\bTODO\b|\bPLACEHOLDER\b|待补全文|待译章节',text), f'{lang}: unfinished placeholder')
        manuscript_anchors.append(anchors)
        manuscript_calls.append(Counter(calls))

        doc=fitz.open(pdf)
        names=doc.resolve_names()
        toc=doc.get_toc()
        aux=HERE/'.build'/lang/sha(tex)[:16]/(stem.name+'.aux')
        aux_text=aux.read_text() if aux.exists() else ''
        label_targets={}
        for line in aux_text.splitlines():
            match=re.match(r'\\newlabel\{(ph-[^}]+)\}\{\{[^}]*\}\{[^}]*\}\{.*\}\{([^}]+)\}\{\}\}',line)
            if match:
                label_targets[match[1]]=match[2]
        check(len(toc)==47, f'{lang}: bookmark count')
        check(all(1<=row[2]<=len(doc) for row in toc), f'{lang}: invalid bookmark destination')
        for name in anchors+[f'ph-note-{n}' for n in range(1,69)]:
            target=name if name in names else label_targets.get(name,'')
            check(target in names and 0<=names[target].get('page',-1)<len(doc), f'{lang}: unresolved destination {name}')

        pages=[]
        link_counts=Counter()
        repeated_links=0
        font_xrefs=set()
        for index,page in enumerate(doc):
            spans=[s for b in page.get_text('dict')['blocks'] if 'lines' in b for line in b['lines'] for s in line['spans']]
            outside=[]
            for span in spans:
                x0,y0,x1,y1=span['bbox']
                if x0 < -0.5 or y0 < -0.5 or x1 > page.rect.width+0.5 or y1 > page.rect.height+0.5:
                    outside.append(span['text'][:80])
            check(not outside, f'{lang}: text outside page {index+1}: {outside}')
            check('\ufffd' not in page.get_text(), f'{lang}: replacement character on page {index+1}')
            links=page.get_links()
            for link in links:
                kind=link['kind'];link_counts[str(kind)]+=1
                if kind in (fitz.LINK_GOTO,fitz.LINK_NAMED):
                    check(0<=link.get('page',-1)<len(doc), f'{lang}: unresolved internal link on page {index+1}')
                elif kind==fitz.LINK_URI:
                    check(link.get('uri','').startswith(('https://','http://')), f'{lang}: non-web URI on page {index+1}')
                else:
                    check(False, f'{lang}: unexpected file/external action on page {index+1}: {kind}')
                if link.get('nameddest','').startswith('ph-note-'):
                    repeated_links+=1
            font_xrefs.update(f[0] for f in page.get_fonts(full=True))
            label=page.get_label()
            footer=[s['text'].strip() for s in spans if s['bbox'][1]>page.rect.height-65]
            if index>0:
                check(label in footer, f'{lang}: footer/label mismatch on page {index+1}: {label}, {footer}')
            pages.append({'physical_page':index+1,'printed_label':label,'text_characters':len(page.get_text()),'outside_page':outside,'links':len(links)})
        check(repeated_links==10, f'{lang}: expected ten repeated-note PDF links, found {repeated_links}')
        fonts=[]
        for xref in sorted(font_xrefs):
            name,ext,kind,data=doc.extract_font(xref)
            check(bool(data), f'{lang}: font not embedded: {name}')
            fonts.append({'xref':xref,'name':name,'extension':ext,'type':kind,'embedded_bytes':len(data)})
        font_table=subprocess.check_output(['pdffonts',str(pdf)],text=True)
        report['documents'][lang]={
            'hashes':hashes,'parts':len(parts),'chapters':len(chapters),'appendices':len(appendices),
            'anchors':len(anchors),'note_definitions':len(definitions),'note_calls':len(calls),
            'typeset_complete_notes':68,'repeated_note_backlinks':repeated_links,
            'physical_pages':len(doc),'bookmarks':toc,'resolved_book_anchor_and_note_destinations':115,
            'latex_label_to_pdf_destination':label_targets,
            'page_labels':doc.get_page_labels(),'links_by_kind':dict(link_counts),
            'fonts':fonts,'poppler_pdffonts':font_table,'pages':pages,
        }

    check(manuscript_anchors[0]==manuscript_anchors[1],'Bilingual anchor order differs')
    check(manuscript_calls[0]==manuscript_calls[1],'Bilingual note-call identities differ')
    baseline=json.loads((REVIEW/'BASELINE.json').read_text())
    mutable={'philosophy/UEOT_PHILOSOPHY.md','philosophy/UEOT_PHILOSOPHY.tex','philosophy/UEOT_PHILOSOPHY.pdf','philosophy/BUILD.json','philosophy/PUBLICATION_RIGHTS.md'}
    for entry in baseline['files']:
        if entry['path'] in mutable:
            continue
        actual=sha(REPO/entry['path'])
        ok=check(actual==entry['sha256'], f"Protected baseline file changed: {entry['path']}")
        report['protected_baseline_files'].append({'path':entry['path'],'sha256':actual,'unchanged':ok})
    manifest=HERE/'EDITION_MANIFEST.json'
    if manifest.exists():
        for item in json.loads(manifest.read_text())['book_files']:
            check(sha(REPO/item['path'])==item['sha256'],f"Manifest hash differs: {item['path']}")
        report['manifest_checked']=True
    else:
        report['manifest_checked']=False
    report['failures']=failures
    report['status']='PASS_MACHINE_CHECKS_ONLY' if not failures else 'FAILED'
    out=REVIEW/'LAYOUT_VALIDATION.json'
    out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'physical_pages':{k:v['physical_pages'] for k,v in report['documents'].items()},'failures':failures,'report':str(out.relative_to(REPO))},ensure_ascii=False,indent=2))
    raise SystemExit(bool(failures))

if __name__=='__main__':
    main()
