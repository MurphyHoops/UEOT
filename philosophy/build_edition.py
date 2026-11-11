#!/usr/bin/env python3
"""Build the two philosophy volumes without changing shared book semantics.

Reuse tools/books font checks, process runner, print filter and preamble.
Only philosophy/ receives outputs and caches. No other book is compiled.
New code: no additional general software licence is granted; see root LICENSE.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
CACHE = HERE / '.build'
spec = importlib.util.spec_from_file_location('ueot_shared_books', REPO/'tools/books/build_books.py')
shared = importlib.util.module_from_spec(spec)
assert spec.loader
spec.loader.exec_module(shared)
shared.CACHE = CACHE
sha = shared.sha

def build(lang: str, env: dict[str,str]) -> dict:
    stem = 'UEOT_PHILOSOPHY' + ('.en' if lang == 'en' else '')
    source, tex, pdf = (HERE / (stem + suffix) for suffix in ('.md','.tex','.pdf'))
    source_hash = sha(source)
    shared_inputs = [REPO/'tools/books/build_books.py',REPO/'tools/books/print.lua',REPO/'tools/books/preamble.tex']
    edition_inputs = [Path(__file__),HERE/'edition.lua',HERE/'edition.layout.tex',HERE/'edition.en.tex']
    input_hashes = {str(p.relative_to(REPO)):sha(p) for p in shared_inputs+edition_inputs}
    work = CACHE / lang
    work.mkdir(parents=True, exist_ok=True)
    command = ['pandoc',str(source.relative_to(REPO)), '--from=markdown+raw_tex',
       '--to=latex','--standalone','--top-level-division=chapter', '--toc',
       '--toc-depth=2','--wrap=none','--no-highlight',
       '--lua-filter=tools/books/print.lua','--lua-filter=philosophy/edition.lua',
       '--include-in-header=tools/books/preamble.tex',
       '--include-in-header=philosophy/edition.layout.tex',
       '--variable=documentclass:book','--variable=classoption:oneside',
       '--variable=fontsize:11pt',
       '--variable=geometry:paperwidth=176mm,paperheight=250mm,left=23mm,right=23mm,top=24mm,bottom=24mm',
       '--variable=mainfont:DejaVuSerif.ttf',
       '--variable=mainfontoptions:BoldFont=DejaVuSerif-Bold.ttf,ItalicFont=DejaVuSerif-Italic.ttf,BoldItalicFont=DejaVuSerif-BoldItalic.ttf',
       '--variable=monofont:DejaVuSansMono.ttf',
       '--variable=monofontoptions:BoldFont=DejaVuSansMono-Bold.ttf,ItalicFont=DejaVuSansMono-Oblique.ttf,BoldItalicFont=DejaVuSansMono-BoldOblique.ttf',
       '--variable=CJKmainfont:NotoSerifCJKsc-Regular.otf',
       '--variable=CJKoptions:BoldFont=NotoSerifCJKsc-Bold.otf',
       '--variable=CJKoptions:AutoFakeSlant=0.15',
       '--variable=babel-lang:' + ('english' if lang=='en' else ''),
       '--variable=colorlinks:true','--variable=linkcolor:MidnightBlue',
       '--variable=urlcolor:MidnightBlue','--variable=toccolor:MidnightBlue',
       '--metadata=ueot-book:philosophy-bilingual',
       '--output='+str(tex.relative_to(REPO))]
    if lang=='en': command.insert(-1,'--include-in-header=philosophy/edition.en.tex')
    shared.run(command,env,work/'pandoc.log')
    work=work/sha(tex)[:16];work.mkdir(parents=True,exist_ok=True)
    for attempt in range(1,4):
        shared.run(['xelatex','-interaction=nonstopmode','-halt-on-error','-file-line-error',
                    '-output-directory='+str(work),str(tex.relative_to(REPO))],
                   env,work/f'xelatex-{attempt}.log')
    log=(work/(stem+'.log')).read_text(errors='replace')
    if 'Missing character:' in log: raise RuntimeError(f'Missing glyph in {lang}: {work}')
    generated=work/(stem+'.pdf')
    if not generated.exists() or generated.stat().st_size<1000: raise RuntimeError('PDF missing')
    if sha(source) != source_hash:
        raise RuntimeError('Source changed during compilation; freeze the text and rebuild before delivery.')
    if any(sha(REPO/key) != value for key,value in input_hashes.items()):
        raise RuntimeError('A build input changed during compilation; rebuild the frozen edition.')
    shutil.copyfile(generated,pdf)
    report={
        'document':'philosophy','language':lang,'edition':'3.0',
        'status':'COMPILED_REQUIRES_VISUAL_REVIEW',
        'source':str(source.relative_to(REPO)),'source_sha256':source_hash,
        'latex':str(tex.relative_to(REPO)),'latex_sha256':sha(tex),
        'pdf':str(pdf.relative_to(REPO)),'pdf_sha256':sha(pdf),
        'tools':{x:subprocess.check_output([x,'--version'],env=env,text=True).splitlines()[0] for x in ('pandoc','xelatex')},
        'font_sha256':{name:pair[1] for name,pair in shared.FONTS.items()},
        'overfull_hbox_warnings':log.count('Overfull \\hbox'),
        'overfull_vbox_warnings':log.count('Overfull \\vbox'),
        'undefined_reference_warnings':log.count('undefined references')+log.count('undefined on input'),
        'build_command':['python3','philosophy/build_edition.py',lang],
        'shared_inputs':{str(p.relative_to(REPO)):input_hashes[str(p.relative_to(REPO))] for p in shared_inputs},
        'edition_inputs':{str(p.relative_to(REPO)):input_hashes[str(p.relative_to(REPO))] for p in edition_inputs},
        'scope':'Document build only; semantic, scholarly and visual review are separately recorded.'
    }
    (HERE/('BUILD.en.json' if lang=='en' else 'BUILD.json')).write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    return report

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('language',choices=['zh','en','all'],default='all',nargs='?')
    parser.add_argument('--font-dir',type=Path,default=CACHE/'fonts')
    parser.add_argument('--download-fonts',action='store_true')
    parser.add_argument('--texmf',type=Path)
    parser.add_argument('--format-dir',type=Path)
    args=parser.parse_args()
    CACHE.mkdir(parents=True,exist_ok=True)
    env=shared.font_environment(args.font_dir.resolve(),args.download_fonts)
    env['SOURCE_DATE_EPOCH']=str(int(datetime(2026,11,11,tzinfo=timezone.utc).timestamp()))
    if args.texmf:env['TEXINPUTS']=str(args.texmf.resolve())+'//:'+env.get('TEXINPUTS','')
    if args.format_dir:env['TEXFORMATS']=str(args.format_dir.resolve())+'//:'+env.get('TEXFORMATS','')
    for lang in (['zh','en'] if args.language=='all' else [args.language]):
        print(json.dumps(build(lang,env),ensure_ascii=False),flush=True)

if __name__=='__main__':main()
