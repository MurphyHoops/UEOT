#!/usr/bin/env python3
"""Build the two mathematics editions without modifying other books' paths.

A complete XeLaTeX installation is normally sufficient. The optional
--runtime-dir is for the explicitly prepared, local minimal TeX runtime.
Compilation does not establish mathematical or empirical validity.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
CACHE = HERE / '.cache'
spec = importlib.util.spec_from_file_location('ueot_original_books', REPO / 'tools/books/build_books.py')
shared = importlib.util.module_from_spec(spec)
spec.loader.exec_module(shared)


def run(command, env, log):
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open('wb') as stream:
        result = subprocess.run(command, cwd=REPO, env=env, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'Command failed ({result.returncode}): {log}')


def build(language, env, invocation):
    stem = 'UEOT_MATHEMATICS' + ('.en' if language == 'en' else '')
    source, tex, pdf = [REPO / 'mathematics' / (stem + suffix) for suffix in ('.md', '.tex', '.pdf')]
    if not source.is_file():
        raise RuntimeError(f'Missing complete manuscript: {source}')
    preamble = 'mathematics/tools/english-preamble.tex' if language == 'en' else 'tools/books/preamble.tex'
    input_paths = [source, HERE / 'print.lua', REPO / preamble,
                   Path(__file__).resolve(), REPO / 'tools/books/build_books.py']
    input_hashes = {path: shared.sha(path) for path in input_paths}
    command = [
        'pandoc', str(source.relative_to(REPO)), '--from=markdown+raw_tex', '--to=latex',
        '--standalone', '--top-level-division=chapter', '--toc', '--toc-depth=2',
        '--wrap=none', '--no-highlight', '--lua-filter=mathematics/tools/print.lua',
        '--include-in-header=' + preamble, '--variable=documentclass:book',
        '--variable=classoption:oneside', '--variable=fontsize:11pt',
        '--variable=geometry:a4paper,left=24mm,right=24mm,top=25mm,bottom=25mm',
        '--variable=mainfont:DejaVuSerif.ttf',
        '--variable=mainfontoptions:BoldFont=DejaVuSerif-Bold.ttf,ItalicFont=DejaVuSerif-Italic.ttf,BoldItalicFont=DejaVuSerif-BoldItalic.ttf',
        '--variable=monofont:DejaVuSansMono.ttf',
        '--variable=monofontoptions:BoldFont=DejaVuSansMono-Bold.ttf,ItalicFont=DejaVuSansMono-Oblique.ttf,BoldItalicFont=DejaVuSansMono-BoldOblique.ttf',
        '--variable=CJKmainfont:NotoSerifCJKsc-Regular.otf',
        '--variable=CJKoptions:BoldFont=NotoSerifCJKsc-Bold.otf',
        '--variable=CJKoptions:AutoFakeSlant=0.15',
        '--variable=babel-lang:' + ('english' if language == 'en' else ''),
        '--variable=colorlinks:true', '--variable=linkcolor:MidnightBlue',
        '--variable=urlcolor:MidnightBlue', '--variable=toccolor:MidnightBlue',
        '--metadata=running-title:' + ('UEOT · Mathematics' if language == 'en' else 'UEOT · 数学著作'),
        '--metadata=ueot-book:mathematics', '--output=' + str(tex.relative_to(REPO)),
    ]
    work = CACHE / language
    run(command, env, work / 'pandoc.log')
    work = work / shared.sha(tex)[:16]
    work.mkdir(parents=True, exist_ok=True)
    for attempt in range(1, 4):
        run(['xelatex', '-interaction=nonstopmode', '-halt-on-error', '-file-line-error',
             '-output-directory=' + str(work), str(tex.relative_to(REPO))],
            env, work / f'xelatex-{attempt}.log')
    log = (work / (stem + '.log')).read_text(errors='replace')
    for defect in ['Missing character:', 'There were undefined references.', 'multiply defined']:
        if defect in log:
            raise RuntimeError(f'Unresolved PDF defect {defect!r}: {work / (stem + ".log")}')
    built = work / (stem + '.pdf')
    if not built.is_file() or built.stat().st_size < 1000:
        raise RuntimeError('No usable PDF was produced')
    changed_inputs = [str(path.relative_to(REPO)) for path, digest in input_hashes.items()
                      if shared.sha(path) != digest]
    if changed_inputs:
        raise RuntimeError('Inputs changed during compilation; discard this run: '
                           + ', '.join(changed_inputs))
    shutil.copyfile(built, pdf)
    info = subprocess.check_output(['pdfinfo', str(pdf)], text=True)
    pages = int(re.search(r'^Pages:\s+(\d+)', info, re.M).group(1))
    receipt = {
        'schema': 'ueot.mathematics.bilingual.build.v1', 'edition': '4.1', 'language': language,
        'status': 'COMPILED_REQUIRES_VISUAL_REVIEW',
        'source': str(source.relative_to(REPO)), 'source_sha256': shared.sha(source),
        'latex': str(tex.relative_to(REPO)), 'latex_sha256': shared.sha(tex),
        'pdf': str(pdf.relative_to(REPO)), 'pdf_sha256': shared.sha(pdf), 'pages': pages,
        'tools': {name: subprocess.check_output([name, '--version'], env=env, text=True).splitlines()[0]
                  for name in ('pandoc', 'xelatex')},
        'font_sha256': {name: data[1] for name, data in shared.FONTS.items()},
        'source_date_epoch': env['SOURCE_DATE_EPOCH'],
        'print_filter_sha256': shared.sha(HERE / 'print.lua'),
        'preamble_sha256': shared.sha(REPO / preamble),
        'build_script_sha256': input_hashes[Path(__file__).resolve()],
        'shared_builder_sha256': input_hashes[REPO / 'tools/books/build_books.py'],
        'overfull_hbox_warnings': log.count('Overfull \\hbox'),
        'overfull_vbox_warnings': log.count('Overfull \\vbox'),
        'undefined_references': False, 'missing_glyphs': False,
        'build_command': invocation,
        'scope': 'Actual document compilation only; visual, semantic, and Lean evidence are recorded separately.',
    }
    name = 'BUILD.en.json' if language == 'en' else 'BUILD.json'
    (REPO / 'mathematics' / name).write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('language', nargs='?', default='both', choices=['zh', 'en', 'both'])
    parser.add_argument('--font-dir', type=Path, default=REPO / 'tools/books/.cache/fonts')
    parser.add_argument('--download-fonts', action='store_true')
    parser.add_argument('--runtime-dir', type=Path, help='Prepared local tree containing texmf/ and xelatex.fmt')
    args = parser.parse_args()
    for tool in ('pandoc', 'xelatex', 'pdfinfo'):
        if not shutil.which(tool):
            parser.error(f'Required executable missing: {tool}')
    shared.CACHE.mkdir(parents=True, exist_ok=True)
    env = shared.font_environment(args.font_dir.resolve(), args.download_fonts)
    # Fixed edition date, separate from the unchanged legacy builder's epoch.
    env['SOURCE_DATE_EPOCH'] = '1794355200'  # 2026-11-11 00:00:00 UTC
    env['FORCE_SOURCE_DATE'] = '1'
    if args.runtime_dir:
        runtime = args.runtime_dir.resolve()
        if not (runtime / 'xelatex.fmt').is_file():
            parser.error('Prepare the local format before using --runtime-dir')
        env['TEXFORMATS'] = str(runtime) + '//:'
        # This explicit runtime option bypasses absent system ls-R databases.
        env['TEXMF'] = '{' + str(runtime / 'texmf') + ',/etc/texmf,/usr/share/texmf,/usr/share/texlive/texmf-dist}'
    import sys
    invocation = ['python3', 'mathematics/tools/build_bilingual.py', *sys.argv[1:]]
    for language in (['zh', 'en'] if args.language == 'both' else [args.language]):
        print(json.dumps(build(language, env, invocation), ensure_ascii=False), flush=True)


if __name__ == '__main__':
    main()
