#!/usr/bin/env python3
"""Check the three-pass Chapter 72 build and render pages for editorial inspection."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

from verify_book import inspect_book


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def verify(source, out):
    receipt = json.loads((out / 'pdf-build.json').read_text())
    stem = source.stem
    pdf = out / (stem + '.pdf')
    build = Path(__file__).resolve().parent
    suffix = '.en' if stem.endswith('.en') else ''
    for path, key in ((source, 'source'), (pdf, 'pdf'), (out / (stem + '.tex'), 'tex'),
                      (build / 'build_pdf.py', 'builder'), (build / f'header{suffix}.tex', 'header'),
                      (build / 'tables.lua', 'tables_filter')):
        require(sha(path) == receipt[key + '_sha256'], f'Build identity mismatch for {path.name}')
    require(receipt['language'] == ('en' if suffix else 'zh-CN') and receipt['edition'] == '3.13'
            and receipt['chapters'] == 73 and receipt['appendices'] == 6, 'Wrong reading edition')
    passes = receipt['compile_passes']
    require(len(passes) == 3 and receipt['last_two_auxiliary_files_identical'], 'Unstable three-pass build')
    for i, row in enumerate(passes, 1):
        require(row['exit_code'] == 0 and sha(out / f'xelatex-pass-{i}.log') == row['sha256'], f'Invalid pass {i}')
    require(not receipt['layout_warnings'] and not receipt['rerun_warnings'],
            f"Typesetting warnings: {receipt['layout_warnings'] + receipt['rerun_warnings']}")
    listing = subprocess.check_output(['pdfinfo', '-dests', str(pdf)], text=True)
    destinations = {name: int(page) for page, name in
                    re.findall(r'(?m)^\s*(\d+)\s+\[[^\n]*\]\s+"([^"]+)"', listing)}
    toc = (out / (stem + '.toc')).read_text()
    chapter_targets = re.findall(r'(?m)^\\contentsline\s*\{chapter\}.*?\{(chapter[^{}]+)\}\s*%?\s*$', toc)
    anchors = re.findall(r'(?m)^<a id="(ch-\d+|appendix-[a-f])"></a>$', source.read_text())
    require(len(chapter_targets) == len(anchors) == 79, 'Incomplete table of contents')
    for anchor, target in zip(anchors, chapter_targets):
        require(destinations[anchor] == destinations[target], 'PDF link lands on wrong page: ' + anchor)
    extracted = subprocess.check_output(['pdftotext', '-layout', str(pdf), '-']).decode()
    hyphens = str.maketrans({'\u2011': '-', '\u2010': '-', '\u2212': '-'})
    pages = [''.join(page.translate(hyphens).split()) for page in extracted.split('\f')]
    require('3.13' in pages[0] and '72' in pages[0], 'Missing edition or chapter credit on title page')
    claims = [r['id'] for r in inspect_book(source.read_text())['claims'] if r['chapter'] == 72]
    require(len(claims) == 19, 'Expected 19 Chapter 72 results')
    first_pages = [next(i for i, p in enumerate(pages, 1) if result in p) for result in claims]
    require(first_pages == sorted(first_pages), 'Chapter 72 result order in PDF')
    text = ''.join(pages[first_pages[0] - 1:first_pages[-1]])
    for value in ('2048/9375', '7/12', '0.153021391482', '2.829147', '3.197065', '0.467832', '0.467833', '83'):
        require(value in text, 'Missing legible bound ' + value)
    review = {1, *range(max(1, first_pages[0] - 1), min(len(pages), first_pages[-1] + 2) + 1)}
    for page in sorted(review):
        subprocess.run(['pdftoppm', '-f', str(page), '-l', str(page), '-singlefile', '-r', '100', '-png',
                        str(pdf), str(out / f'review-{page:04d}')], check=True)
    print(f'Checked printed Chapter 72 ({len(pages)} pages, 79 destinations) and rendered {len(review)} review pages.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output_dir', type=Path)
    args = parser.parse_args()
    verify(args.source, args.output_dir)
