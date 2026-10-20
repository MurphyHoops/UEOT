#!/usr/bin/env python3
"""Compile the canonical complete UEOT physics source; never assemble old drafts.

Requirements: Pandoc, XeLaTeX, a CJK font, standard TeX packages. No shell escape.
Pass --font to a local CJK TrueType/OpenType file; otherwise install Noto Sans CJK SC.
Build receipts bind the actual Markdown, generated TeX, font (when supplied), and PDF.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

from verify_book import inspect_book


BOOK = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare_font(out, font):
    """Manage only the reserved font selected by header.tex in this output dir."""
    target = out / 'UEOT_CJK.ttf'
    if font is None:
        target.unlink(missing_ok=True)
        return None
    source = font.resolve(strict=True)
    if not source.is_file():
        raise ValueError(f'Font must be a file: {source}')
    if not (target.exists() and source.samefile(target)):
        # Unlink the owned entry so a previous symlink cannot redirect the copy.
        target.unlink(missing_ok=True)
        shutil.copy2(source, target)
    return {'sha256': digest(target), 'bytes': target.stat().st_size}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=BOOK / 'UEOT_PHYSICS.md')
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--font', type=Path)
    args = parser.parse_args()
    source = args.source.resolve()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    raw = source.read_text(encoding='utf-8')
    inspect_book(raw)
    anchors = re.findall(r'<a id="([^"]+)"></a>', raw)
    targets = re.findall(r'\]\(#([^)]*)\)', raw)
    if len(anchors) != len(set(anchors)):
        raise ValueError('Duplicate stable anchors')
    if set(targets) - set(anchors):
        raise ValueError(f'Unresolved internal targets: {set(targets)-set(anchors)}')
    chapters = re.findall(r'^# (\d+)\. (.+)$', raw, re.M)
    if [int(n) for n, _ in chapters] != list(range(51)):
        raise ValueError('Expected the complete consecutive chapters 0–50')
    if re.search(r'\b(TODO|PLACEHOLDER)\b', re.sub(r'(?ms)^~~~.*?^~~~\s*$', '', raw)):
        raise ValueError('Unresolved authoring placeholder')

    # The PDF has a generated chapter TOC instead of the Markdown navigation list.
    first = raw.index('<a id="ch-0"></a>')
    meta_end = raw.index('\n---', 4) + len('\n---')
    printable = raw[:meta_end] + '\n\n' + raw[first:]
    printable = re.sub(r'<a id="([^"]+)"></a>\s*\n(# [^\n]+)', r'\2 {#\1}', printable)
    printable = re.sub(r'<a id="([^"]+)"></a>', r'[]{#\1}', printable)
    printable = printable.replace('∎', r'$\square$')
    print_source = out / 'UEOT_PHYSICS.print.md'
    print_source.write_text(printable, encoding='utf-8')
    tex = out / 'UEOT_PHYSICS.tex'
    cmd = ['pandoc', str(print_source), '-f', 'markdown+tex_math_dollars', '-t', 'latex',
           '--standalone', '--top-level-division=chapter', '--toc', '--toc-depth=1',
           '--lua-filter', str(BOOK / 'build/tables.lua'), '--no-highlight',
           '-V', 'documentclass=book', '-V', 'classoption=oneside', '-V', 'fontsize=11pt',
           '-V', 'geometry=a4paper,top=23mm,bottom=23mm,left=23mm,right=23mm',
           '-V', 'colorlinks=true', '-V', 'linkcolor=teal', '-V', 'urlcolor=teal',
           '-H', str(BOOK / 'build/header.tex'), '-o', str(tex)]
    subprocess.run(cmd, check=True, capture_output=True, text=True)
    content = tex.read_text(encoding='utf-8')
    content = content.replace(r'\usepackage{unicode-math}',
                              '\\usepackage{mathtools}\n\\usepackage{unicode-math}')
    content = content.replace(r'\begin{verbatim}',
                              r'\begin{Verbatim}[breaklines,breakanywhere,fontsize=\scriptsize]')
    content = content.replace(r'\end{verbatim}', r'\end{Verbatim}')
    chunks = re.split(r'(\\begin\{Verbatim\}[\s\S]*?\\end\{Verbatim\})', content)
    for i in range(0, len(chunks), 2):
        chunks[i] = chunks[i].replace(r'\_', r'\_\allowbreak ')
        chunks[i] = chunks[i].replace(r'}、\texttt{', r'}、\allowbreak \texttt{')
    tex.write_text(''.join(chunks), encoding='utf-8')
    font_info = prepare_font(out, args.font)
    logs = []
    for attempt in range(3):
        result = subprocess.run(['xelatex', '-interaction=nonstopmode', '-halt-on-error',
                                 '-no-shell-escape', tex.name], cwd=out,
                                capture_output=True, text=True)
        log = out / f'xelatex-pass-{attempt+1}.log'
        log.write_text(result.stdout + result.stderr, encoding='utf-8')
        logs.append({'file': log.name, 'exit_code': result.returncode, 'sha256': digest(log)})
        if result.returncode:
            raise RuntimeError(f'XeLaTeX failed; inspect {log}')
    pdf = out / 'UEOT_PHYSICS.pdf'
    final_log = (out / 'UEOT_PHYSICS.log').read_text(errors='replace')
    warnings = [line for line in final_log.splitlines()
                if any(word in line for word in ['Missing character:', 'Overfull', 'undefined'])]
    receipt = {'schema': 'ueot_physics.pdf_build.v1',
               'created_at_utc': datetime.now(timezone.utc).isoformat(),
               'source_name': source.name, 'source_sha256': digest(source),
               'tex_sha256': digest(tex), 'pdf_sha256': digest(pdf),
               'chapters': len(chapters), 'appendices': len(re.findall(r'^# 附录 ', raw, re.M)),
               'internal_links_valid': True, 'font': font_info, 'compile_passes': logs,
               'layout_warnings': warnings,
               'visual_review': 'REQUIRED_AFTER_BUILD'}
    (out / 'pdf-build.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps(receipt, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
