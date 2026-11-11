#!/usr/bin/env python3
"""Compile the canonical complete UEOT physics source; never assemble old drafts.

Requirements: Pandoc, XeLaTeX, a CJK font, standard TeX packages. No shell escape.
Pass --font to a local CJK TrueType/OpenType file; otherwise install Noto CJK fonts.
Build receipts bind the actual Markdown, generated TeX, selected fonts, and PDF.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
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
        fonts = []
        for family in ('Noto Serif CJK SC', 'Noto Serif CJK SC:style=Bold',
                       'Noto Sans CJK SC', 'Noto Sans CJK SC:style=Bold', 'DejaVu Serif',
                       'Latin Modern Roman', 'Latin Modern Roman:style=Bold',
                       'Latin Modern Roman:style=Italic', 'Latin Modern Sans',
                       'Latin Modern Mono', 'DejaVu Sans Mono'):
            found = subprocess.run(['fc-match', '-f', '%{file}', family],
                                   check=True, capture_output=True, text=True).stdout
            path = Path(found)
            if not path.is_file():
                raise ValueError(f'Cannot identify font file for {family}')
            fonts.append({'family': family, 'path': str(path),
                          'sha256': digest(path), 'bytes': path.stat().st_size})
        return {'mode': 'fontconfig', 'files': fonts}
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
    english = source.name.endswith('.en.md')
    stem = 'UEOT_PHYSICS.en' if english else 'UEOT_PHYSICS'
    header = BOOK / ('build/header.en.tex' if english else 'build/header.tex')
    anchors = re.findall(r'<a id="([^"]+)"></a>', raw)
    targets = re.findall(r'\]\(#([^)]*)\)', raw)
    if len(anchors) != len(set(anchors)):
        raise ValueError('Duplicate stable anchors')
    if set(targets) - set(anchors):
        raise ValueError(f'Unresolved internal targets: {set(targets)-set(anchors)}')
    chapters = re.findall(r'^# (\d+)\. (.+)$', raw, re.M)
    if [int(n) for n, _ in chapters] != list(range(67)):
        raise ValueError('Expected the complete consecutive chapters 0–66')
    if re.search(r'\b(TODO|PLACEHOLDER)\b', re.sub(r'(?ms)^~~~.*?^~~~\s*$', '', raw)):
        raise ValueError('Unresolved authoring placeholder')

    # The PDF has a generated chapter TOC instead of the Markdown navigation list.
    first = raw.index('<a id="ch-0"></a>')
    meta_end = raw.index('\n---', 4) + len('\n---')
    printable = raw[:meta_end] + '\n\n' + raw[first:]
    printable = re.sub(r'<a id="([^"]+)"></a>\s*\n(# [^\n]+)', r'\2 {#\1}', printable)
    printable = re.sub(r'<a id="([^"]+)"></a>', r'[]{#\1}', printable)
    printable = printable.replace('∎', r'$\square$')
    print_source = out / f'{stem}.print.md'
    print_source.write_text(printable, encoding='utf-8')
    tex = out / f'{stem}.tex'
    # Canonical links use the explicit stable anchors checked above. Suppressing
    # unused automatic section labels also avoids a unicode-math/hyperref
    # catcode-only label comparison warning for Greek letters in headings.
    cmd = ['pandoc', str(print_source), '-f', 'markdown+tex_math_dollars-auto_identifiers', '-t', 'latex',
           '--standalone', '--top-level-division=chapter', '--toc', '--toc-depth=1',
           '--lua-filter', str(BOOK / 'build/tables.lua'), '--no-highlight',
           '-V', 'documentclass=book', '-V', 'classoption=oneside', '-V', 'fontsize=11pt',
           '-V', 'geometry=a4paper,top=23mm,bottom=23mm,left=23mm,right=23mm',
           '-V', 'colorlinks=true', '-V', 'linkcolor=teal', '-V', 'urlcolor=teal',
           '-H', str(header), '-o', str(tex)]
    subprocess.run(cmd, check=True, capture_output=True, text=True)
    content = tex.read_text(encoding='utf-8')
    content = content.replace(r'\usepackage{unicode-math}',
                              '\\usepackage{mathtools}\n\\usepackage{unicode-math}')
    content = content.replace(r'\begin{verbatim}',
                              r'\begin{Verbatim}[breaklines,breakanywhere,fontsize=\scriptsize]')
    content = content.replace(r'\end{verbatim}', r'\end{Verbatim}')
    if english:
        content = content.replace(
            r'(\text{quantum process},\text{object certificate},\text{evaluation bridge})'+'\n'+
            r'\longrightarrow V^*\longrightarrow\mathcal A^*\longrightarrow\text{typed long-term structure}.',
            '\\begin{gathered}\n'+
            r'(\text{quantum process},\text{object certificate},\text{evaluation bridge})\longrightarrow V^*\\'+'\n'+
            r'\longrightarrow\mathcal A^*\longrightarrow\text{typed long-term structure}.'+'\n'+
            r'\end{gathered}')
    chunks = re.split(r'(\\begin\{Verbatim\}[\s\S]*?\\end\{Verbatim\})', content)
    for i in range(0, len(chunks), 2):
        # Break long literal declaration/file names at readable component boundaries.
        def break_literal(match):
            original = match.group(1)
            if re.fullmatch(r'[0-9a-f]{40}|[0-9a-f]{64}', original):
                value = r'\allowbreak '.join(original[j:j+12] for j in range(0, len(original), 12))
                return r'\texttt{' + value + '}'
            value = re.sub(r'(?<=[a-z0-9])(?=[A-Z])', lambda _: r'\allowbreak ', original)
            value = value.replace('.', r'.\allowbreak ')
            value = value.replace('/', r'/\allowbreak ')
            value = value.replace('-', r'-\allowbreak ')
            return r'\texttt{' + value + '}'
        chunks[i] = re.sub(r'\\texttt\{([^{}]*)\}', break_literal, chunks[i])
        chunks[i] = chunks[i].replace(r'\_', r'\_\allowbreak ')
        chunks[i] = chunks[i].replace(r'}、\texttt{', r'}、\allowbreak \texttt{')
        # Permit line breaks in long exact hashes without altering canonical text.
        chunks[i] = re.sub(r'\\texttt\{([0-9a-f]{64})\}',
                           lambda m: r'\texttt{' + r'\allowbreak '.join(
                               m.group(1)[j:j+16] for j in range(0, 64, 16)) + '}',
                           chunks[i])
        # The inherited embedded-program hashes are plain text, not inline code.
        chunks[i] = re.sub(r'(代码SHA-256：)([0-9a-f]{64})',
                           lambda m: m.group(1) + r'\allowbreak '.join(
                               m.group(2)[j:j+16] for j in range(0, 64, 16)), chunks[i])
        chunks[i] = re.sub(r'(?<![0-9a-f])([0-9a-f]{40}|[0-9a-f]{64})(?![0-9a-f])',
                           lambda m: r'\allowbreak '.join(
                               m.group(1)[j:j+16] for j in range(0, len(m.group(1)), 16)), chunks[i])
    tex.write_text(''.join(chunks), encoding='utf-8')
    font_info = prepare_font(out, args.font)
    logs = []
    for attempt in range(3):
        result = subprocess.run(['xelatex', '-interaction=nonstopmode', '-halt-on-error',
                                 '-no-shell-escape', tex.name], cwd=out,
                                capture_output=True, text=True)
        log = out / f'xelatex-pass-{attempt+1}.log'
        log.write_text(result.stdout + result.stderr, encoding='utf-8')
        auxiliary = {suffix: digest(out / f'{stem}.{suffix}') for suffix in ('aux', 'toc')
                     if (out / f'{stem}.{suffix}').exists()}
        logs.append({'file': log.name, 'exit_code': result.returncode, 'sha256': digest(log),
                     'auxiliary_sha256': auxiliary})
        if result.returncode:
            raise RuntimeError(f'XeLaTeX failed; inspect {log}')
    pdf = out / f'{stem}.pdf'
    final_log = (out / f'{stem}.log').read_text(errors='replace')
    warnings = [line for line in final_log.splitlines()
                if any(word in line for word in ['Missing character:', 'Overfull', 'undefined'])]
    rerun_warnings = [line for line in final_log.splitlines()
                      if 'Warning:' in line and ('Rerun' in line or 'rerun' in line)]
    if source.read_text(encoding='utf-8') != raw:
        raise RuntimeError('The source changed during compilation; rebuild from a frozen manuscript')
    receipt = {'schema': 'ueot_physics.pdf_build.v2',
               'created_at_utc': datetime.now(timezone.utc).isoformat(),
               'source_name': source.name, 'source_sha256': digest(source),
               'tex_sha256': digest(tex), 'pdf_sha256': digest(pdf),
               'edition': '3.7', 'language': 'en' if english else 'zh-CN',
               'chapters': len(chapters), 'appendices': len(re.findall(r'^# (?:附录|Appendix) ', raw, re.M)),
               'internal_links_valid': True, 'font': font_info, 'compile_passes': logs,
               'builder_sha256': digest(Path(__file__)), 'header_sha256': digest(header),
               'tables_filter_sha256': digest(BOOK / 'build/tables.lua'),
               'texmf_search_override': os.environ.get('TEXMF'),
               'print_only_math_reflow': ['1.6 dependency chain, line break only'] if english else [],
               'explicit_stable_anchor_count': len(anchors),
               'unused_automatic_section_labels': 'disabled; all canonical explicit anchors retained',
               'layout_warnings': warnings,
               'rerun_warnings': rerun_warnings,
               'last_two_auxiliary_files_identical': logs[-1]['auxiliary_sha256'] == logs[-2]['auxiliary_sha256'],
               'visual_review': 'REQUIRED_AFTER_BUILD'}
    (out / 'pdf-build.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps(receipt, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
