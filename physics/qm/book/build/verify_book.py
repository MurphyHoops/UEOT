#!/usr/bin/env python3
"""Check the complete book and bind registry rows to actual theorem anchors.

A valid URL is insufficient: a short ID must not be parsed from the suffix
of another result, e.g. C-01 inside K-QEC-01. Anchor identity is authoritative.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re


def actual_claims(source):
    body = source.split('<a id="appendix-a"></a>', 1)[0]
    lines = body.splitlines()
    chapter = None
    claims = []
    for i, line in enumerate(lines):
        heading = re.fullmatch(r'# (\d+)\. .+', line)
        if heading:
            chapter = int(heading.group(1))
        anchor = re.fullmatch(r'<a id="([a-z0-9-]+)"></a>', line)
        if not anchor or anchor.group(1).startswith('ch-'):
            continue
        name = anchor.group(1).upper()
        next_line = next((text for text in lines[i+1:] if text.strip()), '')
        title = re.match(r'\*\*(.+?)\*\*', next_line)
        if not title or not re.match(re.escape(name)+r'(?=$|[^A-Za-z0-9_-])', title.group(1)):
            raise ValueError(f'Anchor {name} does not precede its own numbered statement')
        claims.append({'id': name, 'chapter': chapter, 'title': title.group(1)})
    return claims


def inspect_book(source):
    anchors = re.findall(r'<a id="([^"]+)"></a>', source)
    if len(anchors) != len(set(anchors)):
        raise ValueError('Duplicate stable anchors')
    appendix_headers = list(re.finditer(r'^# 附录 ([^\n]*)$', source, re.M))
    appendix_letters = []
    for header in appendix_headers:
        label = re.fullmatch(r'([A-Z])\. .+', header.group(1))
        if not label:
            raise ValueError('Malformed appendix header: '+header.group(0))
        appendix_letters.append(label.group(1))
    if appendix_letters != list('ABCDEF'):
        raise ValueError('Expected ordered appendix headers A–F; got '+repr(appendix_letters))
    appendix_anchors = [name for name in anchors if name.startswith('appendix-')]
    expected_appendix_anchors = ['appendix-'+letter.lower() for letter in 'ABCDEF']
    if appendix_anchors != expected_appendix_anchors:
        raise ValueError('Expected ordered appendix anchors appendix-a through appendix-f; got '
                         +repr(appendix_anchors))
    for header, anchor in zip(appendix_headers, expected_appendix_anchors):
        preceding_lines = source[:header.start()].rstrip().splitlines()
        preceding_line = preceding_lines[-1] if preceding_lines else ''
        if preceding_line != f'<a id="{anchor}"></a>':
            raise ValueError(f'Appendix header {header.group(1)!r} must immediately follow '
                             f'its matching stable anchor {anchor!r} (blank lines allowed)')
    targets = re.findall(r'\]\(#([^)]*)\)', source)
    if set(targets)-set(anchors):
        raise ValueError('Unresolved internal targets: '+str(set(targets)-set(anchors)))
    chapters = [int(n) for n in re.findall(r'^# (\d+)\.', source, re.M)]
    if chapters != list(range(57)):
        raise ValueError('Expected complete chapters 0–56')
    sections = re.findall(r'^## (\d+\.\d+)\b', source, re.M)
    if len(sections) != len(set(sections)):
        raise ValueError('Duplicate numbered sections')
    claims = actual_claims(source)
    rows = re.findall(r'^\| \[([^\]]+)\]\(#([^)]*)\) \| (\d+) \| (.+) \|$',
                      source.split('# 附录 B.', 1)[1].split('<a id="appendix-c">', 1)[0], re.M)
    expected = [(x['id'], x['id'].lower(), str(x['chapter']), x['title']) for x in claims]
    if rows != expected:
        differences = [{'actual': a, 'expected': b} for a, b in zip(rows, expected) if a != b]
        raise ValueError('Result registry identity mismatch: '+repr(differences[:8]))
    if len(claims) != 117:
        raise ValueError('This edition requires all 101 inherited and 16 new result IDs')
    return {'schema': 'ueot_physics.book_structure.v1', 'status': 'PASS',
            'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
            'chapters': len(chapters), 'appendices': len(appendix_headers),
            'appendix_letters': appendix_letters, 'appendix_anchors_bound_to_headers': True,
            'numbered_sections': len(sections), 'stable_anchors': len(anchors),
            'numbered_results': len(claims), 'registry_rows_bound_to_actual_anchors': True,
            'internal_links_valid': True, 'claims': claims}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=Path(__file__).resolve().parents[1]/'UEOT_PHYSICS.md')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    receipt = inspect_book(args.source.read_text())
    if args.output:
        args.output.write_text(json.dumps(receipt, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k != 'claims'}, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
