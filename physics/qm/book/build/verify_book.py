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
    targets = re.findall(r'\]\(#([^)]*)\)', source)
    if set(targets)-set(anchors):
        raise ValueError('Unresolved internal targets: '+str(set(targets)-set(anchors)))
    chapters = [int(n) for n in re.findall(r'^# (\d+)\.', source, re.M)]
    if chapters != list(range(51)):
        raise ValueError('Expected complete chapters 0–50')
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
    if len(claims) != 88:
        raise ValueError('This edition requires all 78 inherited and 10 new result IDs')
    return {'schema': 'ueot_physics.book_structure.v1', 'status': 'PASS',
            'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
            'chapters': len(chapters), 'appendices': len(re.findall(r'^# 附录 ', source, re.M)),
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
