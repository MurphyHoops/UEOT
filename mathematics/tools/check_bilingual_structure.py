#!/usr/bin/env python3
"""Compare mathematical-book structure without claiming semantic equivalence.

Usage:
  python3 check_bilingual_structure.py CHINESE.md ENGLISH.md --output report.json
  python3 check_bilingual_structure.py CHINESE.md ENGLISH.md \
      --whitelist explicit_pairs.json --output report.json --map-output sections.json

Only explicitly declared normalization is allowed: Unicode NFC, line-ending
normalization, insignificant whitespace outside math text commands, and exact
formula-text replacements listed in the whitelist. Fenced source code is exact
apart from line endings. Formula comparisons are ordered within each section.
"""
from __future__ import annotations
import argparse
import collections
import difflib
import hashlib
import json
import re
import sys
import unicodedata
from pathlib import Path

FENCE = re.compile(r"(?m)^[ \t]{0,3}(`{3,}|~{3,})([^\n]*)\n")
MATH = re.compile(r"(?<!\\)\$\$(.*?)\$\$|\\\[(.*?)\\\]|(?<![\\$])\$(?!\$)(.*?)(?<![\\$])\$(?!\$)|\\\((.*?)\\\)", re.S)
ANCHOR = re.compile(r'<a\s+id=["\']([^"\']+)["\'][^>]*>\s*</a>')
IDENTIFIER = re.compile(r'(?<![A-Za-z0-9_-])(?:P|K|D|H|E|N|O)-[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*(?![A-Za-z0-9_-])|(?<![A-Za-z0-9_-])M-(?:[A-Z]+-\d+|\d+(?:\.\d+)*)(?![A-Za-z0-9_-])')
LINK = re.compile(r'(?<!!)\[[^\]\n]*\]\(([^\s)]+)(?:\s+"[^"]*")?\)')
TEXT_COMMAND = re.compile(r'\\(?:text|textrm|textsf|texttt|mbox|operatorname)\*?\s*\{')
CHINESE_NUMBER = '一二三四五六七八九十'


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def normalized_file(path: Path) -> str:
    return unicodedata.normalize('NFC', path.read_text(encoding='utf-8').replace('\r\n', '\n').replace('\r', '\n'))


def extract_fences(text: str):
    """Recognize both Markdown fence styles, excluding code from other scans."""
    blocks, spans = [], []
    cursor = 0
    while m := FENCE.search(text, cursor):
        marker, info = m.group(1), m.group(2).strip()
        closing = re.compile(r'(?m)^[ \t]{0,3}' + re.escape(marker[0]) + '{' + str(len(marker)) + r',}[ \t]*$').search(text, m.end())
        if closing is None:
            raise ValueError(f'Unclosed fenced block at line {text.count(chr(10),0,m.start())+1}')
        blocks.append({'info': info, 'body': text[m.end():closing.start()], 'offset': m.start()})
        spans.append((m.start(), closing.end()))
        cursor = closing.end()
    masked = list(text)
    for a, b in spans:
        for i in range(a, b):
            if masked[i] != '\n':
                masked[i] = ' '
    return blocks, ''.join(masked)


def inline_codes(text: str):
    # Run lengths are respected; these books do not use multiline code spans.
    out = []
    pattern = re.compile(r'(`+)([^\n]*?)\1')
    for m in pattern.finditer(text):
        out.append(m.group(2))
    return out


def heading_id(title: str, unnumbered: int) -> str:
    app = re.match(r'(?:附录|Appendix)\s+([A-Z])(?:\b|[.、：:])', title)
    if app:
        return 'appendix-' + app.group(1).lower()
    numbered = re.match(r'(\d+(?:\.\d+)*|[A-Z](?:\.\d+)+)(?=[.、：:\s]|$)', title)
    if numbered:
        return numbered.group(1)
    return f'unnumbered-{unnumbered}'


def sections(text: str):
    fences, masked = extract_fences(text)
    hs, unnumbered = [], 0
    for m in re.finditer(r'(?m)^(#{1,6})\s+(.+?)\s*#*$', masked):
        title = m.group(2).strip()
        ident = heading_id(title, unnumbered)
        if ident.startswith('unnumbered-'):
            unnumbered += 1
        hs.append({'id': ident, 'level': len(m.group(1)), 'title': title, 'start': m.start(), 'body_start': m.end()})
    result = [{'id': 'frontmatter', 'level': 0, 'title': '', 'start': 0, 'body_start': 0}]
    result.extend(hs)
    for i, sec in enumerate(result):
        sec['end'] = result[i+1]['start'] if i+1 < len(result) else len(text)
        sec['body'] = text[sec['body_start']:sec['end']]
        sec['masked'] = masked[sec['body_start']:sec['end']]
        sec['fences'] = [f for f in fences if sec['body_start'] <= f['offset'] < sec['end']]
    return result


def math_normalize(expr: str, side: str, whitelist: dict) -> str:
    expr = unicodedata.normalize('NFC', expr)
    if side == 'zh':
        for pair in whitelist.get('formula_text_replacements', []):
            if not all(k in pair for k in ('zh', 'en', 'reason')):
                raise ValueError('Each formula replacement needs zh, en, and reason')
            expr = expr.replace(pair['zh'], pair['en'])
    # Preserve whitespace inside text-bearing braces; remove whitespace elsewhere.
    preserve = set()
    for m in TEXT_COMMAND.finditer(expr):
        depth, pos = 1, m.end()
        while pos < len(expr) and depth:
            if expr[pos] == '{' and (pos == 0 or expr[pos-1] != '\\'):
                depth += 1
            elif expr[pos] == '}' and (pos == 0 or expr[pos-1] != '\\'):
                depth -= 1
            preserve.add(pos)
            pos += 1
    # A space after a TeX control word can delimit its name.  For example,
    # ``\beta P`` must not normalize to the different token ``\betaP``.
    # Preserve one such delimiter while ignoring other layout whitespace.
    out, pos = [], 0
    while pos < len(expr):
        char = expr[pos]
        if not char.isspace() or pos in preserve:
            out.append(char)
            pos += 1
            continue
        end = pos + 1
        while end < len(expr) and expr[end].isspace() and end not in preserve:
            end += 1
        previous = ''.join(out)
        if (end < len(expr) and re.match(r'[A-Za-z]', expr[end])
                and re.search(r'\\[A-Za-z]+$', previous)):
            out.append(' ')
        pos = end
    return ''.join(out)


def formulae(text: str, side: str, whitelist: dict):
    out = []
    for m in MATH.finditer(text):
        group = next(i for i, g in enumerate(m.groups()) if g is not None)
        out.append(('display' if group < 2 else 'inline', math_normalize(m.group(group+1), side, whitelist)))
    return out


def reference_numbers(text: str):
    # Restrict to explicit cross-reference language, not decimal constants.
    out = []
    item = r'\d+(?:\.\d+)*(?:\s*[—–-]\s*\d+(?:\.\d+)*)?'
    separator = r'(?:\s*(?:、|，|,|;|；)\s*(?:(?:and|or)\s+)?|\s+(?:and|or|及|与|和)\s*)'
    items = item + r'(?:' + separator + item + r')*'
    patterns = [
        r'第\s*(' + items + r')\s*(?:章|节)',
        r'§§?\s*(' + items + r')',
        r'\b(?:Chapter|Chapters|Section|Sections)\s+(' + items + r')',
    ]
    for pattern in patterns:
        for m in re.finditer(pattern, text):
            for ref in re.findall(item, m.group(1)):
                out.append(re.sub(r'\s+', '', ref).replace('—','-').replace('–','-'))
    app_item = r'[A-F](?:\.\d+)*(?:\s*[—–-]\s*[A-F](?:\.\d+)*)?'
    app_items = app_item + r'(?:' + separator + app_item + r')*'
    for m in re.finditer(r'(?:附录\s*|\b(?:Appendix|Appendices)\s+)(' + app_items + r')', text):
        for ref in re.findall(app_item, m.group(1)):
            out.append(re.sub(r'\s+', '', ref).replace('—','-').replace('–','-'))
    return sorted(out)


def fingerprint(sec: dict, side: str, whitelist: dict):
    text = sec['masked']
    fm = formulae(text, side, whitelist)
    return {
        'formulas': fm,
        'display_count': sum(t == 'display' for t, _ in fm),
        'inline_count': sum(t == 'inline' for t, _ in fm),
        'proof_end': text.count('∎') + text.count('\\qed') + text.count('\\square'),
        'anchors': ANCHOR.findall(text),
        'identifiers': sorted(collections.Counter(x for x in IDENTIFIER.findall(text) if x != 'P-ID').items()),
        'inline_code': inline_codes(text),
        'fenced_code': [(f['info'], f['body']) for f in sec['fences']],
        'link_targets': LINK.findall(text),
        'cross_reference_numbers': reference_numbers(text),
        'paragraph_count': len([p for p in re.split(r'\n\s*\n', text) if p.strip()]),
    }


def compact_diff(a, b, limit=6):
    out = []
    for op,i,j,k,l in difflib.SequenceMatcher(None,a,b,autojunk=False).get_opcodes():
        if op != 'equal':
            out.append({'operation':op,'zh_range':[i,j],'en_range':[k,l],
                        'zh':a[i:j][:3],'en':b[k:l][:3]})
            if len(out) >= limit:
                break
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('chinese', type=Path)
    parser.add_argument('english', type=Path)
    parser.add_argument('--whitelist', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--map-output', type=Path)
    args = parser.parse_args()
    whitelist = json.loads(args.whitelist.read_text()) if args.whitelist else {}
    zh, en = normalized_file(args.chinese), normalized_file(args.english)
    a, b = sections(zh), sections(en)
    issues, warnings, coverage = [], [], []
    sa, sb = [(x['id'],x['level']) for x in a], [(x['id'],x['level']) for x in b]
    if sa != sb:
        issues.append({'check':'heading_identity_and_order','difference':compact_diff(sa,sb)})
    for n,(x,y) in enumerate(zip(a,b)):
        fa, fb = fingerprint(x,'zh',whitelist), fingerprint(y,'en',whitelist)
        row = {'section_id':x['id'],'zh_heading':x['title'],'en_heading':y['title'],
               'zh_body_sha256':sha(x['body']),'en_body_sha256':sha(y['body']),
               'zh_lines':[zh.count('\n',0,x['start'])+1, zh.count('\n',0,x['end'])+1],
               'en_lines':[en.count('\n',0,y['start'])+1, en.count('\n',0,y['end'])+1],
               'formula_count':[len(fa['formulas']),len(fb['formulas'])],
               'proof_end_count':[fa['proof_end'],fb['proof_end']],
               'paragraph_count':[fa['paragraph_count'],fb['paragraph_count']],
               'semantic_review':'NOT_ESTABLISHED_BY_THIS_CHECK'}
        for key in ('formulas','proof_end','anchors','identifiers','inline_code','fenced_code','link_targets'):
            if fa[key] != fb[key]:
                detail = compact_diff(fa[key],fb[key]) if isinstance(fa[key],list) else {'zh':fa[key],'en':fb[key]}
                issues.append({'section':x['id'],'check':key,'difference':detail})
        for key in ('cross_reference_numbers','paragraph_count'):
            if fa[key] != fb[key]:
                warnings.append({'section':x['id'],'check':key,'zh':fa[key],'en':fb[key],
                    'meaning':'Requires explicit human alignment; these diagnostics do not prove omission.'})
        coverage.append(row)
    all_anchors_a, all_anchors_b = ANCHOR.findall(extract_fences(zh)[1]), ANCHOR.findall(extract_fences(en)[1])
    if len(all_anchors_a)!=len(set(all_anchors_a)) or len(all_anchors_b)!=len(set(all_anchors_b)):
        issues.append({'check':'duplicate_explicit_anchor'})
    report = {'schema':'ueot.bilingual.structure.v1','status':'PASS_STRUCTURAL_ONLY' if not issues else 'FAIL',
        'chinese':str(args.chinese),'english':str(args.english),'chinese_sha256':sha(zh),'english_sha256':sha(en),
        'normalization':['Unicode NFC','LF line endings','whitespace outside math text commands',
                         'exact formula text replacements, if declared in attached whitelist'],
        'whitelist':whitelist,'heading_count':[len(a)-1,len(b)-1],
        'explicit_anchor_count':[len(all_anchors_a),len(all_anchors_b)],
        'hard_issue_count':len(issues),'issues':issues,'alignment_warning_count':len(warnings),'alignment_warnings':warnings,
        'limitations':['Not a proof of mathematical equivalence or complete prose translation.',
            'Unnumbered headings are aligned by order and level; titles need human review.',
            'Cross-reference prose and paragraph alignment are diagnostics requiring human review.',
            'Structural preservation can coexist with a mistranslated quantifier or omitted prose.'],
        'section_coverage':coverage}
    args.output.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    if args.map_output:
        args.map_output.write_text(json.dumps(coverage,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','heading_count','hard_issue_count','alignment_warning_count')},ensure_ascii=False))
    return 0 if not issues else 1


if __name__ == '__main__':
    sys.exit(main())
