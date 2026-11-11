#!/usr/bin/env python3
"""Small, reproducible mutation checks for the publication structure checker.

The semantic negative control intentionally passes: this is evidence of the
checker's limitation, not evidence that a changed quantifier is acceptable.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

ZH = r'''# 0. 入口

## 0.1 命题

<a id="p-test-01"></a>

**P-TEST-01.** 对每个输入，$a=b$；参见第 2、3、4 章。

$$\beta P=\text{成功}.$$

**证明。** 代入。∎

重要接口为 `actualKernel`，详见[下一节](#next)。

~~~python
assert 1 + 1 == 2
~~~

## 0.2 边界

范围仅限指定输入。
'''

EN = r'''# 0. Entry

## 0.1 Proposition

<a id="p-test-01"></a>

**P-TEST-01.** For every input, $a=b$; see Chapters 2, 3, and 4.

$$\beta P=\text{success}.$$

**Proof.** Substitute. ∎

The important interface is `actualKernel`; see [the next section](#next).

~~~python
assert 1 + 1 == 2
~~~

## 0.2 Boundary

The scope is restricted to the specified inputs.
'''


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--checker', type=Path, default=Path(__file__).with_name('check_bilingual_structure.py'))
    p.add_argument('--output', type=Path, default=Path(__file__).with_name('STRUCTURE_CHECK_VALIDATION.json'))
    args = p.parse_args()
    cases = [
        ('paired_baseline', EN, 0, None, False),
        ('wrong_formula', EN.replace('$a=b$', '$a=c$'), 1, 'formulas', False),
        ('tex_control_word_boundary', EN.replace(r'\beta P', r'\betaP'), 1, 'formulas', False),
        ('missing_proof_end', EN.replace('∎', ''), 1, 'proof_end', False),
        ('missing_number', EN.replace('## 0.1', '## 0.9'), 1, 'heading_identity_and_order', False),
        ('missing_section', EN[:EN.index('## 0.2')], 1, 'heading_identity_and_order', False),
        ('altered_code', EN.replace('assert 1 + 1 == 2', 'assert 1 + 1 == 3'), 1, 'fenced_code', False),
        ('altered_inline_code', EN.replace('`actualKernel`', '`otherKernel`'), 1, 'inline_code', False),
        ('missing_linked_reference', EN.replace('[the next section](#next)', 'the next section'), 1, 'link_targets', False),
        ('missing_theorem_id', EN.replace('P-TEST-01', 'P-TEST-02'), 1, 'identifiers', False),
        ('ordinary_cross_reference_changed', EN.replace('Chapters 2, 3, and 4', 'Chapters 2, 3, and 5'), 0, 'cross_reference_numbers', True),
        ('semantic_quantifier_change_outside_scope', EN.replace('For every input', 'For some input'), 0, None, False),
    ]
    results = []
    with tempfile.TemporaryDirectory(prefix='ueot-bilingual-check-') as temp:
        tmp = Path(temp)
        z, e, whitelist, report = [tmp/n for n in ('zh.md', 'en.md', 'whitelist.json', 'report.json')]
        z.write_text(ZH)
        whitelist.write_text(json.dumps({'formula_text_replacements': [
            {'zh': r'\text{成功}', 'en': r'\text{success}', 'reason': 'translation of a text label only'}
        ]}, ensure_ascii=False))
        for name, candidate, expected_rc, expected_check, warning in cases:
            e.write_text(candidate)
            proc = subprocess.run([sys.executable, str(args.checker), str(z), str(e), '--whitelist', str(whitelist), '--output', str(report)], capture_output=True, text=True)
            data = json.loads(report.read_text())
            found = [x['check'] for x in data['issues']]
            warned = [x['check'] for x in data['alignment_warnings']]
            correct = proc.returncode == expected_rc and (expected_check is None or expected_check in (warned if warning else found))
            results.append({'case': name, 'returncode': proc.returncode, 'expected': expected_rc, 'correct': correct, 'hard_checks': found, 'diagnostics': warned})
    result = {
        'checker_sha256': hashlib.sha256(args.checker.read_bytes()).hexdigest(),
        'all_expected_outcomes': all(x['correct'] for x in results),
        'results': results,
        'scope': 'Mutation tests of structure only. The last negative control deliberately demonstrates that prose quantifiers require mathematical review.'
    }
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps({'cases': len(results), 'all_expected_outcomes': result['all_expected_outcomes']}))
    raise SystemExit(0 if result['all_expected_outcomes'] else 1)


if __name__ == '__main__':
    main()
