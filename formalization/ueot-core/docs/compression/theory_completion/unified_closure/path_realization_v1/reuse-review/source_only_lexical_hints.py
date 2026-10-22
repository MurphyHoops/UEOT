#!/usr/bin/env python3
"""Prepare reproducible source-only reuse hints from an immutable Git baseline.

This does not run the integration protocol, freeze its inputs, elaborate Lean,
install an overlay, or certify the working tree's compiled proof graph.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import types

if not __debug__:
    raise RuntimeError('OPTIMIZED_PYTHON_DISABLES_REQUIRED_ASSERTIONS')

CORE = 'formalization/ueot-core/'
KNOWLEDGE = CORE + 'docs/compression/theory_completion/knowledge/'
REUSE = KNOWLEDGE + 'reuse/'
PACKET = CORE + 'docs/compression/theory_completion/unified_closure/'
NAMES = sorted((
    'C3ExecutableSearch', 'FiniteMemoryPhysicalSafety', 'FiniteMemoryRealization',
    'FiniteMemorySafetyWitness', 'FiniteWindowDoob', 'FiniteWindowDoobWitness',
    'SameSourceFiniteWindow',
))
NEW_PATHS = [CORE + 'UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/' + name + '.lean'
             for name in NAMES]


def require(condition, reason):
    if not condition:
        raise RuntimeError(reason)


def git(repo, *args):
    return subprocess.check_output(['git', *args], cwd=repo)


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


def source_fingerprint(data):
    digest = sha256()
    for path, raw in sorted(data.items(), key=lambda item: item[0][len(CORE):-5].replace('/', '.')):
        module = path[len(CORE):-5].replace('/', '.')
        digest.update(module.encode() + b'\0' + raw + b'\0')
    return digest.hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', required=True, type=Path)
    ap.add_argument('--base', required=True)
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    repo, out = args.repo.resolve(), args.output.resolve()
    require(not out.exists(), 'NEW_OUTPUT_DIRECTORY_REQUIRED')
    base = git(repo, 'rev-parse', '--verify', args.base + '^{commit}').decode().strip()

    immutable = []
    for path in (REUSE + 'fkrg_reuse.py', REUSE + 'pr_preflight.py', KNOWLEDGE + 'fkrg.py',
                 PACKET + 'audit_umc_local.py'):
        raw = git(repo, 'show', base + ':' + path)
        require((repo / path).read_bytes() == raw, 'IMMUTABLE_HELPER_DRIFT: ' + path)
        immutable.append({'path': path, 'sha256': sha256(raw).hexdigest()})

    consumer_path = REUSE + 'fkrg_reuse.py'
    consumer_source = git(repo, 'show', base + ':' + consumer_path)
    consumer = types.ModuleType('path_realization_immutable_baseline_consumer')
    consumer.__file__ = str(repo / consumer_path)
    sys.modules[consumer.__name__] = consumer
    exec(compile(consumer_source, consumer.__file__, 'exec'), consumer.__dict__)
    # Reconstruct only the explicitly immutable historical input. The current
    # source corpus is checked below; this is not a live freshness acceptance.
    prior = consumer.load(verify_source=False)
    require((len(prior['modules']), len(prior['graph']), len(prior['overlays'])) == (684, 4272, 10),
            'WRONG_IMMUTABLE_BASELINE_CENSUS')

    parser_path = repo / REUSE / 'pr_preflight.py'
    spec = importlib.util.spec_from_file_location('path_realization_immutable_source_parser', parser_path)
    parser = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = parser
    spec.loader.exec_module(parser)
    baseline = parser.corpus(repo, base)
    require(len(baseline) == 684, 'BASELINE_SOURCE_CENSUS_DRIFT')
    overrides = {}
    for overlay in prior['overlays']:
        overrides.update(overlay.get('source_hash_overrides', {}))
    require(set(baseline) == {row['path'] for row in prior['modules']}, 'BASELINE_SOURCE_SET_DRIFT')
    for row in prior['modules']:
        expected = overrides.get(row['path'], row['content_sha256'])
        require(sha256(baseline[row['path']].encode()).hexdigest() == expected,
                'BASELINE_SOURCE_HASH_DRIFT: ' + row['path'])
    baseline_declarations = [d for p, s in baseline.items() for d in parser.declarations(p, s)]
    baseline_names = parser.validate_unique(baseline_declarations, 'IMMUTABLE_BASELINE')
    require(set(baseline_names) == set(prior['graph']), 'BASELINE_PUBLIC_GRAPH_SET_DRIFT')

    core = repo / CORE
    current = {p.relative_to(repo).as_posix(): p.read_bytes()
               for p in [core / 'UEOT.lean', *(core / 'UEOT').rglob('*.lean')] if p.is_file()}
    require(len(current) == 691 and set(baseline) <= set(current), 'CURRENT_SOURCE_CENSUS_DRIFT')
    require(sorted(set(current) - set(baseline)) == sorted(NEW_PATHS), 'EXACT_SEVEN_MODULE_SCOPE_REQUIRED')
    root = CORE + 'UEOT/V3/Compression/TheoryCompletion.lean'
    changed_old = sorted(p for p, s in baseline.items() if current[p] != s.encode())
    require(set(changed_old) <= {root}, 'UNEXPECTED_OLD_SOURCE_CHANGE')
    if changed_old:
        old_lines, new_lines = baseline[root].splitlines(), current[root].decode().splitlines()
        require([line for line in new_lines if line in old_lines] == old_lines,
                'OLD_IMPORT_SEQUENCE_CHANGED')
        require(all(line.startswith('import UEOT.V3.Compression.TheoryCompletion.')
                    for line in new_lines if line not in old_lines), 'NON_IMPORT_ROOT_CHANGE')
    declarations = [d for p in NEW_PATHS for d in parser.declarations(p, current[p].decode())]
    names = parser.validate_unique(declarations, 'SEVEN_NEW_SOURCE_MODULES')
    require(not set(names) & set(baseline_names), 'PUBLIC_NAME_COLLISION')
    hints = [{**d, 'reuse_candidates': parser.candidate_hints(d, baseline_declarations)}
             for d in declarations]
    require(all((repo / p).read_bytes() == raw for p, raw in current.items()),
            'SOURCE_BYTES_CHANGED_DURING_PREPARATION')
    for row in immutable:
        require(sha256((repo / row['path']).read_bytes()).hexdigest() == row['sha256'],
                'HELPER_CHANGED_DURING_PREPARATION')

    hinted_names = {h['symbol'] for row in hints for h in row['reuse_candidates']}
    old_hinted = [d for d in baseline_declarations if d['symbol'] in hinted_names]
    hint_bytes = encoded(hints)
    old_bytes = encoded(old_hinted)
    receipt = {
        'schema': 'PATH_REALIZATION_SOURCE_ONLY_REUSE_HINTS_V1',
        'status': 'SOURCE_ONLY_HINTS_READY_SEMANTIC_REVIEW_REQUIRED_NATIVE_PENDING',
        'baseline_ref': base,
        'baseline_reconstruction': 'Exact Git-object consumer; immutable 684-module, 4272-public, 10-overlay input only. Not a current-source freshness certificate.',
        'immutable_helpers': immutable,
        'baseline_source_fingerprint': source_fingerprint({p: s.encode() for p, s in baseline.items()}),
        'baseline_module_count': len(baseline),
        'baseline_public_lexical_theorem_count': len(baseline_declarations),
        'baseline_registered_public_count': len(prior['graph']),
        'baseline_overlay_count': len(prior['overlays']),
        'current_complete_source_module_count': len(current),
        'current_complete_source_fingerprint': source_fingerprint(current),
        'old_source_changes': changed_old,
        'new_sources': [{'path': p, 'sha256': sha256(current[p]).hexdigest(),
                         'public_source_candidates': sum(d['path'] == p for d in declarations)}
                        for p in NEW_PATHS],
        'new_public_source_candidate_count': len(declarations),
        'nonempty_lexical_hint_group_count': sum(bool(row['reuse_candidates']) for row in hints),
        'old_candidate_pair_count': sum(len(row['reuse_candidates']) for row in hints),
        'unique_old_hinted_theorem_count': len(hinted_names),
        'lexical_reuse_hints_sha256': sha256(hint_bytes).hexdigest(),
        'hinted_baseline_declarations_sha256': sha256(old_bytes).hexdigest(),
        'preparation_script_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'all_current_source_bytes_stable_during_preparation': True,
        'native_export_executed': False,
        'protocol_inputs_frozen': False,
        'fixed_native_hashes_or_type_comparison_results': None,
        'git_object_candidate_preflight': False,
        'counted_ledger_promotion': 'NONE',
    }
    out.mkdir(parents=True)
    (out / 'LEXICAL_REUSE_HINTS.json').write_bytes(hint_bytes)
    (out / 'HINTED_BASELINE_DECLARATIONS.json').write_bytes(old_bytes)
    (out / 'SOURCE_ONLY_HINTS_RECEIPT.json').write_bytes(encoded(receipt))
    print(json.dumps({key: receipt[key] for key in (
        'status', 'baseline_ref', 'current_complete_source_module_count',
        'new_public_source_candidate_count', 'nonempty_lexical_hint_group_count',
        'old_candidate_pair_count', 'unique_old_hinted_theorem_count',
        'current_complete_source_fingerprint')}))


if __name__ == '__main__':
    main()
