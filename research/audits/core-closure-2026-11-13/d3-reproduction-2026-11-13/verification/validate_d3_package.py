#!/usr/bin/env python3
"""Validate the staged D3 evidence package; no Lean or remote commands are run."""
from datetime import datetime, timezone
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import urllib.parse

PACKAGE = Path(__file__).resolve().parents[1]
REPO = Path(__file__).resolve().parents[5]
BASE = '6dd6a3bc13e26f41eddc10ee4d2f39fa1c8ab3d4'
PREFIX = PACKAGE.relative_to(REPO).as_posix() + '/'
MAC = Path('/Users/murphyhoops/Documents/ueot-core-audit-20261113')

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def read_json(path):
    return json.loads(path.read_text())

def git(*args, binary=False):
    return subprocess.check_output(['git', '-C', str(REPO), *args], text=not binary)

def main():
    changed = git('diff', '--cached', '--name-only', BASE).splitlines()
    require(changed, 'No staged evidence package')
    require(all(p == 'core/status/CURRENT.md' or p.startswith(PREFIX) for p in changed), 'Change escaped bounded package')
    current = REPO / 'core/status/CURRENT.md'
    old = git('show', BASE + ':core/status/CURRENT.md', binary=True)
    lines = current.read_bytes().splitlines(keepends=True)
    new_rows = [l for l in lines if l.startswith(b'| 2026-11-13 D3 targeted reproduction |')]
    require(len(new_rows) == 1 and b''.join(l for l in lines if l not in new_rows) == old,
            'Historical CURRENT content changed beyond one successor row')

    index = {}
    for row in git('ls-files', '--stage', '-z').split('\0'):
        if not row:
            continue
        header, path = row.split('\t', 1)
        mode, oid, stage = header.split()
        require(stage == '0', 'Unmerged index')
        index[path] = oid
    source_manifest = read_json(PACKAGE / 'verification/EXPECTED_SOURCE_BLOBS.json')
    source_mismatches = [p for p, oid in source_manifest['files'].items()
                         if index.get('formalization/ueot-core/' + p) != oid]
    require(len(source_manifest['files']) == 1055 and not source_mismatches, 'Current indexed proof source differs from executed manifest')

    storage = read_json(PACKAGE / 'evidence/TRANSFER_AND_STORAGE_MANIFEST.json')
    for row in storage['payloads']:
        data = (PACKAGE / 'evidence' / row['stored_path']).read_bytes()
        require(len(data) == row['stored_bytes'] and sha(data) == row['stored_sha256'], 'Stored payload mismatch: ' + row['stored_path'])
        raw = gzip.decompress(data) if row['gzip'] else data
        require(len(raw) == row['original_bytes'] and sha(raw) == row['original_sha256'], 'Original payload mismatch')
    require(len(storage['payloads']) == 57, 'Original payload inventory differs')
    receipt_paths = ['run-20261113T0920Z/D3_RECEIPT.json', 'run-20261113T0932Z/D3_RECEIPT.json',
                     'probe-continuation-20261113T0940Z/CONTINUATION_RECEIPT.json']
    receipts = [read_json(PACKAGE / 'evidence' / p) for p in receipt_paths]
    require(all(r['status'] == 'FAILED_OR_BLOCKED' for r in receipts), 'Original failed wrapper states must be preserved')
    log_count = 0
    for r in receipts:
        for step in r['steps']:
            local = PACKAGE / 'evidence' / Path(step['log']).relative_to(MAC)
            require(sha(local.read_bytes()) == step['log_sha256'], 'Raw log bytes changed')
            log_count += 1
    require(log_count == 35, 'Observed command-log inventory differs')
    modules = [s for s in receipts[1]['steps'] if 'module' in s]
    require(len(modules) == 15 and all(s['exit_code'] == 0 for s in modules), 'Expected source compilation missing')
    require(len(receipts[2]['steps']) == 2 and all(s['exit_code'] == 0 for s in receipts[2]['steps']), 'Final Lean query did not succeed')
    post = read_json(PACKAGE / 'evidence/FINAL_SOURCE_ARTIFACT_CHECK.json')
    require(post['source_and_config_files_unchanged'] == 1055 and post['source_module_artifacts_unchanged'] == 30,
            'Post-execution readback incomplete')
    require(post['old_target_cache'] == {'status': 'UNCHANGED', 'before_count': 63, 'after_count': 63, 'changes': []},
            'Old target cache preservation differs')

    parsed = read_json(PACKAGE / 'reviews/D3_OBSERVED_AXIOMS_AND_TYPES.json')
    require(parsed['status'] == 'PASS_STRICT_PARSING_AND_EVIDENCE_BINDING' and parsed['endpoint_count'] == 44,
            'Strict axiom review incomplete')
    require(parsed['mode_counts'] == {'fresh_recompiled': 37, 'fresh_probe_of_reused_olean': 7}, 'Endpoint evidence modes differ')
    require(parsed['disclosed_native_count'] == 2, 'Native dependency scope differs')
    require(parsed['parser_sha256'] == sha((PACKAGE / 'verification/parse_observed_axioms.py').read_bytes()), 'Parser identity differs')
    b = read_json(PACKAGE / 'reviews/D3_SEMANTIC_ENDPOINT_REVIEW.json')
    c = read_json(PACKAGE / 'reviews/C_D3_ACCEPTANCE_DETAILS.json')
    require(b['verdict'] == 'SUPPORT_TARGETED_D3_CLOSURE', 'B has not accepted scope')
    require(c['status'] == 'ACCEPT_D3_IN_DECLARED_TARGETED_EXECUTION_SCOPE' and not c['remaining_blocking_findings'], 'C blocking findings remain')
    require(b['report_sha256'] == sha((PACKAGE / 'reviews/B_D3_MATHEMATICAL_REVIEW.md').read_bytes()), 'B report identity differs')
    require(c['C_final_report_sha256'] == sha((PACKAGE / 'reviews/C_D3_EXECUTION_ACCEPTANCE.md').read_bytes()), 'C report identity differs')
    require((PACKAGE / 'reviews/A_D3_FINAL_TEXT_REVIEW.md').is_file(), 'A final text review absent')
    require(sha((PACKAGE / 'reviews/D3_OBSERVED_AXIOMS_AND_TYPES.json').read_bytes()) == c['B_result_sha256'], 'B/C results not cross-bound')
    governance = read_json(PACKAGE / 'evidence/GOVERNANCE_VALIDATION.json')
    require(governance['exit_code'] == 0, 'Repository governance check did not pass')
    require(sha((PACKAGE / 'evidence/GOVERNANCE_VALIDATION.log').read_bytes()) == governance['output_sha256'], 'Governance log identity differs')
    governance_source = git('show', BASE + ':formalization/ueot-core/scripts/validate_compression_research.py', binary=True)
    require(sha(governance_source) == governance['validator_source_sha256'], 'Governance validator differs from unchanged baseline')

    tracked = set(index)
    directories = {str(q) for p in tracked for q in PurePosixPath(p).parents if str(q) != '.'}
    checked_links = 0
    for rel in changed:
        if not rel.endswith('.md'):
            continue
        text = (REPO / rel).read_text()
        text = re.sub(r'```.*?```', '', text, flags=re.S)
        for target in re.findall(r'(?<!!)\[[^\]\n]+\]\(([^\s)]+)(?:\s+[^)]*)?\)', text):
            u = urllib.parse.urlsplit(target.strip('<>'))
            if u.scheme or u.netloc:
                continue
            p = urllib.parse.unquote(u.path)
            dest = os.path.normpath(str(PurePosixPath(rel).parent / p)) if p else rel
            require(dest in tracked or dest in directories, 'Unresolved relative link: ' + rel + ' -> ' + target)
            checked_links += 1

    preserved_probes = {
        PREFIX + 'verification/D3Probe.lean': 'a61ab3753293be95512136ae6eca13cc32ede7e56825f8f9b872177d71d913ea',
        PREFIX + 'verification/D3ProbeFinal.lean': '28c731287dc45ad7f7f6cbbdd67e011ef493614989da1462bf7f3135ed9bcb8c'
    }
    for rel, digest in preserved_probes.items():
        require(sha((REPO / rel).read_bytes()) == digest, 'Executed probe bytes changed')
    raw_check = subprocess.run(['git', '-C', str(REPO), 'diff', '--cached', '--check', BASE], capture_output=True, text=True)
    diagnostics = [x for x in raw_check.stdout.splitlines() if not x.startswith('+')]
    require(raw_check.returncode in (0, 2), 'Unexpected diff-check failure')
    for line in diagnostics:
        path = line.split(':', 1)[0]
        require(path in preserved_probes or path.startswith(PREFIX + 'evidence/') and path.endswith('.log') or
                path.startswith(PREFIX + 'verification/') and path.endswith('.diff'),
                'New non-evidence whitespace error: ' + line)
    strict = subprocess.run(['git', '-C', str(REPO), 'diff', '--cached', '--check', BASE, '--', '.',
                             ':(exclude)' + PREFIX + 'evidence/**', ':(exclude)' + PREFIX + 'verification/*.diff',
                             *[':(exclude)' + p for p in preserved_probes]],
                            capture_output=True, text=True)
    require(strict.returncode == 0, strict.stdout + strict.stderr)
    files = []
    for rel in changed:
        if rel == PREFIX + 'VALIDATION.json':
            continue
        data = (REPO / rel).read_bytes()
        require(git('show', ':' + rel, binary=True) == data, 'Index/worktree mismatch: ' + rel)
        files.append({'path': rel, 'bytes': len(data), 'sha256': sha(data), 'git_blob': index[rel]})
    result = {
        'status': 'PASS_TARGETED_D3_ACCEPTED', 'checked_utc': datetime.now(timezone.utc).isoformat(),
        'baseline_commit': BASE, 'executed_source_commit': receipts[1]['git_head'],
        'new_production_lean_theorems': 0, 'protected_sources_and_prior_audit_unchanged': True,
        'current_status_change': 'Exactly one successor evidence row; all historical text retained',
        'source_config_git_blobs_matched': 1055, 'source_compilations_exit_zero': 15,
        'final_probe_lean_exit_code': 0, 'actual_type_axiom_queries': 44,
        'endpoint_modes': parsed['mode_counts'], 'standard_only_endpoints': 42, 'disclosed_native_endpoints': 2,
        'definition_structure_queries': 12, 'raw_log_hashes_verified': log_count,
        'original_payloads_preserved': 57, 'gzip_storage_only': 'CACHE_MIRROR_MANIFEST.json',
        'original_failed_wrapper_states_preserved': True, 'full_clean_build': False,
        'native_numeric_computations_reexecuted': False, 'prior_A_freeze_scope_unchanged': True,
        'empirical_status': 'UNVERIFIED', 'relative_markdown_links_verified': checked_links,
        'unchanged_repository_governance_validator': 'PASS',
        'whitespace': {'authored_content': 'PASS', 'original_log_probe_and_patch_notes': diagnostics},
        'new_lean_execution_by_this_validator': False,
        'content_manifest_excluding_this_validation': files,
        'limits': ['Targeted source recompilation with dependency caches',
                   'Mac binary hashes measured by the lead; independent agents cross-bound returned records',
                   'Pretty-printer ellipses supplemented from exact bound sources',
                   'Original wrappers failed; successful constituent commands and reviewed postprocessing support this acceptance',
                   'No empirical or global-priority promotion', 'GitHub integration is a separate observed event']
    }
    (PACKAGE / 'VALIDATION.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('content_manifest_excluding_this_validation', 'whitespace')}, ensure_ascii=False, indent=2))

if __name__ == '__main__':
    main()
