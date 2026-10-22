#!/usr/bin/env python3
"""Run the unchanged complete baseline parser regression suite once.

All raw subprocess bytes and the exact executable command are retained.
This wrapper does not filter, skip, rewrite, or modify any test.
"""
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import time

BASE = 'd503586107974c56e0773b4ea106b41a7d144b43'
REPO = Path('/workspace/scratch/534b0448126c/ueot-core-next')
OUT = Path(__file__).resolve().parent
PREFIX = 'formalization/ueot-core/docs/compression/theory_completion/'
TEST = PREFIX + 'knowledge/reuse/test_pr_preflight.py'
INPUTS = (
    TEST,
    PREFIX + 'knowledge/reuse/pr_preflight.py',
    PREFIX + 'knowledge/fkrg.py',
    PREFIX + 'unified_closure/audit_umc_local.py',
)


def digest(raw):
    return sha256(raw).hexdigest()


def utc():
    return datetime.now(timezone.utc).isoformat()


def main():
    if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
        raise RuntimeError('NORMAL_UNOPTIMIZED_PYTHON_REQUIRED')
    outputs = [OUT / name for name in ('STDOUT.txt', 'STDERR.txt', 'COMMAND.json', 'RECEIPT.json')]
    if any(p.exists() for p in outputs):
        raise RuntimeError('REFUSE_TO_OVERWRITE_EXISTING_GATE_EXECUTION')
    resolved_base = subprocess.check_output(
        ['git', 'rev-parse', '--verify', BASE + '^{commit}'], cwd=REPO, text=True).strip()
    if resolved_base != BASE:
        raise RuntimeError('BASE_IDENTITY_MISMATCH')
    identities = []
    for relative in INPUTS:
        baseline = subprocess.check_output(['git', 'show', BASE + ':' + relative], cwd=REPO)
        current = (REPO / relative).read_bytes()
        if current != baseline:
            raise RuntimeError('IMMUTABLE_BASE_PARSER_INPUT_CHANGED: ' + relative)
        identities.append({'path': relative, 'baseline_sha256': digest(baseline),
                           'executed_sha256': digest(current), 'equal_to_base': True})
    argv = [sys.executable, str(REPO / TEST)]
    command = {'argv': argv, 'display': shlex.join(argv), 'cwd': str(REPO),
               'shell': False, 'test_selection_or_filters': None,
               'python_version': sys.version, 'python_executable_realpath': str(Path(sys.executable).resolve()),
               'python_optimization': sys.flags.optimize,
               'baseline_ref': BASE, 'inputs': identities,
               'wrapper_sha256': digest(Path(__file__).read_bytes())}
    (OUT / 'COMMAND.json').write_text(json.dumps(command, indent=2) + '\n')
    started_utc = utc()
    started = time.perf_counter()
    process = subprocess.run(argv, cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    seconds = time.perf_counter() - started
    finished_utc = utc()
    (OUT / 'STDOUT.txt').write_bytes(process.stdout)
    (OUT / 'STDERR.txt').write_bytes(process.stderr)
    stderr = process.stderr.decode('utf-8', 'replace')
    match = re.search(r'^Ran (\d+) tests? in ([0-9.]+)s$', stderr, re.MULTILINE)
    ran = int(match.group(1)) if match else None
    skips = re.search(r'\bskipped=(\d+)', stderr)
    skipped = int(skips.group(1)) if skips else 0
    ok_lines = len(re.findall(r'\.\.\. ok$', stderr, re.MULTILINE))
    inputs_stable = all(digest((REPO / row['path']).read_bytes()) == row['executed_sha256']
                        for row in identities)
    passed = (process.returncode == 0 and ran == 89 and skipped == 0 and ok_lines == 89
              and re.search(r'^OK\s*$', stderr, re.MULTILINE) is not None and inputs_stable)
    receipt = {
        'schema': 'PATH_REALIZATION_IMMUTABLE_BASE_PARSER_GATE_V1',
        'status': 'PASS' if passed else 'FAIL',
        'baseline_ref': BASE,
        'command': command,
        'command_file_sha256': digest((OUT / 'COMMAND.json').read_bytes()),
        'started_utc': started_utc,
        'finished_utc': finished_utc,
        'elapsed_seconds': seconds,
        'exit_code': process.returncode,
        'unittest_ran_count': ran,
        'unittest_reported_seconds': float(match.group(2)) if match else None,
        'unittest_success_lines': ok_lines,
        'unittest_skipped_count': skipped,
        'input_bytes_equal_to_baseline_before_execution': True,
        'input_bytes_stable_after_execution': inputs_stable,
        'stdout_path': 'STDOUT.txt', 'stdout_sha256': digest(process.stdout),
        'stderr_path': 'STDERR.txt', 'stderr_sha256': digest(process.stderr),
        'test_suite_modified_or_filtered': False,
        'live_overlay_dependent_gates_executed': False,
        'reuse_rule': 'Reuse this exact completed local 89-test result later in this increment; do not rerun unless its immutable inputs or runtime assumptions change.',
    }
    (OUT / 'RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in (
        'status', 'baseline_ref', 'exit_code', 'elapsed_seconds', 'unittest_ran_count',
        'unittest_success_lines', 'unittest_skipped_count', 'input_bytes_stable_after_execution',
        'stdout_sha256', 'stderr_sha256')}))
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
