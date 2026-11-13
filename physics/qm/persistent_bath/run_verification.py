#!/usr/bin/env python3
"""Replay the v31.14 finite scientific checks without altering authored evidence.

Production source layout: this script and A/B/C Python modules are flat in
physics/qm/persistent_bath. Historical evidence is in the sibling
kernel/evidence/v31.14/authored/{a,b,c}. No sample generation is invoked.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import importlib.util
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import time
import traceback


SOURCE_FILES = {
    'a': ('finite_operations.py', 'verify_a.py', 'review_b.py'),
    'b': ('dynamics.py', 'verify_dynamics.py', 'interval_certificate.py',
          'build_certificates.py', 'certify_memory_witness.py', 'physical_prediction.py'),
    'c': ('common_c.py', 'calibrate.py', 'generate_synthetic.py', 'interval_source.py',
          'verify_generation.py', 'evaluate_holdout.py', 'finalize_certificate.py',
          'reproduce_external_observable.py'),
}
C_INPUT_FILES = (
    'CALIBRATION_CONTRACT.json', 'FROZEN_CALIBRATION_IDENTITY.json',
    'FROZEN_HOLDOUT_PLAN.json', 'NOMINAL_MODEL.json', 'SYNTHETIC_TRUTH.json',
    'calibration_generation_receipt.json', 'holdout_generation_receipt.json',
    'calibration_shots.npz', 'holdout_shots.npz', 'EXTERNAL_OBSERVABLE_PLAN.json',
    'external/PROVENANCE.json', 'external/zhu_2025_processed_O.h5',
)
CALIBRATION_COMPARE_FIELDS = (
    'lambda_hat', 'eta_hat', 'lambda_projection_outer', 'eta_projection_outer',
    'nonempty_witness_interval_verified', 'alpha', 'counts', 'lambda_max_error',
    'eta_max_error', 'all_input_ideal_nominal_CQ_error_upper',
    'all_input_ideal_Galerkin_CQ_error_upper', 'fixed_tester_readout_error_addition',
)


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


def write_json(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def file_identity(path):
    return {'path': str(Path(path).resolve()), 'bytes': Path(path).stat().st_size,
            'sha256': digest(path)}


def git_context(directory):
    def get(*args):
        try:
            result = subprocess.run(['git', '-C', str(directory), *args],
                                    capture_output=True, text=True, check=False)
        except OSError as error:
            return {'returncode': 127, 'stdout': '', 'stderr': str(error)}
        return {'returncode': result.returncode, 'stdout': result.stdout.rstrip(),
                'stderr': result.stderr.rstrip()}
    root = get('rev-parse', '--show-toplevel')
    if root['returncode']:
        return {'available': False, 'reason': root}
    return {'available': True, 'repository_root': root['stdout'],
            'HEAD': get('rev-parse', 'HEAD')['stdout'],
            'HEAD_tree': get('rev-parse', 'HEAD^{tree}')['stdout'],
            'branch': get('rev-parse', '--abbrev-ref', 'HEAD')['stdout'],
            'status_porcelain': get('status', '--porcelain=v1', '--untracked-files=normal')['stdout']}


def choose_input(source_dir, authored_dir, role, name):
    """Contract inputs may be canonical; original receipts/data come from archive."""
    archived = authored_dir / role / name
    canonical = source_dir / name
    # Keep historical nominal, receipts, samples and external member identity.
    historical = name in {
        'FROZEN_CALIBRATION_IDENTITY.json', 'FROZEN_HOLDOUT_PLAN.json',
        'NOMINAL_MODEL.json', 'SYNTHETIC_TRUTH.json',
        'calibration_generation_receipt.json', 'holdout_generation_receipt.json',
        'calibration_shots.npz', 'holdout_shots.npz',
    } or name.startswith('external/')
    options = (archived, canonical) if historical else (canonical, archived)
    existing = [p for p in options if p.is_file()]
    if not existing:
        raise FileNotFoundError(f'Missing declared input {role}/{name}: tried {options}')
    if len(existing) == 2 and digest(existing[0]) != digest(existing[1]):
        raise RuntimeError(f'Canonical and authored versions disagree for {name}; no silent selection')
    return existing[0]


def validate_frozen_inputs(work_c):
    import numpy as np
    contract = read_json(work_c / 'CALIBRATION_CONTRACT.json')
    frozen = read_json(work_c / 'FROZEN_CALIBRATION_IDENTITY.json')
    plan = read_json(work_c / 'FROZEN_HOLDOUT_PLAN.json')
    if digest(work_c / 'CALIBRATION_CONTRACT.json') != frozen['contract_sha256']:
        raise RuntimeError('Calibration contract does not match its prior frozen identity')
    nominal_sha = digest(work_c / 'NOMINAL_MODEL.json')
    if plan['nominal_sha256'] != nominal_sha:
        raise RuntimeError('Frozen holdout does not bind the unchanged original nominal')
    for field, filename in [('classifier_sha256', 'evaluate_holdout.py'),
                            ('interval_source_sha256', 'interval_source.py')]:
        if field in plan and plan[field] != digest(work_c / filename):
            raise RuntimeError(f'Frozen holdout rule differs from current source: {filename}')
    counts = {}
    for phase in ('calibration', 'holdout'):
        receipt = read_json(work_c / f'{phase}_generation_receipt.json')
        sample_path = work_c / f'{phase}_shots.npz'
        if digest(sample_path) != receipt['data_sha256']:
            raise RuntimeError(f'{phase} sample bytes differ from original generation receipt')
        if receipt['contract_sha256'] != frozen['contract_sha256']:
            raise RuntimeError(f'{phase} generation used a different contract')
        if phase == 'holdout' and receipt['nominal_sha256'] != nominal_sha:
            raise RuntimeError('Original holdout generation did not bind this nominal')
        observed = 0
        with np.load(sample_path, allow_pickle=False) as arrays:
            expected = {r['setting_id']: r['shots'] for r in receipt['settings']}
            if set(arrays.files) != set(expected):
                raise RuntimeError(f'{phase} setting names differ from original receipt')
            for name in arrays.files:
                values = arrays[name]  # actually decompress/read every archived row
                maximum = 1 if phase == 'calibration' else 7
                if values.ndim != 1 or len(values) != expected[name] or np.any(values > maximum) or np.any(values < 0):
                    raise RuntimeError(f'Invalid archived {phase} outcomes in {name}')
                observed += len(values)
        if observed != receipt['total_shots']:
            raise RuntimeError(f'{phase} row count differs from original receipt')
        counts[phase] = {'reused_rows': observed,
                         'historical_generation_receipt': file_identity(work_c / f'{phase}_generation_receipt.json')}
    counts['total_unique_archived_synthetic_rows'] = sum(counts[x]['reused_rows'] for x in ('calibration', 'holdout'))
    counts['new_synthetic_shots_this_run'] = 0
    counts['hardware_shots_this_run'] = 0
    counts['new_Lean_runs_this_run'] = 0
    return counts


def run(args):
    source_dir = (args.source_dir or Path(__file__).resolve().parent).resolve()
    authored_dir = (args.evidence_dir or source_dir.parent / 'kernel/evidence/v31.14/authored').resolve()
    output = args.output_dir.resolve()
    if output.is_relative_to(source_dir) or output.is_relative_to(authored_dir):
        raise ValueError('Output must be outside canonical sources and immutable authored evidence')
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        raise ValueError('--output-dir must be absent or an empty directory; prior runs are never overwritten')
    output.mkdir(parents=True, exist_ok=True)
    logdir = output / 'logs'; logdir.mkdir()
    receipt_path = output / 'runtime.json'
    wall_start = time.perf_counter(); own_cpu_start = time.process_time()
    children_start = resource.getrusage(resource.RUSAGE_CHILDREN)
    state = {'schema': 'ueot.persistent_bath.portable_verification.v1',
             'status': 'RUNNING', 'started_at_utc': now(), 'source_dir': str(source_dir),
             'authored_evidence_dir': str(authored_dir), 'output_dir': str(output),
             'runner': file_identity(Path(__file__)), 'python_executable': sys.executable,
             'source_files': {}, 'copied_inputs': {}, 'commands': [],
             'inputs_stable_during_execution': True, 'immutability_checkpoints': [],
             'git_context_start': git_context(source_dir),
             'scope': 'Replayed finite exact/interval/floating checks against unchanged archived synthetic rows; no new samples, Lean builds, hardware calls or external publication'}
    state['dependency_versions'] = {}
    for package in ('numpy', 'scipy', 'sympy', 'mpmath', 'h5py'):
        try:
            spec = importlib.util.find_spec(package)
            state['dependency_versions'][package] = {
                'version': importlib.metadata.version(package),
                'module_origin': spec.origin if spec else None}
        except (importlib.metadata.PackageNotFoundError, ImportError):
            state['dependency_versions'][package] = {'available': False}
    state['inherited_pythonpath'] = os.environ.get('PYTHONPATH')
    immutable = {}
    env = dict(os.environ)
    env.update({'PYTHONDONTWRITEBYTECODE': '1', 'OPENBLAS_NUM_THREADS': '1',
                'OMP_NUM_THREADS': '1', 'MKL_NUM_THREADS': '1', 'NUMEXPR_NUM_THREADS': '1'})
    state['controlled_environment'] = {k: env[k] for k in (
        'PYTHONDONTWRITEBYTECODE', 'OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS',
        'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS')}

    def checkpoint(label):
        changed = [str(p) for p, original in immutable.items()
                   if not p.is_file() or digest(p) != original]
        state['immutability_checkpoints'].append({'at_utc': now(), 'label': label,
                                                  'files_checked': len(immutable), 'changed': changed})
        if changed:
            state['inputs_stable_during_execution'] = False
            write_json(receipt_path, state)
            raise RuntimeError(f'Immutable inputs changed: {changed}')

    def copy_input(src, dest, logical):
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dest)
        item = {'source': file_identity(src), 'working_copy': str(dest), 'sha256': digest(dest)}
        if item['source']['sha256'] != item['sha256']:
            raise RuntimeError(f'Copy byte mismatch for {logical}')
        state['copied_inputs'][logical] = item
        immutable[src] = item['sha256']; immutable[dest] = item['sha256']

    def command(name, argv, cwd):
        checkpoint('before:' + name)
        number = len(state['commands']) + 1
        stdout_path = logdir / f'{number:02d}_{name}.stdout.txt'
        stderr_path = logdir / f'{number:02d}_{name}.stderr.txt'
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        started = time.perf_counter()
        record = {'name': name, 'argv': [str(a) for a in argv], 'cwd': str(cwd),
                  'started_at_utc': now(), 'stdout': str(stdout_path.relative_to(output)),
                  'stderr': str(stderr_path.relative_to(output))}
        state['commands'].append(record); write_json(receipt_path, state)
        print(f'[{number}] Running {name}', flush=True)
        try:
            with stdout_path.open('w') as out, stderr_path.open('w') as err:
                result = subprocess.run(record['argv'], cwd=cwd, env=env,
                                        stdout=out, stderr=err, check=False,
                                        timeout=args.step_timeout_seconds)
            record['returncode'] = result.returncode
        except subprocess.TimeoutExpired:
            record['returncode'] = None; record['timed_out'] = True
        finally:
            after = resource.getrusage(resource.RUSAGE_CHILDREN)
            record.update({'finished_at_utc': now(), 'wall_seconds': time.perf_counter() - started,
                           'child_cpu_seconds': (after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime)})
            for label, path in [('stdout_sha256', stdout_path), ('stderr_sha256', stderr_path)]:
                if path.exists(): record[label] = digest(path)
            write_json(receipt_path, state)
        checkpoint('after:' + name)
        if record.get('returncode') != 0:
            raise RuntimeError(f'{name} failed; inspect {record["stderr"]} and {record["stdout"]}')

    try:
        works = {role: output / f'work_{role}' for role in ('a', 'b', 'c')}
        env['UEOT_DYNAMICS_PATH'] = str(works['b'] / 'dynamics.py')
        state['controlled_environment']['UEOT_DYNAMICS_PATH'] = env['UEOT_DYNAMICS_PATH']
        for role, names in SOURCE_FILES.items():
            works[role].mkdir()
            for name in names:
                original = source_dir / name
                if not original.is_file():
                    raise FileNotFoundError(f'Missing flat production source {original}')
                copy_input(original, works[role] / name, f'source/{role}/{name}')
                state['source_files'][name] = file_identity(original)
        contract = source_dir / 'SHARED_MODEL.json'
        copy_input(contract, output / 'SHARED_MODEL.json', 'SHARED_MODEL.json')
        model = choose_input(source_dir, authored_dir, 'b', 'model_contract.json')
        copy_input(model, works['b'] / 'model_contract.json', 'b/model_contract.json')
        for name in C_INPUT_FILES:
            original = choose_input(source_dir, authored_dir, 'c', name)
            copy_input(original, works['c'] / name, f'c/{name}')
        state['data_accounting'] = validate_frozen_inputs(works['c'])
        state['original_nominal_sha256'] = digest(works['c'] / 'NOMINAL_MODEL.json')
        state['original_holdout_plan_sha256'] = digest(works['c'] / 'FROZEN_HOLDOUT_PLAN.json')
        py = [sys.executable, '-B']
        command('A_verify', py + [works['a'] / 'verify_a.py', '--contract', output / 'SHARED_MODEL.json'], works['a'])
        command('B_dynamics', py + [works['b'] / 'verify_dynamics.py'], works['b'])
        command('B_eight_interval_certificates', py + [works['b'] / 'build_certificates.py'], works['b'])
        command('B_strict_memory_event', py + [works['b'] / 'certify_memory_witness.py'], works['b'])
        command('A_independent_B_review', py + [works['a'] / 'review_b.py', '--bdir', works['b']], works['a'])
        if args.calibration_readback:
            caldir = output / 'calibration_readback'; caldir.mkdir()
            for name in ('common_c.py', 'calibrate.py', 'CALIBRATION_CONTRACT.json',
                         'FROZEN_CALIBRATION_IDENTITY.json', 'calibration_generation_receipt.json',
                         'calibration_shots.npz'):
                copy_input(works['c'] / name, caldir / name, f'calibration_readback/{name}')
            command('C_optional_calibration_readback', py + [caldir / 'calibrate.py'], caldir)
            original = read_json(works['c'] / 'NOMINAL_MODEL.json')
            readback = read_json(caldir / 'NOMINAL_MODEL.json')
            different = [field for field in CALIBRATION_COMPARE_FIELDS if original[field] != readback[field]]
            state['calibration_readback'] = {'enabled': True, 'compared_fields': list(CALIBRATION_COMPARE_FIELDS),
                'different_fields': different, 'original_nominal_sha256': digest(works['c'] / 'NOMINAL_MODEL.json'),
                'new_readback_output_sha256': digest(caldir / 'NOMINAL_MODEL.json'),
                'holdout_or_truth_copied_to_estimator_directory': False,
                'readback_used_for_holdout': False}
            if different:
                raise RuntimeError(f'Calibration-only readback differs in scientific fields: {different}')
        else:
            state['calibration_readback'] = {'enabled': False, 'original_nominal_reused_unchanged': True}
        command('C_generation_probability_audit', py + [works['c'] / 'verify_generation.py'], works['c'])
        command('C_frozen_holdout', py + [works['c'] / 'evaluate_holdout.py'], works['c'])
        command('C_final_exact_certificate', py + [works['c'] / 'finalize_certificate.py', '--certificate-dir', works['b']], works['c'])
        command('C_external_processed_observable', py + [works['c'] / 'reproduce_external_observable.py'], works['c'])
        a = read_json(works['a'] / 'A_VERIFICATION.json')
        ar = read_json(works['a'] / 'A_REVIEW_B_CHECK.json')
        b = read_json(works['b'] / 'dynamics_results.json')
        memory = read_json(works['b'] / 'memory_event_witness.json')
        c = read_json(works['c'] / 'FINAL_CERTIFICATE.json')
        hold = read_json(works['c'] / 'HOLDOUT_RESULTS.json')
        external = read_json(works['c'] / 'EXTERNAL_OBSERVABLE_RESULT.json')
        expected = {'deployment': 'NOT_REJECTED_FROZEN_HOLDOUT',
                    'changed_intervals': 'NOT_REJECTED_FROZEN_HOLDOUT',
                    'detector_violation': 'REJECTED_MODEL_CONTRACT'}
        if a['status'] != 'PASS_DECLARED_FINITE_SCOPE' or ar['status'] != 'PASS_EXACT_CERTIFICATE_READBACK_AND_DECLARED_INTERFACE':
            raise RuntimeError('A verification did not report the declared passing scopes')
        if {name: hold['families'][name]['status'] for name in expected} != expected:
            raise RuntimeError('Frozen holdout classifications changed')
        if c['source_certificate_status'] != 'CERTIFIED_CONDITIONAL_SYNTHETIC_SOURCE' or not c['all_original_decisions_unchanged']:
            raise RuntimeError('C final certificate did not satisfy the frozen conditional target')
        if c['hardware_status'] != 'NOT_CERTIFIED' or hold['method_gain'] != 'EQUIVALENT_NO_ADDED_GAIN':
            raise RuntimeError('Scientific scope or baseline gain labels changed')
        state['scientific_outputs'] = {'A_status': a['status'], 'B_status': b['status'],
            'independent_B_review_status': ar['status'], 'strict_memory_status': memory['status'],
            'strict_memory_event_lower_rational': memory['strict_event_gap_lower_rational'],
            'interval_certificates': len(ar['certificates']),
            'exact_principal_minors_checked': sum(sum(x['count'] for x in cert['exact_principal_minor_psd'].values()) + cert['residual_psd']['count'] for cert in ar['certificates']),
            'source_certificate_status': c['source_certificate_status'],
            'quantum_complete_CQ_upper': c['quantum_complete_CQ_upper'],
            'fixed_complete_terminal_tester_upper': c['fixed_complete_terminal_tester_upper'],
            'heldout_classifications': expected, 'method_gain': hold['method_gain'],
            'hardware_status': c['hardware_status'], 'external_data_qualification': external['data_qualification']}
        checkpoint('final')
        state['status'] = 'PASS'
    except Exception as error:
        state['status'] = 'FAIL'
        state['failure'] = {'type': type(error).__name__, 'message': str(error),
                            'traceback': traceback.format_exc()}
        print(f'FAIL: {error}', file=sys.stderr, flush=True)
    finally:
        after_children = resource.getrusage(resource.RUSAGE_CHILDREN)
        state.update({'finished_at_utc': now(), 'wall_seconds': time.perf_counter() - wall_start,
                      'runner_cpu_seconds': time.process_time() - own_cpu_start,
                      'child_cpu_seconds': after_children.ru_utime + after_children.ru_stime - children_start.ru_utime - children_start.ru_stime,
                      'git_context_end': git_context(source_dir)})
        state['output_files'] = {str(path.relative_to(output)): {'bytes': path.stat().st_size, 'sha256': digest(path)}
                                 for path in sorted(output.rglob('*'))
                                 if path.is_file() and path != receipt_path and path not in immutable}
        write_json(receipt_path, state)
    print(json.dumps({'status': state['status'], 'inputs_stable_during_execution': state['inputs_stable_during_execution'],
                      'runtime_receipt': str(receipt_path), 'wall_seconds': state['wall_seconds']}, indent=2), flush=True)
    return 0 if state['status'] == 'PASS' else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', required=True, type=Path,
                        help='absent or empty output directory, outside canonical sources and authored evidence')
    parser.add_argument('--source-dir', type=Path,
                        help='flat production source directory; default is this script directory')
    parser.add_argument('--evidence-dir', type=Path,
                        help='authored archive root containing a,b,c; default is sibling kernel/evidence/v31.14/authored')
    parser.add_argument('--calibration-readback', action='store_true',
                        help='recompute calibration in a separate directory, compare scientific fields only, never replace frozen nominal')
    parser.add_argument('--step-timeout-seconds', type=float, default=600,
                        help='per-command timeout; failures and partial outputs are retained')
    args = parser.parse_args()
    if args.step_timeout_seconds <= 0:
        parser.error('--step-timeout-seconds must be positive')
    raise SystemExit(run(args))


if __name__ == '__main__':
    main()
