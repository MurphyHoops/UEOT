from pathlib import Path
import hashlib
import json
import re

BASE = Path('/workspace/scratch/9a8d58b21e30')
AUTHOR = BASE / 'tmp/core-global-review-20261021/tail-proof-v1'
OUT = BASE / 'tmp/core-global-review-20261021/independent'
REPO = BASE / 'ueot-integration'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def pin(p):
    p = Path(p)
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha(p)}

checked = {}
def check_records(x):
    if isinstance(x, dict):
        if 'path' in x and 'sha256' in x:
            p = Path(x['path'])
            assert p.is_file(), str(p)
            actual = pin(p)
            assert actual['sha256'] == x['sha256'], str(p)
            if 'bytes' in x:
                assert actual['bytes'] == x['bytes'], str(p)
            checked[str(p)] = actual
        for value in x.values():
            check_records(value)
    elif isinstance(x, list):
        for value in x:
            check_records(value)

names = ['COMPILE_PASS.json', 'DECLARATION_COMPARISON.json',
         'RESOLVED_DIRECT_IMPORTS.json', 'ENVIRONMENT_REUSE_BINDING.json',
         'API_INPUTS.json', 'lean-attempt-001/STATUS.json']
data = {name: json.loads((AUTHOR / name).read_text()) for name in names}
for name, value in data.items():
    check_records(value)
    checked[str(AUTHOR / name)] = pin(AUTHOR / name)

source = (AUTHOR / 'SameSourceSurvivalTail.lean').read_bytes()
assert source == (AUTHOR / 'v1-original/SameSourceSurvivalTail.lean').read_bytes()
assert source == (AUTHOR / 'lean-attempt-001/SameSourceSurvivalTail.lean').read_bytes()
assert (AUTHOR / 'SOURCE_DELTA.patch').read_bytes() == b''
for name in ['CONTRACT.md', 'API_INPUTS.json', 'ENVIRONMENT_REUSE_BINDING.json', 'STATUS.json']:
    assert (AUTHOR / name).read_bytes() == (AUTHOR / 'v1-original' / name).read_bytes()
    checked[str(AUTHOR / 'v1-original' / name)] = pin(AUTHOR / 'v1-original' / name)

# Inspect the complete declaration delimiter, not nested named-argument :=.
text = source.decode()
starts = list(re.finditer(r'(?m)^(?:private\s+)?(?:theorem|def|instance|axiom|opaque)\b', text))
assert len(starts) == 1
start = starts[0].start()
depth = 0
end = None
for i in range(start, len(text) - 1):
    c = text[i]
    if c in '([{':
        depth += 1
    elif c in ')]}':
        depth -= 1
    if depth == 0 and text[i:i+2] == ':=':
        end = i
        break
assert end is not None
header = text[start:end]
decl = data['DECLARATION_COMPARISON.json']['complete_headers'][0]
assert header == decl['original'] == decl['final']
assert hashlib.sha256(header.encode()).hexdigest() == decl['sha256']
assert not re.search(r'(?m)^\s*(?:sorry|admit|axiom|set_option)\b', text)

status = data['lean-attempt-001/STATUS.json']
assert status['status'] == 'PASS' and status['exit_code'] == 0 and not status['timed_out']
assert status['elapsed_seconds'] == 8.895
assert status['source']['sha256'] == status['source_after']['sha256'] == sha(AUTHOR / 'SameSourceSurvivalTail.lean')
assert sorted(p.name for p in AUTHOR.glob('lean-attempt-*') if p.is_dir()) == ['lean-attempt-001']
log = (AUTHOR / 'lean-attempt-001/lean.log').read_text()
assert len(re.findall(r'warning:', log)) == 1
assert 'letI' in log and 'error:' not in log
ax = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log, re.S)
assert len(ax) == 1
axioms = [x.strip() for x in ax[0][1].split(',')]
assert axioms == ['propext', 'Classical.choice', 'Quot.sound']
assert ax[0][0].endswith('.killed_survival_mass_tendsto_homogeneous_neverHit_real')

api = data['API_INPUTS.json']
assert len(api['records']) == 25
build_path = Path(status['production_manifest']['path'])
build = json.loads(build_path.read_text())['build_identity']
core = REPO / 'formalization/ueot-core'
live_sources = {str(p.relative_to(REPO)): sha(p)
                for p in [core / 'UEOT.lean', *sorted((core / 'UEOT').rglob('*.lean'))]}
pinned_sources = {r['path']: r['sha256'] for r in build['source_files']}
assert live_sources == pinned_sources and len(live_sources) == 666
for row in build['environment_files']:
    assert sha(REPO / row['path']) == row['sha256']
for row in build['runtime_tools'].values():
    assert sha(row['executable']) == row['sha256']
assert build['source_tree_sha256'] == status['production_complete_source_sha256']
assert build['dependencies'] == data['ENVIRONMENT_REUSE_BINDING.json']['pinned_dependencies']

env = json.loads((AUTHOR / 'lean-attempt-001/ENV_AFTER_LAKE.json').read_text())
resolution = data['RESOLVED_DIRECT_IMPORTS.json']
roots = [Path(p) for p in env['LEAN_PATH'].split(':')]
assert list(map(str, roots)) == resolution['actual_search_roots']
assert len(roots) == 15
assert env['LEAN_NUM_THREADS'] == '1'
assert env['ELAN_TOOLCHAIN'] == 'leanprover/lean4:4.33.1'
assert env['LEAN_SYSROOT'] == str(BASE / 'tmp/registered-interfaces-20261021/linux-runtime/lean-4.33.1-linux')
imports = re.findall(r'(?m)^import\s+(\S+)', text)
assert imports == [r['module'] for r in resolution['direct_imports']]
resolved = []
for row in resolution['direct_imports'] + resolution['all_four_frozen_private_modules']:
    module_path = Path(*row['module'].split('.')).with_suffix('.olean')
    candidates = [root / module_path for root in roots if (root / module_path).is_file()]
    assert list(map(str, candidates)) == row['all_existing_candidates']
    assert candidates and str(candidates[0]) == row['selected_olean']['path']
    assert sha(candidates[0]) == row['selected_olean']['sha256']
    resolved.append({'module': row['module'], 'selected': pin(candidates[0]), 'candidate_count': len(candidates)})

evidence = {
    'schema': 'UEOT_SAME_SOURCE_TAIL_INDEPENDENT_EXECUTION_EVIDENCE_V1',
    'reviewer': '/root/audit_resume',
    'status': 'IDENTITY_AND_EXECUTION_EVIDENCE_CHECKED_NO_REEXECUTION',
    'checked_records': sorted(checked.values(), key=lambda row: row['path']),
    'source_original_snapshot_final_byte_identical': True,
    'complete_public_header': header,
    'complete_public_header_sha256': hashlib.sha256(header.encode()).hexdigest(),
    'production_source_count': len(live_sources),
    'production_complete_path_sha_vector_equal': True,
    'production_source_tree_sha256': build['source_tree_sha256'],
    'dependency_identity_scope': 'Reuses completed-build actual dependency HEAD/clean evidence; no fresh Git query.',
    'actual_import_resolution': resolved,
    'actual_search_root_count': len(roots),
    'actual_lean_exit_code': status['exit_code'],
    'actual_lean_elapsed_seconds': status['elapsed_seconds'],
    'actual_axioms': {ax[0][0]: axioms},
    'actual_warning_count': 1,
    'actual_lean_failures': [],
    'metadata_preparation_failure_preserved_separately': pin(AUTHOR / 'preparation-001.log'),
    'original_contract_API_environment_STATUS_preserved': True,
    'reviewer_operations': {'Lean': False, 'Lake': False, 'native': False, 'tests': False,
                            'Git': False, 'production_author_archive_write': False},
}
(OUT / 'TAIL_EXECUTION_EVIDENCE.json').write_text(json.dumps(evidence, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'status': evidence['status'], 'verified_record_count': len(checked),
                  'production_sources': len(live_sources), 'API_inputs': len(api['records']),
                  'direct_imports': len(imports), 'private_olean_pairs': 4,
                  'output': pin(OUT / 'TAIL_EXECUTION_EVIDENCE.json')}, ensure_ascii=False))
