from pathlib import Path
import datetime
import difflib
import hashlib
import json
import re
import sys

root = Path(__file__).resolve().parent
attempt = root / f'lean-attempt-{int(sys.argv[1]):03d}'
status = json.loads((attempt / 'STATUS.json').read_text())
assert status['status'] == 'PASS' and status['exit_code'] == 0 and not status['timed_out']
source = root / 'SameSourceKilledPath.lean'
old_source = root / 'SameSourceKilledPath_v1.lean'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(source) == status['source_sha256'] == status['source_sha256_after']
assert digest(attempt / source.name) == digest(source)
log = (attempt / 'lean.log').read_text()
assert 'sorryAx' not in log and ': error:' not in log
names = ['state_terminal_mass_eq_killed_pow',
         'actual_survival_terminal_mass_eq_killed_pow',
         'actual_survival_mass_eq_killed_pow_sum']
printed = dict(re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log, re.S))
axioms = {}
statements = {}
for name in names:
    full_name = 'UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledPathCheck.' + name
    actual = sorted(x.strip() for x in printed[full_name].split(',') if x.strip())
    assert set(actual) <= {'propext', 'Classical.choice', 'Quot.sound'}
    axioms[full_name] = actual
    pattern = re.compile(r'theorem ' + re.escape(name) + r'\b[\s\S]*?\s:= by')
    old_decl = pattern.search(old_source.read_text()).group()
    new_decl = pattern.search(source.read_text()).group()
    assert old_decl == new_decl
    statements[name] = {'unchanged_from_original': True,
                        'sha256': hashlib.sha256(new_decl.encode()).hexdigest()}
assert not re.search(r'\b(?:sorry|admit|axiom)\b', source.read_text())
delta = ''.join(difflib.unified_diff(old_source.read_text().splitlines(keepends=True),
                                   source.read_text().splitlines(keepends=True),
                                   fromfile=old_source.name, tofile=source.name))
patch = root / 'PROOF_ELABORATION_DELTA.patch'
patch.write_text(delta)
attempts = []
for item in sorted(root.glob('lean-attempt-*/STATUS.json')):
    data = json.loads(item.read_text())
    attempts.append({key: data.get(key) for key in
                     ['attempt', 'status', 'source_sha256', 'exit_code', 'timed_out',
                      'elapsed_seconds', 'log_sha256']})
receipt = {
    'schema': 'UEOT_PRIVATE_SAME_SOURCE_KILLED_K1_COMPILE_PASS_V1',
    'status': 'PRIVATE_FOCUSED_LEAN_PASS_NOT_INTEGRATED',
    'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source': str(source), 'source_sha256': digest(source),
    'original_source_sha256': digest(old_source),
    'passed_attempt': status, 'attempt_status_sha256': digest(attempt / 'STATUS.json'),
    'actual_axiom_closures': axioms, 'unchanged_endpoint_statements': statements,
    'proof_delta_sha256': digest(patch), 'all_attempts_preserved': attempts,
    'historical_draft_status_preserved': json.loads((root / 'STATUS.json').read_text()),
    'scope': 'K1 finite-window actual risk survival/terminal event masses and same-source killed matrix powers; no K2/K3 claim.',
    'boundary': ['n=0 includes initial failure', 'empty safe set allowed',
                 'arbitrary observation type', 'stationary current-observation randomized policy',
                 'no positive-survival or QSD hypothesis', 'no assumed source identity'],
    'production_changed': False, 'books_changed': False, 'git_or_remote_changed': False,
    'lake_build_executed_by_this_task': False, 'native_validation_claimed': False,
}
(root / 'COMPILE_PASS.json').write_text(json.dumps(receipt, indent=2) + '\n')
text = f'''# Private same-source killed-path K1: actual Lean PASS

Status: **PRIVATE_FOCUSED_LEAN_PASS_NOT_INTEGRATED**.

Attempt {status['attempt']:03d} exited 0 in {status['elapsed_seconds']} seconds, with
`LEAN_NUM_THREADS=1` and a {status['timeout_seconds']}-second timeout. Its recorded
startup gate had the root full build RUNNING and native WAITING. It imported the
already passed SourcePolicyPathBridge olean, with exact source and olean hashes
bound in the attempt receipt. No `lake build`, native export, production edit,
book edit, Git operation, or remote operation was performed by this task.

The three printed theorem closures contain only `propext`, `Classical.choice`,
and `Quot.sound`; there is no `sorryAx`. The three theorem declarations through
`:= by` are byte-identical to the original draft. The final differences concern
proof elaboration, a transparency option scoped to the private successor lemma,
the status comment, and the additional requested axiom print.

## Proven interface

For the actual action/state risk-path PMF under the original model and a
stationary current-observation randomized policy, survival through n steps
includes time zero. Its joint survival/terminal mass at v in K equals
`rowApply (safeInitialRow p0 K) (killedMatrix M pi K ^ n) v`.
Its survival probability is the sum of that row over K. The killed matrix is
defined as the restriction of the actual policy matrix, and the initial row is
the unnormalized restriction of the actual initial PMF. Neither identity is a
caller-supplied assumption. The source path pushforward is reused internally.

The result permits initial mass outside K and an empty K. Observation type Y
is arbitrary; states and actions are finite, actions are nonempty, and the
actual-event statements use the existing measurable-singleton assumptions.
This proves the finite-window K1 interface only. Conditional laws, QSD, and
Doob-transform claims remain outside this completion receipt.

## Evidence

- Final source SHA256: `{digest(source)}`.
- Passed olean SHA256: `{status['olean_sha256']}`.
- Actual log SHA256: `{status['log_sha256']}`.
- Original draft and every failed attempt remain unchanged.
- `PROOF_ELABORATION_DELTA.patch` records the original-to-final proof delta.
- `COMPILE_PASS.json` binds all attempts, startup gates, exact commands,
  imported source-bridge identities, and all three actual axiom closures.

This private compile is not canonical integration, a native export, or
resulting-main validation.
'''
(root / 'COMPILE_PASS.md').write_text(text)
print(json.dumps({'status': receipt['status'], 'source_sha256': digest(source),
                  'compile_receipt_sha256': digest(root / 'COMPILE_PASS.json'),
                  'actual_axiom_closures': axioms}, indent=2))
