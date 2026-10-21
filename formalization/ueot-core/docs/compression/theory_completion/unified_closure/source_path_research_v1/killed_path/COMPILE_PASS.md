# Private same-source killed-path K1: actual Lean PASS

Status: **PRIVATE_FOCUSED_LEAN_PASS_NOT_INTEGRATED**.

Attempt 010 exited 0 in 81.381 seconds, with
`LEAN_NUM_THREADS=1` and a 180-second timeout. Its recorded
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

- Final source SHA256: `fa4f5ce017d6bfa4d9f3fe77805ad629f1c04f34a7ac3495c9114c432bc6c826`.
- Passed olean SHA256: `91c3d26034d72d7abeb140d057c78b55296d4e4e7450cf5b291ccc3ad748d1e5`.
- Actual log SHA256: `cb1c77ddde8702fae626aad9b7ac6de6a079cf3e6cf71e21287c6c48430f5862`.
- Original draft and every failed attempt remain unchanged.
- `PROOF_ELABORATION_DELTA.patch` records the original-to-final proof delta.
- `COMPILE_PASS.json` binds all attempts, startup gates, exact commands,
  imported source-bridge identities, and all three actual axiom closures.

This private compile is not canonical integration, a native export, or
resulting-main validation.
