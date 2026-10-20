# Replayed Ops publication-boundary review

Reviewer: `/root/independent_audit`. Date: 2026-10-20.

**Decision: CLEAR for publication of `0d22cf09b45ebb053c1e4426744e80787390a289` against `7d05d0369b6793e28f0e39efaa77c0c9887479d1`.** This is an exact-object/source-and-receipt review, not a new test run, remote CI receipt or assertion of merge completion.

## Exact boundary

- Candidate parent is the declared actual base `7d05d0369b6793e28f0e39efaa77c0c9887479d1`.
- The immutable candidate diff contains exactly the six originally reviewed O paths.
- Every candidate path is byte-identical to original O `3f5da21d923c4d2e1d644dd8df9c0180fa7488b4` and to the source manifest bound by the five-check Mac PASS.
- The entire binary Git patch `BASE → HEAD` is identical to `X → O`; only the integration parent has changed.
- The inspected candidate worktree was clean.

## QM preservation

Both candidate subtrees equal the real base subtrees:

| Protected subtree | Unchanged Git tree |
| --- | --- |
| `formalization/ueot-qm` | `729f6ff3f7a2595eb1e4182daa2754060fe7d50b` |
| `physics/qm` | `ff04f70838138243aa5ca0aeca5b885b4f7e245f` |

No QM or physics file is part of this Ops diff. Earlier X-to-current-main continuity review also established that the complete Core subtree, dependency lock, toolchain and all six baseline policy paths were unchanged by the intervening QM work.

## Validation and review reuse

The actual-base check receipt at `/workspace/scratch/9a8d58b21e30/tmp/release/ops-base-checks.json` names the exact base/head above. Both recorded commands returned 0: immutable-range `git diff --check` and research ownership validation from the actual base checkout. Their log bytes match the receipt hashes. The executed base-validator file is byte-identical to its immutable base blob. Receipt SHA-256: `11fc554ab3f5ffdeed12f73fc6c45013394fbb945234bcbccbbc455937b5458d`.

The previous Mac five-step PASS at `S/root/native-final-evidence-v2/files/ops-check-v2/status.json` remains reusable for this identical six-file source: the receipt says PASS, all five exit codes are 0, source integrity after execution is true, and its manifest hash and all six candidate source hashes agree. It records diff, ownership, research regressions, compression regressions and finalization regressions. This review did not rerun them. Its SHA-256 is `1675e0d4024ddb6b5cf1aa9639a994419934cb232a57b1067448d9c028ea990a`.

The existing independent six-file source review and this reviewer's subsequent O inspection remain applicable because the source patch is unchanged. Automatic governance and proof-escape checks stay enabled; cloud Lean is honestly NOT RUN unless manually requested; frozen/L3 FINAL evidence requirements remain intact. The narrow support-viability exception is not available to the Core PR until this Ops change is actually merged into canonical main.

## Remaining publication action

Publish this exact head, consume actual PR/base-policy checks, merge, and fetch the real resulting main before replaying C. No new mathematical proof build is justified by this policy-only replay. This CLEAR does not waive live remote checks or establish that any branch was pushed or merged.
