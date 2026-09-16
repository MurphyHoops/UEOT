# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current lifecycle snapshot

- source P-IDs: **106**;
- authoritative full-green baseline before this ledger checkpoint: **82/106**;
- full-green 82 baseline: `main@86a2cd21e4693ae084e7bc904d38046f9b3a1519`;
- full-green 82 resulting-main CI: `35083749972` — success;
- P-CTL-01 proof main: `3efe7ebc74d8f2a6705c12a5218a7880f5a3688c`;
- P-CTL-01 proof resulting-main CI: `35104140440` — success;
- ledger branch: `formal/ledger-81-pcomp01`;
- this branch stages **83/106**;
- remaining not-yet-counted P-IDs after staging: **23**;
- active uncounted proof lanes after this staging: **0**.

**Do not call 83/106 full-green until this ledger/recovery branch passes its own
branch CI, PR CI, lands on `main`, and the resulting main CI succeeds.**

## P-CTL-01 — proof complete, ledger promotion running

Frozen Core 3 P-CTL-01 is represented at source strength for finite discounted
control: finite state space, state-dependent finite nonempty action sets,
bounded rewards, stochastic transitions and `0 < beta < 1`.

The proof establishes:

1. Bellman is a contraction in the finite-state sup metric;
2. the Bellman fixed point `V*` exists and is unique;
3. value iteration converges from every initial value function;
4. the residual stopping certificate is proved;
5. an arbitrary causal policy may carry arbitrary time-indexed memory and a randomized action law, so full history dependence is retained;
6. finite-horizon values of every causal policy are bounded by `V*` plus an explicit geometric terminal tail;
7. bounded rewards give a geometric increment bound, Cauchy convergence and a well-defined infinite discounted value;
8. every causal history-dependent randomized policy is dominated by `V*`;
9. a stationary deterministic Bellman-greedy causal policy attains `V*` at every state.

Canonical theorem:
- `UEOT.V3.FiniteDiscountedControl.p_ctl_01_causal_optimality`.

Supporting source-facing facts:
- `UEOT.V3.FiniteDiscountedControl.Model.fixedPoint_unique`;
- `UEOT.V3.FiniteDiscountedControl.Model.valueIteration_tendsto`;
- `UEOT.V3.FiniteDiscountedControl.Model.valueError_le_residual`;
- `UEOT.V3.FiniteDiscountedControl.CausalPolicy.infiniteValue_le_optimal`;
- `UEOT.V3.FiniteDiscountedControl.greedy_infiniteValue_eq_optimal`.

Evidence:
- feature `formal/pcomp01-multiblock-v1@47218ef06c63ed81ab3974d107f0d3d46cc49ecb`;
- feature official root CI `35098260086` success;
- source semantic audit complete;
- prohibited-proof audit clean (`sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`);
- clean integration `formal/pcomp01-main-integration-v1@45440746a7086b74bc65ba741611f98a8da92f27`;
- clean integration official root CI `35099296408` success;
- proof PR #93 PR CI `35102272835` success;
- proof main `3efe7ebc74d8f2a6705c12a5218a7880f5a3688c`;
- proof resulting-main CI `35104140440` success.

Exact next action: complete the separate **83/106** ledger/recovery branch → PR →
main resulting-CI lifecycle. Only after that gate may the authoritative count
advance from 82/106 to 83/106 full-green.

## Previous full-green promotion — 82/106

P-COMP-02 and all earlier counted P-IDs are already closed in the 82/106
baseline at `main@86a2cd21e4693ae084e7bc904d38046f9b3a1519`; ledger resulting-main CI
`35083749972` succeeded.

P-TEL-01 is already counted. Older archived compilation reports that called it
partial must not override the current main coverage ledger or cause a duplicate
proof lane.

## Branchless next-front audit

No second proof branch is open during the P-CTL-01 ledger lifecycle.

- **P-QUO-01:** now high leverage because Chapter 20 explicitly assumes the Chapter 19 Bellman existence/uniqueness layer. Frozen source requires a surjection with same-fiber action sets, reward closure and every-action pushed-forward transition closure; Bellman intertwining must yield `V* = Vbar* o f`, and macro argmax must lift to a micro optimal policy.
- **P-QUO-02:** approximate continuation of that interface; it additionally requires the span-sensitive P-MET-02 residual bound and proves `||V*-w|| <= D` plus lifted-policy regret `<= 2D`.
- **P-CTL-02:** non-quick compact/Feller control theorem with continuity and measurable-selection obligations.
- **P-PER-02 / P-ALI-01 / P-KL-04/05 / P-EVO-03/04 / P-DDH-02/03/04/05 / P-QSD-01/04:** remain larger source-strength foundations unless a fresh main audit finds an exact bridge.

Remote branch count is above the repository hard cap. After the 83/106 ledger
lifecycle closes, run the reviewed Core 3 branch-hygiene workflow before opening
a new theorem branch.

## Guards

- do not reopen counted green P-IDs absent source mismatch/CI regression;
- feature green or proof-main green never increments coverage;
- no `sorry`, `admit`, `native_decide`, or unsourced `axiom`;
- preserve frozen source strength; do not replace hard clauses by convenient finite/toy/assumed-conclusion surrogates;
- source-object identity must be explicit; a more general theorem does not count without a bridge to the frozen source object;
- historical conversation decisions and rejected surrogate routes are part of the recovery audit;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-KL-04/05 must remain at their frozen CTMC/Girsanov level;
- P-EVO-03 requires the full primitive nonnegative-matrix Perron-Frobenius asymptotic package, not assumed convergence.

## Recovery order

1. `NEW_CHAT_BOOTSTRAP.md`;
2. `docs/REPOSITORY_BRANCH_GOVERNANCE.md`;
3. `UEOT_CORE3_LEAN_OPERATIONS.md`;
4. Issue #56 when available;
5. `PID_STATUS.yaml`;
6. `FORMALIZATION_STATE.md`;
7. `V3_COVERAGE_STATUS.md`;
8. this `HANDOFF_LATEST.md` fallback snapshot;
9. live main/branches/CI reconciliation.
