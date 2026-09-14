# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`. GitHub Issue #56
> carries the live cross-chat construction log when available.

Last synchronized: **2026-09-14**

## Environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`
- exact canonical bytes in public repo: pending synchronization

## Current staged checkpoint

| operational state | count |
|---|---:|
| integrated proved, staged by this checkpoint | **75** |
| active proof / feature-green uncounted | **1** |
| source audit | **0** |
| blocked | **0** |
| pending/unclassified | **30** |
| total | **106** |

The authoritative full-green baseline before this ledger branch is **74/106** at
`main@11dcc0349aeeba6444655752e1aca40eeaf75e02`, CI `34811815264` success.
P-REF-03 has now completed all proof-side and proof-main gates and this branch
stages 75/106. Do not call 75/106 full-green until this ledger branch passes PR
CI, lands on `main`, and the resulting main CI succeeds.

## Newly staged proof — P-REF-03

Frozen §27.3 is implemented without weakening its arbitrary-signal scope:

- the signal is represented by an arbitrary sub-σ-algebra;
- the action set is finite and nonempty;
- action payoffs are integrable;
- free information may be ignored, so every fixed action is still available;
- the pointwise informed maximum dominates every fixed-action conditional
  expectation;
- integrating and applying the conditional-expectation tower identity proves
  that informed expected value is at least the best uninformed fixed-action
  value.

Canonical source-facing theorem:
- `UEOT.V3.FreeInformationValue.p_ref_03`.

Evidence:
- feature `formal/pref03-free-information-v1@7ed287043f6da1e3d53bc67a95b7377bb989382a`;
- feature CI `34809014590`: success;
- clean integration `formal/pref03-main-integration-v1@1403f8529ec6920bfe2fb4ecb86ab55a2cfb6c3b`;
- clean integration CI `34812358314`: success;
- PR #73 PR-triggered CI `34812784352`: success;
- proof main `0ebef06b4a2be2eb88d5b5708ca4bd5901db7b92`;
- proof resulting-main CI `34814852905`: success;
- frozen-source semantic audit: complete;
- prohibited-proof audit: clean.

## Counted-source reconciliation — P-REF-04 / P-REF-05

The authoritative 74-P-ID baseline already contains P-REF-04 and P-REF-05.
The audit branches created during this cycle therefore do **not** open new
coverage slots:

- `formal/pref04-source-wrapper-v1@e63e74bfcd72273204bcd5608506d8c50ac40416`, CI `34812442268` success;
- `formal/pref05-source-wrapper-v1@756e0862f36bc272a727b81ba11e3d6aa7019d9b`, CI `34815023569` success.

Existing counted infrastructure already proves the frozen content through
`UEOT.V3.Decision.goal_regret` and `UEOT.V3.Agency.feasibleValue_mono` /
`feasibleValueReal_mono`. No substantive source mismatch was found, so the
no-reopen/no-double-count rule applies. The wrapper branches are audit/interface
hardening evidence only.

## Feature-green uncounted — P-BRG-01

Frozen §26.3 is source-locked to the finite fixed-positive-fitness no-mutation
replicator theorem. The completed feature contract now includes all of:

1. exact recurrence and explicit closed form;
2. an explicit converse/uniqueness theorem: arbitrary trajectories with the
   declared initial condition and recurrence equal the closed form;
3. no creation of types absent from the initial support;
4. choose `R_*` as the maximum fitness on the initial positive-mass support;
5. each supported suboptimal type has geometric factor `(R_i/R_*)^n`;
6. total suboptimal mass is bounded by a finite sum of those exponential terms
   and tends to zero;
7. support maximizers preserve their initial relative proportions.

Current branch: `formal/pbrg01-fixed-fitness-v1`.
Current feature head: `b3f47b89ad901fb11f322d7f386d5a86ba06e708`.
Official feature run: `34815094214` — success.

Implemented modules:
- `UEOT/V3/FixedFitnessSelection.lean`;
- `UEOT/V3/FixedFitnessRecurrenceUniqueness.lean`;
- `UEOT/V3/FixedFitnessConcentration.lean`.

Frozen-source semantic audit and prohibited-proof audit are complete. This lane
remains uncounted until 75/106 becomes FULL-GREEN and a fresh clean integration
is built from that exact main.

## Grounded non-quick fronts

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/03/04: source-locked distinct non-A results.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron-Frobenius asymptotic package; do not count an assumed-convergence
surrogate.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available,
   `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent audit/proof lane.
