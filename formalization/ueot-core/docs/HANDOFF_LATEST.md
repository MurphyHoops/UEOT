# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current lifecycle snapshot

- source P-IDs: **106**;
- authoritative full-green baseline before this ledger checkpoint: **74/106**;
- full-green 74 baseline: `main@11dcc0349aeeba6444655752e1aca40eeaf75e02`;
- full-green 74 main CI: `34811815264` — success;
- P-REF-03 proof main: `0ebef06b4a2be2eb88d5b5708ca4bd5901db7b92`;
- P-REF-03 proof resulting-main CI: `34814852905` — success;
- this branch stages **75/106**;
- remaining not-yet-counted P-IDs after staging: **31**;
- active uncounted lane: **P-BRG-01** (feature-green, source-audited).

**Do not call 75/106 full-green until this ledger/recovery branch passes PR CI,
lands on `main`, and the resulting main CI succeeds.**

## P-REF-03 — completed proof contract, ledger promotion running

Frozen §27.3 is implemented at source scope:

1. arbitrary signal information represented by an arbitrary sub-σ-algebra;
2. finite nonempty action set;
3. integrable action payoffs;
4. free information may be ignored, so every fixed action remains feasible;
5. pointwise informed maximum dominates each fixed action;
6. integration plus the conditional-expectation tower identity yields informed
   value at least the best fixed-action value.

Canonical theorem: `UEOT.V3.FreeInformationValue.p_ref_03`.

Evidence:
- feature branch `formal/pref03-free-information-v1`;
- feature head `7ed287043f6da1e3d53bc67a95b7377bb989382a`;
- feature CI `34809014590` success;
- clean integration branch `formal/pref03-main-integration-v1`;
- clean integration head `1403f8529ec6920bfe2fb4ecb86ab55a2cfb6c3b`;
- clean integration CI `34812358314` success;
- PR #73 PR CI `34812784352` success;
- proof-main squash `0ebef06b4a2be2eb88d5b5708ca4bd5901db7b92`;
- proof resulting-main CI `34814852905` success;
- source semantic audit complete;
- prohibited-proof audit clean.

Exact next P-REF-03 action: complete this separate 75 ledger/recovery PR lifecycle.

## Counted-source reconciliation — P-REF-04 / P-REF-05

Both P-REF-04 and P-REF-05 already belong to the authoritative counted 74-P-ID
baseline. Audit wrappers produced during this cycle are therefore not new
coverage:

- P-REF-04 wrapper head `e63e74bfcd72273204bcd5608506d8c50ac40416`, CI `34812442268` success;
- P-REF-05 wrapper head `756e0862f36bc272a727b81ba11e3d6aa7019d9b`, CI `34815023569` success.

Existing counted theorems `Decision.goal_regret` and
`Agency.feasibleValue_mono` / `feasibleValueReal_mono` already match their
frozen source contracts. Do not double-count or reopen them absent a substantive
source mismatch or CI regression.

## P-BRG-01 — feature-green, uncounted

Frozen §26.3 contract:

- finite types and fixed `R_i > 0`;
- exact replicator recurrence **implies** the explicit closed form;
- `R_*` is the maximum fitness on the initially positive support;
- no mutation means no creation outside initial support;
- each initially supported suboptimal type carries an explicit
  `(R_i/R_*)^n` geometric factor;
- total suboptimal mass is bounded by a finite sum of those geometric terms and
  therefore decays exponentially to zero;
- support maximizers keep their initial relative proportions.

Feature branch: `formal/pbrg01-fixed-fitness-v1`.
Current head: `b3f47b89ad901fb11f322d7f386d5a86ba06e708`.
Current CI: `34815094214` — success.

Current modules:
- `UEOT/V3/FixedFitnessSelection.lean` — algebraic core;
- `UEOT/V3/FixedFitnessRecurrenceUniqueness.lean` — arbitrary-recurring-trajectory uniqueness / closed-form converse;
- `UEOT/V3/FixedFitnessConcentration.lean` — source concentration layer.

Source semantic audit and prohibited-proof audit are complete. Once 75/106 is
FULL-GREEN, create a new clean integration from that exact main, copy only the
effective P-BRG-01 files/imports, and run the normal promotion gates.

## Guards

- do not reopen counted green P-IDs absent source mismatch/CI regression;
- feature green never increments coverage;
- no `sorry`, `admit`, `native_decide`, or unsourced `axiom`;
- preserve frozen source strength; do not replace hard clauses by convenient
  finite/toy/Markov-only surrogates;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-REF-03 requires arbitrary signal spaces;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-BRG-01 includes recurrence⇒closed-form, concentration/extinction and maximizer-ratio clauses;
- P-KL-04/05 must remain at their frozen CTMC/Girsanov level.

## Recovery order

1. `UEOT_CORE3_LEAN_OPERATIONS.md`;
2. Issue #56 when available;
3. `PID_STATUS.yaml`;
4. `FORMALIZATION_STATE.md`;
5. `V3_COVERAGE_STATUS.md`;
6. this `HANDOFF_LATEST.md` fallback snapshot;
7. live main/branches/CI reconciliation.
