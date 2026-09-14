# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current lifecycle snapshot

- source P-IDs: **106**;
- authoritative full-green baseline before this ledger checkpoint: **75/106**;
- full-green 75 baseline: `main@b4c8cd81c62b2e175998ebc4e855901e4b46f125`;
- P-BRG-01 proof main: `667471f1627ef762ebb116d082f2ed588132fa67`;
- P-BRG-01 proof resulting-main CI: `34818138195` — success;
- this branch stages **76/106**;
- remaining not-yet-counted P-IDs after staging: **30**;
- active uncounted proof lanes after this staging: **0**.

**Do not call 76/106 full-green until this ledger/recovery branch passes PR CI,
lands on `main`, and the resulting main CI succeeds.**

## P-BRG-01 — completed proof contract, ledger promotion running

Frozen §26.3 contract is implemented at full declared scope:

1. finite types and fixed strictly positive fitness `R_i`;
2. exact no-mutation replicator recurrence with declared initial state uniquely
   implies the explicit closed form;
3. initially absent types remain absent;
4. a maximum `R_*` is attained on the initially positive support;
5. each initially supported strictly suboptimal type has an explicit
   `(R_i/R_*)^n` geometric envelope;
6. total supported suboptimal mass is bounded by a finite sum of geometric terms
   and tends to zero;
7. equal-fitness support maximizers preserve their initial relative proportions.

Canonical theorems:
- `UEOT.V3.FixedFitnessRecurrenceUniqueness.p_brg_01_closedForm_of_recurrence`;
- `UEOT.V3.FixedFitnessConcentration.p_brg_01`.

Evidence:
- feature branch `formal/pbrg01-fixed-fitness-v1`;
- feature head `b3f47b89ad901fb11f322d7f386d5a86ba06e708`;
- feature CI `34815094214` success;
- source semantic audit complete;
- prohibited-proof audit clean;
- clean integration branch `formal/pbrg01-main-integration-v1`;
- clean integration head `a40b18ddc99617b25d873b376edf2aab3b096061`;
- clean integration CI `34817101777` success;
- PR #75 PR CI `34817631959` success;
- proof-main squash `667471f1627ef762ebb116d082f2ed588132fa67`;
- proof resulting-main CI `34818138195` success.

Exact next P-BRG-01 action: complete this separate 76 ledger/recovery PR lifecycle.

## P-REF-03 — previous promotion complete

P-REF-03 was promoted from the 74 baseline to the authoritative 75-P-ID
baseline. Its proof main is `0ebef06b4a2be2eb88d5b5708ca4bd5901db7b92` and
its ledger main is `b4c8cd81c62b2e175998ebc4e855901e4b46f125`.
Do not reopen it absent source mismatch or regression.

## Counted-source reconciliation — P-REF-04 / P-REF-05

Both P-REF-04 and P-REF-05 were already counted before this cycle. The wrapper
branches are audit/interface hardening only:

- P-REF-04 wrapper head `e63e74bfcd72273204bcd5608506d8c50ac40416`, CI `34812442268` success;
- P-REF-05 wrapper head `756e0862f36bc272a727b81ba11e3d6aa7019d9b`, CI `34815023569` success.

Existing counted theorems `Decision.goal_regret` and
`Agency.feasibleValue_mono` / `feasibleValueReal_mono` match the frozen source
contracts. Do not double-count or reopen them absent a substantive mismatch.

## Guards

- do not reopen counted green P-IDs absent source mismatch/CI regression;
- feature green never increments coverage;
- no `sorry`, `admit`, `native_decide`, or unsourced `axiom`;
- preserve frozen source strength; do not replace hard clauses by convenient
  finite/toy/Markov-only surrogates;
- P-QSD-01 and P-QSD-03 must never be swapped;
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
