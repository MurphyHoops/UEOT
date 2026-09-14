# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current lifecycle snapshot

- source P-IDs: **106**;
- authoritative full-green baseline before this ledger checkpoint: **73/106**;
- full-green 73 baseline: `main@0285b7b8da4c94cc7d8d890336cd97e5e64718cb`;
- full-green 73 main CI: `34808329108` — success;
- P-REF-02 proof main: `c1213a6014f37a84bdfe128cced1a472b682248e`;
- P-REF-02 proof resulting-main CI: `34810452071` — success;
- this branch stages **74/106**;
- remaining not-yet-counted P-IDs after staging: **32**;
- active uncounted lanes: **P-REF-03** (feature-green) and **P-BRG-01** (proof).

**Do not call 74/106 full-green until this ledger/recovery branch passes PR CI,
lands on `main`, and the resulting main CI succeeds.**

## P-REF-02 — completed proof contract, ledger promotion running

Frozen §27.2 is implemented at source scope:

1. finite latent parameter/state Bayesian model;
2. normalized predictive observation law determined only by `(b,a)`;
3. exact positive-evidence Bayes posterior;
4. zero evidence is explicit `modelConflict`;
5. general observation posterior/disintegration reconstructs the one-step joint
   law and averages back to the predicted latent law;
6. one-step bounded-discount expected reward and continuation depend only on
   belief and action, providing the frozen belief-control reduction interface;
7. no generic Bellman theorem is overclaimed.

Canonical source-facing theorems live in `UEOT.V3.PRef02`.

Evidence:
- clean integration branch `formal/pref02-main-integration-v1`;
- clean integration head `0037fc0e494b46200ead20e2f5c3ce84a66eb577`;
- push CI `34808870460` success;
- PR #71 PR CI `34810019287` success;
- proof-main squash `c1213a6014f37a84bdfe128cced1a472b682248e`;
- proof resulting-main CI `34810452071` success;
- source semantic audit complete;
- prohibited-proof audit clean.

Exact next P-REF-02 action: complete this separate 74 ledger/recovery PR lifecycle.

## P-REF-03 — feature-green, uncounted

Branch: `formal/pref03-free-information-v1`.
Final feature head: `7ed287043f6da1e3d53bc67a95b7377bb989382a`.
Feature CI: `34809014590` — success.

The frozen arbitrary-signal-space scope is retained through an arbitrary
sub-sigma-algebra. Only actions are finite, and all action payoffs are
integrable. The effective source change is only
`UEOT/V3/FreeInformationValue.lean` plus one top-level import.

The branch history diverges from main. **Never merge this branch directly.**
Once 74/106 is full-green, create a new clean integration from that main and
copy only the two effective file changes, then run the normal promotion gates.

## P-BRG-01 — active proof, uncounted

Frozen §26.3 contract:

- finite types and fixed `R_i > 0`;
- exact replicator recurrence and explicit closed form;
- `R_*` is the maximum fitness on the initially positive support;
- no mutation means no creation outside initial support;
- each initially supported suboptimal type carries an explicit
  `(R_i/R_*)^n` geometric factor;
- finite total suboptimal mass tends to zero exponentially;
- support maximizers keep their initial relative proportions.

Feature branch: `formal/pbrg01-fixed-fitness-v1`.
Current head: `4a7facca5fc312568890ba547d343b7a04bbf2ef`.
Current CI: `34810851201`.

Current modules:
- `UEOT/V3/FixedFitnessSelection.lean` — algebraic core;
- `UEOT/V3/FixedFitnessConcentration.lean` — source concentration layer.

Do not call this lane feature-green until current CI succeeds and the source
semantic audit confirms the total-mass exponential clause is represented at
full strength.

## Guards

- do not reopen counted green P-IDs absent source mismatch/CI regression;
- feature green never increments coverage;
- no `sorry`, `admit`, `native_decide`, or unsourced `axiom`;
- preserve frozen source strength; do not replace hard clauses by convenient
  finite/toy/Markov-only surrogates;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-REF-03 requires arbitrary signal spaces;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-BRG-01 includes concentration/extinction/maximizer-ratio clauses;
- P-KL-04/05 must remain at their frozen CTMC/Girsanov level.

## Recovery order

1. `UEOT_CORE3_LEAN_OPERATIONS.md`;
2. Issue #56 when available;
3. `PID_STATUS.yaml`;
4. `FORMALIZATION_STATE.md`;
5. `V3_COVERAGE_STATUS.md`;
6. this `HANDOFF_LATEST.md` fallback snapshot;
7. live main/branches/CI reconciliation.
