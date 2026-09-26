# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **104/106**;
- this ledger branch stages: **105/106**;
- pending after successful ledger lifecycle: **1**;
- proof main: `5c88124a5c2f8ef0fd53d685c82f553917a1c6f7`;
- P-QSD-04 proof PR: **#141**;
- proof PR root CI: `36243218374` — success;
- proof resulting-main root CI: `36243627501` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-QSD-04 is **PROOF-COMPLETE** but is not called COUNTED / 105 FULL-GREEN until
this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and the
resulting-main CI succeeds.

## P-QSD-04 — proof-complete lifecycle

Frozen §10.4 source obligations retained:

1. genuine continuous-time killed/subprobability semigroup rather than a
   finite-state surrogate;
2. evolved density explicitly represents the killed-semigroup law;
3. compact symmetric resolvent witness on finite-measure `L²(m)`;
4. positive principal mode and strict `lambda2-lambda1` spectral gap;
5. Appendix-C-licensed spectral expansion and L² remainder bound only;
6. L²→L¹, normalization, TV convergence and eventual survival lower bound are
   proved in Lean rather than assumed; and
7. the final survival inequality is written on the actual killed-semigroup
   survival mass.

Canonical theorem:
- `UEOT.V3.ReversibleKilledSpectralQSD.SpectralData.p_qsd_04`.

Proof evidence:
- feature `ee0d942c8c6e4913afd6fc803b8ecd0a1f26491c`, root CI
  `36242678627` success;
- clean integration `7b37181280718b7ca73a3ba7cf46f39e75a13359` from
  `main@9a8a6261ca18c45cd2773c4cb1026bc450b32428`;
- feature/integration tree `0c88c8fd5d29281bdaf9896935d697127dbfa1da`
  identical;
- integration root CI `36242788142` success;
- proof PR #141 exact-head root CI `36243218374` success;
- proof main `5c88124a5c2f8ef0fd53d685c82f553917a1c6f7`;
- proof resulting-main root CI `36243627501` success;
- local official build success (`9010/9010`);
- prohibited-proof audit clean; audited axioms only `propext`,
  `Classical.choice`, `Quot.sound`.

## Previous FULL-GREEN checkpoint — 104/106

The P-KL-05 ledger landed at
`main@9a8a6261ca18c45cd2773c4cb1026bc450b32428` and its resulting-main root CI
`36234355278` succeeded. P-KL-05 and all older counted P-IDs stay closed absent
source mismatch or main regression.

## Dynamic frontier after the 105 ledger closes

No next theorem branch is opened as part of this promotion. The exact remaining
set after a successful 105/106 ledger lifecycle is:

- P-CTL-03

The final theorem lane must be opened from the new 105/106 FULL-GREEN `main`
only after this ledger finishes and a live dependency/branch preflight is
repeated.
## Guards

- do not reopen counted green P-IDs absent source mismatch/CI regression;
- feature/integration/proof-main green never increments source coverage;
- no `sorry`, Lean `admit`, `native_decide`, or unsourced `axiom`;
- preserve frozen source strength; no finite/toy/assumed-conclusion replacement
  of a stronger source theorem;
- source-object identity must be explicit; generalization alone does not count
  without a bridge back to the frozen object;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-KL-04/05 stay at their frozen CTMC/Girsanov level.

## Exact continuation order

1. finish this **105/106 ledger lifecycle**: full local build -> branch root CI ->
   ledger PR exact-head root CI -> merge -> resulting-main exact-head root CI;
2. only after every ledger gate succeeds, record **105/106 FULL-GREEN** in Issue
   #56;
3. safely retire the P-QSD-04 feature/integration/ledger branches only after
   their applicable lifecycle gates are complete;
4. reconcile exact new `main`, re-run dynamic frontier/branch preflight, and
   open exactly one theorem branch;
5. repeat the full proof and separate ledger promotion lifecycle before any
   further count increment.

## Recovery order

1. `NEW_CHAT_BOOTSTRAP.md`;
2. `docs/REPOSITORY_BRANCH_GOVERNANCE.md`;
3. `UEOT_CORE3_LEAN_OPERATIONS.md`;
4. Issue #56 when available;
5. `V3_COVERAGE_STATUS.md`;
6. `FORMALIZATION_STATE.md`;
7. this fallback handoff;
8. live main/branches/PR/CI reconciliation.
