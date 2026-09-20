# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **94/106**;
- this ledger branch stages: **95/106**;
- pending after successful ledger lifecycle: **11**;
- proof main: `6f9173ee290e01838e4746faba6429928399b98c`;
- P-GOA-03 proof PR: **#121**;
- proof PR root CI: `35536497250` — success;
- proof resulting-main root CI: `35536908530` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-GOA-03 is **PROOF-COMPLETE** but is not called COUNTED / 95 FULL-GREEN until
this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and the
resulting-main CI succeeds.

## P-GOA-03 — proof-complete lifecycle

Frozen §21.4 source obligations retained:

1. one common finite state space with the same transient set and same literal
   recurrent-class partition before and after perturbation;
2. actual row-stochastic kernels whose `Q` and direct class-entry `R` blocks
   are pointwise linked to the stored decomposition;
3. `N=(I-Q)⁻¹`, `H=NR`, the exact max-row-sum perturbation hypotheses and
   smallness condition `‖N‖∞ epsQ < 1`;
4. the exact source `B_H` numerator/denominator;
5. actual same-initial-state periodic-safe Cesaro limits for baseline and
   perturbed chains;
6. exact TV coefficient `1/2`, with perturbed absorption weights multiplying
   the within-class stationary-law errors;
7. recurrent support/class preservation is mandatory; no changed-class case is
   silently generalized into the theorem.

Canonical theorem:
- `UEOT.V3.FiniteRecurrentDecompositionStability.p_goa_03`.

Proof evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- source-facing feature commits
  `8cd02864498ff369b59e9e4b1913082558bd2820` and
  `c1ff6baecdaa7c56a8ade42fbffaeeddf42ec909`;
- feature tree `3c956eadc54fd67a0784af9d46d21ecb88acd764`;
- final feature root CI `35535448015` success;
- full local `lake build UEOT`: success (`8987` jobs);
- two independent final source/proof audits PASS;
- executable audits checked exact resolvent algebra, actual-kernel block links,
  recurrent communication/uniqueness, periodic-safe Cesaro convergence,
  empty-transient degeneracy and exact TV orientation;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pgoa03-main-integration@4d518420cd93e4130a1cd59ceccf888dc9638b6c`
  from `main@cf8aaa8b91b3096cd05d60ad148ada14cc773924`;
- feature/integration tree `3c956eadc54fd67a0784af9d46d21ecb88acd764` identical;
- clean integration root CI `35536081037` success;
- proof PR #121 root CI `35536497250` success;
- proof main `6f9173ee290e01838e4746faba6429928399b98c`;
- proof resulting-main root CI `35536908530` success.

## Previous FULL-GREEN checkpoint — 94/106

The P-DDH-05 ledger landed at
`main@cf8aaa8b91b3096cd05d60ad148ada14cc773924` and its resulting-main root CI
`35530223703` succeeded. P-DDH-05, P-GOA-04, P-DDH-02/03/04, P-GOA-01/02,
P-QUO-01/02/03/04/05, P-CTL-01, P-TEL-01 and all older counted P-IDs stay closed
absent source mismatch or main regression.

## Dynamic frontier after the 95 ledger closes

No next theorem branch is opened as part of this promotion. Current branchless
frontier guidance is:

- P-CORE-01 — the recurrent-structure blocker from P-GOA-03 is now discharged;
  exact 95/106-main source/dependency re-audit is required before opening it;
- P-PER-02 / P-QSD-01 — read-only alternatives that still require new
  continuous-time semigroup / occupation-measure infrastructure.

The exact next lane must be selected from the new 95/106 FULL-GREEN `main` only
after this ledger finishes and a live dependency/branch preflight is repeated.

## Guards

- do not reopen counted green P-IDs absent source mismatch/CI regression;
- feature/integration/proof-main green never increments source coverage;
- no `sorry`, Lean `admit`, `native_decide`, or unsourced `axiom`;
- preserve frozen source strength; no finite/toy/assumed-conclusion replacement
  of a stronger source theorem;
- source-object identity must be explicit; generalization alone does not count
  without a bridge back to the frozen object;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-KL-04/05 stay at their frozen CTMC/Girsanov level;
- P-EVO-03 requires the full K-PF-01 asymptotic package.

## Exact continuation order

1. finish this **95/106 ledger lifecycle**: full local build -> branch root CI -> ledger PR exact-head root CI -> merge -> resulting-main exact-head root CI;
2. only after every ledger gate succeeds, record **95/106 FULL-GREEN** in Issue #56;
3. safely retire the P-GOA-03 feature/integration/ledger branches only after their applicable lifecycle gates are complete;
4. reconcile exact new `main`, re-run dynamic frontier/branch preflight, and open exactly one theorem branch;
5. first re-audit P-CORE-01 now that the P-GOA-03 recurrent-structure blocker is discharged, while retaining P-PER-02 / P-QSD-01 as alternatives;
6. repeat the full proof and separate ledger promotion lifecycle before any further count increment.

## Recovery order

1. `NEW_CHAT_BOOTSTRAP.md`;
2. `docs/REPOSITORY_BRANCH_GOVERNANCE.md`;
3. `UEOT_CORE3_LEAN_OPERATIONS.md`;
4. Issue #56 when available;
5. `V3_COVERAGE_STATUS.md`;
6. `FORMALIZATION_STATE.md`;
7. this fallback handoff;
8. live main/branches/PR/CI reconciliation.
