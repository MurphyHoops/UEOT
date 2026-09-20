# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **91/106**;
- this ledger branch stages: **92/106**;
- pending after successful ledger lifecycle: **14**;
- proof main: `dabc8da9076b1ab764b5c6f06aed2d32be42ccfc`;
- P-DDH-02 proof PR: **#115**;
- proof PR root CI: `35519091198` — success;
- proof resulting-main root CI: `35519437495` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-DDH-02 is **PROOF-COMPLETE** but is not called COUNTED / 92 FULL-GREEN until
this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and the
resulting-main CI succeeds.

## P-DDH-02 — proof-complete lifecycle

Frozen §23.3 source obligations retained:

1. finite state space and strictly positive baseline `p0`;
2. arbitrary finite dimension `k`, including `k = 0`;
3. arbitrary prescribed feature map `F` and arbitrary parameter `theta`;
4. exact log-partition gradient equals the tilted feature mean;
5. exact Hessian equals the tilted covariance as a continuous bilinear operator;
6. no full-rank/feature-independence/strict-convexity/PD-covariance/
   identifiability/unique-parameter/interior assumption.

Canonical theorem:
- `UEOT.V3.ExponentialFamilyCalculus.p_ddh_02`.

Proof evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- source-facing feature commit `e8ae0d2d1b4c4a44d0c0437b46babf392d72626e`;
- feature tree `1157210901f7b027cac3b3d1fe9279e1a4c2ada7`;
- feature root CI `35518289262` success;
- full local `lake build UEOT`: success (`8984` jobs);
- two independent final source/proof audits PASS;
- executable audit checked the Hessian/fderiv bridge, `k = 0`, normalized tilt
  weights, and exact covariance evaluation;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pddh02-main-integration@de23f78ec8136695a469e05160266d61e14e061b` from `main@8afa467eccd826a44d6251d7b318e9a4b9fd23cd`;
- feature/integration tree `1157210901f7b027cac3b3d1fe9279e1a4c2ada7` identical;
- clean integration root CI `35518715443` success;
- proof PR #115 root CI `35519091198` success;
- proof main `dabc8da9076b1ab764b5c6f06aed2d32be42ccfc`;
- proof resulting-main root CI `35519437495` success.

## Previous FULL-GREEN checkpoint — 91/106

The P-DDH-03 ledger landed at
`main@8afa467eccd826a44d6251d7b318e9a4b9fd23cd` and its resulting-main root CI
`35516201948` succeeded. P-DDH-03/04, P-GOA-01/02, P-QUO-01/02/03/04/05,
P-CTL-01, P-TEL-01 and all older counted P-IDs stay closed absent source
mismatch or main regression.

## Dynamic frontier after the 92 ledger closes

No next theorem branch is opened as part of this promotion. Current branchless
source/API audits place the leading uncounted candidates at:

- P-GOA-04 — Class C, L;
- P-DDH-05 — Class D, L after deeper singular-value perturbation audit;
- P-GOA-03 — Class D, L-XL.

P-CORE-01 remains hard-blocked by P-GOA-03. The exact next lane must be selected
from the new 92/106 FULL-GREEN `main` only after this ledger finishes and a live
dependency/branch preflight is repeated.

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

1. finish this **92/106 ledger lifecycle**: full local build -> branch root CI -> ledger PR exact-head root CI -> merge -> resulting-main exact-head root CI;
2. only after every ledger gate succeeds, record **92/106 FULL-GREEN** in Issue #56;
3. safely retire the P-DDH-02 feature/integration/ledger branches only after their applicable lifecycle gates are complete;
4. reconcile exact new `main`, re-run dynamic frontier/branch preflight, and open exactly one theorem branch;
5. current leading source/API candidate is P-GOA-04, subject to that live exact-main re-audit;
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
