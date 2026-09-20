# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **90/106**;
- this ledger branch stages: **91/106**;
- pending after successful ledger lifecycle: **15**;
- proof main: `6e2a179d9fad8293b02b0f47a971f4083eabbeb3`;
- P-DDH-03 proof PR: **#113**;
- proof PR root CI: `35514474988` — success;
- proof resulting-main root CI: `35514827747` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-DDH-03 is **PROOF-COMPLETE** but is not called COUNTED / 91 FULL-GREEN until
this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and the
resulting-main CI succeeds.

## P-DDH-03 — proof-complete lifecycle

Frozen §23.3 source obligations retained:

1. finite state space and strictly positive baseline `p0`;
2. arbitrary finite dimension, prescribed feature map `F`, arbitrary finite
   parameter `theta`;
3. only assumes that the displayed exponential tilt realizes target moment `m`;
4. minimization ranges over every probability law with the same moment;
5. equality iff the competing law is exactly the tilt;
6. no claim that boundary targets admit finite-parameter realization;
7. no full-rank/feature-independence/strict-convexity/PD-covariance/
   unique-parameter/interior assumption and no dependency on P-DDH-02.

Canonical theorem:
- `UEOT.V3.ExponentialFamilyIProjection.p_ddh_03`.

Proof evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- source-facing feature commit `360f5b941d57a5d0b2edf73924c217034dfd0bcd`;
- feature tree `1c0278bb9b21501ebb30733ed77f2cb48f3228a0`;
- feature root CI `35513672240` success;
- full local `lake build UEOT`: success (`8983` jobs);
- two independent final source/proof audits PASS;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pddh03-main-integration@4bce0870076e740f21e14411b8741493c4d61e84` from `main@22a0b0d68201a18d574c0d841679f511a86994b9`;
- feature/integration tree `1c0278bb9b21501ebb30733ed77f2cb48f3228a0` identical;
- clean integration root CI `35514069336` success;
- proof PR #113 root CI `35514474988` success;
- proof main `6e2a179d9fad8293b02b0f47a971f4083eabbeb3`;
- proof resulting-main root CI `35514827747` success.

## Previous FULL-GREEN checkpoint — 90/106

The P-DDH-04 ledger landed at
`main@22a0b0d68201a18d574c0d841679f511a86994b9` and its resulting-main root CI
`35511293247` succeeded. P-DDH-04, P-GOA-01/02, P-QUO-01/02/03/04/05,
P-CTL-01, P-TEL-01 and all older counted P-IDs stay closed absent source
mismatch or main regression.

## Dynamic frontier after the 91 ledger closes

No next theorem branch is opened as part of this promotion. Current branchless
source/API audits place the leading uncounted candidates at:

- P-DDH-02 — Class C, M / upper-M; finite log-partition gradient and
  Hessian/covariance; exact-main probes compile the gradient and raw Hessian;
- P-GOA-04 — Class C, L;
- P-DDH-05 — Class D, L after deeper singular-value perturbation audit;
- P-GOA-03 — Class D, L-XL.

P-CORE-01 remains hard-blocked by P-GOA-03. The exact next lane must be selected
from the new 91/106 FULL-GREEN `main` only after this ledger finishes and a live
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

1. finish this **91/106 ledger lifecycle**: full local build -> branch root CI -> ledger PR exact-head root CI -> merge -> resulting-main exact-head root CI;
2. only after every ledger gate succeeds, record **91/106 FULL-GREEN** in Issue #56;
3. safely retire the P-DDH-03 feature/integration/ledger branches only after their applicable lifecycle gates are complete;
4. reconcile exact new `main`, re-run dynamic frontier/branch preflight, and open exactly one theorem branch;
5. current leading source/API candidate is P-DDH-02, subject to that live exact-main re-audit;
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
