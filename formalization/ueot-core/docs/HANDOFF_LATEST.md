# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **92/106**;
- this ledger branch stages: **93/106**;
- pending after successful ledger lifecycle: **13**;
- proof main: `0aa8f233724c04a937a6bd1e35eb7e312cd4ecff`;
- P-GOA-04 proof PR: **#117**;
- proof PR root CI: `35524709704` — success;
- proof resulting-main root CI: `35525091956` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-GOA-04 is **PROOF-COMPLETE** but is not called COUNTED / 93 FULL-GREEN until
this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and the
resulting-main CI succeeds.

## P-GOA-04 — proof-complete lifecycle

Frozen §21.5 source obligations retained:

1. finite symmetric nonnegative irreducible substochastic baseline and perturbed
   killed kernels;
2. positive unit principal eigenvectors and baseline spectral gap
   `g = rho - lambda2 > 0`;
3. genuine Euclidean L2 operator perturbation `‖Khat-K‖ ≤ eta < g/2`;
4. exact principal-root perturbation `|rhohat-rho| ≤ eta`;
5. exact canonical total-variation bound on the squared principal-vector laws,
   `TV ≤ 2 * sqrt(2) * eta / g`;
6. no Frobenius substitution, hidden closeness/rank/PD/identifiability/interior
   strengthening.

Canonical theorem:
- `UEOT.V3.SymmetricKilledSpectralStability.p_goa_04`.

Proof evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- source-facing feature commit `ffdd703a02fcae801212c4a7a5f641684d940f64`;
- feature tree `e6f0d0328be4e2f1c2d13a5c054e512503011132`;
- feature root CI `35523847252` success;
- full local `lake build UEOT`: success (`8985` jobs);
- two independent final source/proof audits PASS;
- executable audit checked the symmetry/operator-norm bridges, squared-law PMF
  normalization and exact finite-PMF total-variation conversion;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pgoa04-main-integration@9b315810c7b5fcdff5f55504806f4c74eab8a079` from `main@cb6e960169994dc88e4a7f37e85f1c063607e3f9`;
- feature/integration tree `e6f0d0328be4e2f1c2d13a5c054e512503011132` identical;
- clean integration root CI `35524289735` success;
- proof PR #117 root CI `35524709704` success;
- proof main `0aa8f233724c04a937a6bd1e35eb7e312cd4ecff`;
- proof resulting-main root CI `35525091956` success.

## Previous FULL-GREEN checkpoint — 92/106

The P-DDH-02 ledger landed at
`main@cb6e960169994dc88e4a7f37e85f1c063607e3f9` and its resulting-main root CI
`35520947479` succeeded. P-DDH-02/03/04, P-GOA-01/02, P-QUO-01/02/03/04/05,
P-CTL-01, P-TEL-01 and all older counted P-IDs stay closed absent source
mismatch or main regression.

## Dynamic frontier after the 93 ledger closes

No next theorem branch is opened as part of this promotion. Current branchless
source/API audits place the leading uncounted candidates at:

- P-DDH-05 — Class D, L; executable direct singular-value/min-max probes are
  positive, with the indexed operator-norm Lipschitz/Weyl bridge still missing;
- P-GOA-03 — Class D, L-XL.

P-CORE-01 remains hard-blocked by P-GOA-03. The exact next lane must be selected
from the new 93/106 FULL-GREEN `main` only after this ledger finishes and a live
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

1. finish this **93/106 ledger lifecycle**: full local build -> branch root CI -> ledger PR exact-head root CI -> merge -> resulting-main exact-head root CI;
2. only after every ledger gate succeeds, record **93/106 FULL-GREEN** in Issue #56;
3. safely retire the P-GOA-04 feature/integration/ledger branches only after their applicable lifecycle gates are complete;
4. reconcile exact new `main`, re-run dynamic frontier/branch preflight, and open exactly one theorem branch;
5. current leading source/API candidate is P-DDH-05, subject to that live exact-main re-audit;
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
