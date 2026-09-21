# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **95/106**;
- this ledger branch stages: **96/106**;
- pending after successful ledger lifecycle: **10**;
- proof main: `ab9c4c220f442eec2b2e14709a3285e6dd01a066`;
- P-EVO-04 proof PR: **#123**;
- proof PR root CI: `35560162916` — success;
- proof resulting-main root CI: `35560658256` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-EVO-04 is **PROOF-COMPLETE** but is not called COUNTED / 96 FULL-GREEN until
this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and the
resulting-main CI succeeds.

## P-EVO-04 — proof-complete lifecycle

Frozen §25.5 source obligations retained:

1. finite-type true population counts with finite first moments;
2. literal vector conditional mean `E[Z_{n+1}|F_n]=Z_nM`;
3. K-PF-01 consequences `R>0`, `r>0`, `Mr=Rr`;
4. exact normalized reproductive value `W_n=R^{-n}Z_nr`;
5. nonnegativity, integrability and the actual martingale property;
6. deterministic finite initial counts and `EW_n=Z_0r`;
7. no UI, `L¹)-convergence or nonextinction-positivity overclaim.

Canonical theorem:
- `UEOT.V3.EvolutionReproductiveMartingale.p_evo_04`.

Proof evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- source-facing feature commit
  `f09c411f41c4386089cab17f6fcdc536314b762c`;
- feature tree `f162b2c9a1f34d55d58185eaaa9dfe0f94b2f540`;
- feature root CI `35539758527` success;
- full local `lake build UEOT`: success (`8988` jobs);
- two independent final source/proof audits PASS;
- executable audits checked vector-to-scalar conditional expectation,
  normalization algebra, martingale construction, deterministic initial-value
  expectation and root-import reachability;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pevo04-main-integration@1c167457bbfa27f7ec3f60861479aba6f75303f5`
  from `main@ee529be7008b38dbe928223ef1beebbd49db0912`;
- feature/integration tree `f162b2c9a1f34d55d58185eaaa9dfe0f94b2f540` identical;
- clean integration root CI `35559166344` success;
- proof PR #123 root CI `35560162916` success;
- proof main `ab9c4c220f442eec2b2e14709a3285e6dd01a066`;
- proof resulting-main root CI `35560658256` success.

## Previous FULL-GREEN checkpoint — 95/106

The P-GOA-03 ledger landed at
`main@ee529be7008b38dbe928223ef1beebbd49db0912` and its resulting-main root CI
`35538326271` succeeded. P-GOA-03, P-DDH-05, P-GOA-04, P-DDH-02/03/04,
P-GOA-01/02, P-QUO-01/02/03/04/05, P-CTL-01, P-TEL-01 and all older counted
P-IDs stay closed absent source mismatch or main regression.

## Dynamic frontier after the 96 ledger closes

No next theorem branch is opened as part of this promotion. Current branchless
frontier guidance is:

- P-CORE-01 — exact 96/106-main source/dependency re-audit is required before
  opening it;
- P-EVO-03 — still uncounted and requires the full K-PF-01 asymptotic package;
- P-PER-02 / P-QSD-01 — read-only alternatives that still require new
  continuous-time semigroup / occupation-measure infrastructure.

The exact next lane must be selected from the new 96/106 FULL-GREEN `main` only
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

1. finish this **96/106 ledger lifecycle**: full local build -> branch root CI -> ledger PR exact-head root CI -> merge -> resulting-main exact-head root CI;
2. only after every ledger gate succeeds, record **96/106 FULL-GREEN** in Issue #56;
3. safely retire the P-EVO-04 feature/integration/ledger branches only after their applicable lifecycle gates are complete;
4. reconcile exact new `main`, re-run dynamic frontier/branch preflight, and open exactly one theorem branch;
5. re-audit the exact 96/106 frontier, including P-CORE-01 and P-EVO-03, while retaining P-PER-02 / P-QSD-01 as alternatives;
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
