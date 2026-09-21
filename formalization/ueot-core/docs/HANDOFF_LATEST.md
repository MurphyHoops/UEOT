# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **97/106**;
- this ledger branch stages: **98/106**;
- pending after successful ledger lifecycle: **8**;
- proof main: `4d581a675f4057069dbe19db7d0e182bfdf91ff8`;
- P-EVO-03 proof PR: **#127**;
- proof PR root CI: `35577642954` — success;
- proof resulting-main root CI: `35578270234` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-EVO-03 is **PROOF-COMPLETE** but is not called COUNTED / 98 FULL-GREEN until
this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and the
resulting-main CI succeeds.

## P-EVO-03 — proof-complete lifecycle

Frozen §25.4 source obligations retained:

1. finite primitive nonnegative mean matrix `M`;
2. full K-PF-01 data on the same `M`: `R>0`, positive `r,l`, both eigenrelations,
   `∑l=1`, `lr=1`, rank-one power asymptotics, positive Perron-eigendirection
   uniqueness and strict spectral dominance;
3. every nonzero nonnegative initial count row has positive `z₀r`;
4. exact scaled mean limit `R⁻ⁿ z₀Mⁿ → (z₀r)l`;
5. normalized mean type composition converges to `l`; and
6. every strictly positive linear valuation satisfying the source identity for
   all nonnegative rows has eigenvalue `R` and is a positive multiple of `r`.

Canonical theorem:
- `UEOT.V3.EvolutionPerronGrowth.p_evo_03`.

Proof evidence:
- dual independent final source/proof audits GREEN;
- source-facing feature commit
  `340a56d4ca19236bba141b79b8471ed95a512995`;
- feature tree `7ee94553049f5d6de825a9883695719e2399a4a7`;
- feature root CI `35576131678` success;
- focused/root/full local checks: success (`8990` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- audited `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pevo03-main-integration@11e17eaab6385017c1515afaaff1a460a91e79c6`
  from `main@85b3e410ab9a1ef71ca512c0e8f8f6a2f9aa6cb2`;
- feature/integration tree `7ee94553049f5d6de825a9883695719e2399a4a7` identical;
- integration focused/root/full local checks: success (`8990` jobs);
- clean integration root CI `35576926135` success;
- proof PR #127 exact-head root CI `35577642954` success;
- proof main `4d581a675f4057069dbe19db7d0e182bfdf91ff8`;
- proof resulting-main root CI `35578270234` success.

## Previous FULL-GREEN checkpoint — 97/106

The P-CORE-01 ledger landed at
`main@85b3e410ab9a1ef71ca512c0e8f8f6a2f9aa6cb2` and its resulting-main root CI
`35573090853` succeeded. P-CORE-01 and all older counted P-IDs stay closed absent
source mismatch or main regression.

## Dynamic frontier after the 98 ledger closes

No next theorem branch is opened as part of this promotion. The exact remaining
set after a successful 98/106 ledger lifecycle is:

- P-PER-02
- P-QSD-01
- P-QSD-04
- P-CTL-02
- P-CTL-03
- P-KL-04
- P-KL-05
- P-ALI-01

The exact next lane must be selected from the new 98/106 FULL-GREEN `main` only
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
- P-KL-04/05 stay at their frozen CTMC/Girsanov level;

## Exact continuation order

1. finish this **98/106 ledger lifecycle**: full local build -> branch root CI -> ledger PR exact-head root CI -> merge -> resulting-main exact-head root CI;
2. only after every ledger gate succeeds, record **98/106 FULL-GREEN** in Issue #56;
3. safely retire the P-EVO-03 feature/integration/ledger branches only after their applicable lifecycle gates are complete;
4. reconcile exact new `main`, re-run dynamic frontier/branch preflight, and open exactly one theorem branch;
5. repeat the full proof and separate ledger promotion lifecycle before any further count increment.

## Recovery order

1. `NEW_CHAT_BOOTSTRAP.md`;
2. `docs/REPOSITORY_BRANCH_GOVERNANCE.md`;
3. `UEOT_CORE3_LEAN_OPERATIONS.md`;
4. Issue #56 when available;
5. `V3_COVERAGE_STATUS.md`;
6. `FORMALIZATION_STATE.md`;
7. this fallback handoff;
8. live main/branches/PR/CI reconciliation.
