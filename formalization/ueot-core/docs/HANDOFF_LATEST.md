# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **99/106**;
- this ledger branch stages: **100/106**;
- pending after successful ledger lifecycle: **6**;
- proof main: `ac17ea1a0859b364542fa4996de1e7458b94b53a`;
- P-QSD-01 proof PR: **#131**;
- proof PR root CI: `35629472501` attempt 2 — success;
- proof resulting-main root CI: `35900895439` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-QSD-01 is **PROOF-COMPLETE** but is not called COUNTED / 100 FULL-GREEN until
this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and the
resulting-main CI succeeds.

## P-QSD-01 — proof-complete lifecycle

Frozen §10.1 source obligations retained:

1. a killed subprobability semigroup and one fixed initial law define the
   literal conditioned family `μ_t^c = μP_t^V / (μP_t^V1)`;
2. `μ_t^c -> q` in total variation;
3. `qP_s^V1 > 0` for every finite nonzero `s`;
4. survival is right-continuous at zero;
5. semigroup shifting and TV convergence imply the QSD identity; and
6. multiplicative positive survival is exponential with a rate `λ >= 0`,
   allowing `λ = 0` in the no-absorption case.

Canonical theorem:
- `UEOT.V3.QSDTVLimit.p_qsd_01`.

Proof evidence:
- final frozen-source/proof audits GREEN;
- source-facing feature commit
  `b9625635c10cc114e854bfc1e1d7b2af277a47d8`;
- feature tree `f269847d42b34f5c7cd30236e011aa841a0aafb7`;
- feature root CI `35624526524` success;
- focused/root/full local checks: success (`8992` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pqsd01-main-integration@10a37206f049684c292c53d7826087f05580d489`
  from `main@9b00f80e091a80cc335cd592e527d0e98253f5f7`;
- feature/integration tree `f269847d42b34f5c7cd30236e011aa841a0aafb7`
  identical;
- integration focused/root/full local checks: success (`8992` jobs);
- clean integration root CI `35628806058` success;
- proof PR #131 exact-head root CI `35629472501` attempt 2 success;
- proof main `ac17ea1a0859b364542fa4996de1e7458b94b53a`;
- proof resulting-main root CI `35900895439` success.

## Previous FULL-GREEN checkpoint — 99/106

The P-PER-02 ledger landed at
`main@9b00f80e091a80cc335cd592e527d0e98253f5f7` and its resulting-main root CI
`35605364675` succeeded. P-PER-02 and all older counted P-IDs stay closed
absent source mismatch or main regression.

## Dynamic frontier after the 100 ledger closes

No next theorem branch is opened as part of this promotion. The exact remaining
set after a successful 100/106 ledger lifecycle is:

- P-QSD-04
- P-CTL-02
- P-CTL-03
- P-KL-04
- P-KL-05
- P-ALI-01

The exact next lane must be selected from the new 100/106 FULL-GREEN `main`
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

1. finish this **100/106 ledger lifecycle**: full local build -> branch root CI ->
   ledger PR exact-head root CI -> merge -> resulting-main exact-head root CI;
2. only after every ledger gate succeeds, record **100/106 FULL-GREEN** in Issue
   #56;
3. safely retire the P-QSD-01 feature/integration/ledger branches only after
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
