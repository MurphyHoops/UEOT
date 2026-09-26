# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **102/106**;
- this ledger branch stages: **103/106**;
- pending after successful ledger lifecycle: **3**;
- proof main: `7af0d8970a33063bb31a216bce97235a380571c0`;
- P-KL-04 proof PR: **#137**;
- proof PR root CI: `36222997612` — success;
- proof resulting-main root CI: `36224107001` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-KL-04 is **PROOF-COMPLETE** but is not called COUNTED / 103 FULL-GREEN until
this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and the
resulting-main CI succeeds.

## P-KL-04 — proof-complete lifecycle

Frozen §22.4 source obligations retained:

1. finite continuous-time jump generators and the full random-finite-jump path
   law, not a fixed-jump-count surrogate;
2. common initial state and source support inclusion;
3. explicit common-reference likelihood and Radon--Nikodym derivative;
4. Campbell/renewal identities derived from path densities rather than assumed
   compensator certificates;
5. signed jump-log recombination and real `llr` integrability;
6. `0 log 0 = 0` through `jumpLogRatio`; and
7. the final literal clock-time jump-rate integral.

Canonical theorem:
- `UEOT.V3.FiniteCTMCPathKL.p_kl_04`.

Proof evidence:
- final frozen-source/proof audit CLEAR, zero blockers;
- source-facing feature commit
  `79bc6873d9b445627f70017ae37c43e498332158`;
- feature tree `79049834494228824abbe6a7de487f790f926edc`;
- feature root CI `36222018778` success;
- focused/root/full local checks: success (`9008/9008`);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pkl04-main-integration@1117010ab9554ab073d47a6f7f16e7fc78ada214`
  from `main@91547a488ba9a1a86abbb4e5ead7ad5aa98b6bde`;
- feature/integration tree `79049834494228824abbe6a7de487f790f926edc`
  identical;
- integration root CI `36222441619` success;
- proof PR #137 exact-head root CI `36222997612` success;
- proof main `7af0d8970a33063bb31a216bce97235a380571c0`;
- proof resulting-main root CI `36224107001` success.

## Previous FULL-GREEN checkpoint — 102/106

The P-CTL-02 ledger landed at
`main@91547a488ba9a1a86abbb4e5ead7ad5aa98b6bde` and its resulting-main root CI
`36156516104` succeeded. P-CTL-02 and all older counted P-IDs stay closed absent
source mismatch or main regression.

## Dynamic frontier after the 103 ledger closes

No next theorem branch is opened as part of this promotion. The exact remaining
set after a successful 103/106 ledger lifecycle is:

- P-QSD-04
- P-CTL-03
- P-KL-05

The exact next lane must be selected from the new 103/106 FULL-GREEN `main`
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

1. finish this **103/106 ledger lifecycle**: full local build -> branch root CI ->
   ledger PR exact-head root CI -> merge -> resulting-main exact-head root CI;
2. only after every ledger gate succeeds, record **103/106 FULL-GREEN** in Issue
   #56;
3. safely retire the P-KL-04 feature/integration/ledger branches only after
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
