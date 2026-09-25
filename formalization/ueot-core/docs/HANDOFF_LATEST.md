# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **101/106**;
- this ledger branch stages: **102/106**;
- pending after successful ledger lifecycle: **4**;
- proof main: `6a334b4c9870cf73ecda97a65965f822cf5e9e26`;
- P-CTL-02 proof PR: **#135**;
- proof PR root CI: `36141205611` — success;
- proof resulting-main root CI: `36142098525` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-CTL-02 is **PROOF-COMPLETE** but is not called COUNTED / 102 FULL-GREEN until
this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and the
resulting-main CI succeeds.

## P-CTL-02 — proof-complete lifecycle

Frozen §19.3 source obligations retained:

1. `X` and the fixed action space `A` remain compact metric spaces, with
   nonempty `A`, continuous reward, Markov transition kernel, and
   `0 < β < 1`;
2. weak continuity is represented by continuity of all continuous-test
   integrals and proved equivalent to continuity in Mathlib's weak
   `ProbabilityMeasure` topology;
3. the Bellman map is an actual self-map of `C(X, ℝ)` and is proved to be the
   exact `β`-contraction;
4. Banach contraction gives a unique continuous fixed point;
5. the measurable stationary maximizer is constructed from dense-sequence
   compact neighborhoods and a measurable Cauchy limit rather than assumed by
   a selection theorem; and
6. the resulting stationary deterministic policy is proved optimal against
   arbitrary randomized full-history causal policies.

Canonical theorem:
- `UEOT.V3.CompactFellerControl.Model.p_ctl_02`.

Proof evidence:
- final frozen-source/proof audit CLEAR, zero blockers;
- source-facing feature commit
  `4b17ec1219f95dd9fa0480f46beea6e585c122eb`;
- feature tree `7497670441126d08f2fdb91b15ada086d2a9565f`;
- feature root CI `36139857404` success;
- focused/root/full local checks: success (`8996` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pctl02-main-integration@863c9679b9d025a5f58282af4548fe5587e37860`
  from `main@7add6a361c8c46f7539d48ace389d403219b053d`;
- feature/integration tree `7497670441126d08f2fdb91b15ada086d2a9565f`
  identical;
- clean integration root CI `36140869360` success;
- proof PR #135 exact-head root CI `36141205611` success;
- proof main `6a334b4c9870cf73ecda97a65965f822cf5e9e26`;
- proof resulting-main root CI `36142098525` success.

## Previous FULL-GREEN checkpoint — 101/106

The P-ALI-01 ledger landed at
`main@7add6a361c8c46f7539d48ace389d403219b053d` and its resulting-main root CI
`36125245565` succeeded. P-ALI-01 and all older counted P-IDs stay closed absent
source mismatch or main regression.

## Dynamic frontier after the 102 ledger closes

No next theorem branch is opened as part of this promotion. The exact remaining
set after a successful 102/106 ledger lifecycle is:

- P-QSD-04
- P-CTL-03
- P-KL-04
- P-KL-05

The exact next lane must be selected from the new 102/106 FULL-GREEN `main`
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

1. finish this **102/106 ledger lifecycle**: full local build -> branch root CI ->
   ledger PR exact-head root CI -> merge -> resulting-main exact-head root CI;
2. only after every ledger gate succeeds, record **102/106 FULL-GREEN** in Issue
   #56;
3. safely retire the P-CTL-02 feature/integration/ledger branches only after
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
