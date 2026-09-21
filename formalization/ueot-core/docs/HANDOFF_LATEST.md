# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **98/106**;
- this ledger branch stages: **99/106**;
- pending after successful ledger lifecycle: **7**;
- proof main: `1aa9d4c0dd745a2909903c8d1083676b0ec11751`;
- P-PER-02 proof PR: **#129**;
- proof PR root CI: `35601980474` — success;
- proof resulting-main root CI: `35602757494` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-PER-02 is **PROOF-COMPLETE** but is not called COUNTED / 99 FULL-GREEN until
this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and the
resulting-main CI succeeds.

## P-PER-02 — proof-complete lifecycle

Frozen §8.4 source obligations retained:

1. a continuous-time Markov semigroup on a Polish space whose action sends
   bounded continuous functions to bounded continuous functions;
2. marginals are exactly `μ₀P_t` from one fixed initial probability law;
3. occupation measures are exactly the marginal time averages
   `bar μ_T = T⁻¹ ∫₀ᵀ μ₀P_t dt`;
4. tightness of the `T >= 1` occupation family yields a weakly convergent
   subsequence along every `T_n -> ∞`;
5. every such weak limit is invariant, using the exact
   `2s||f||∞/T` shift estimate and the Feller property; and
6. if every time marginal has mass one on a closed set `V`, every weak limit
   also has mass one on `V` by Portmanteau.

The source explicitly distinguishes this marginal occupation result from
sample-path empirical-frequency convergence, which would need ergodicity.

Canonical theorem:
- `UEOT.V3.PersistenceOccupation.FellerOccupationSystem.p_per_02`.

Proof evidence:
- final frozen-source/proof audits GREEN;
- source-facing feature commit
  `2e12c0dbad89f8cddf8f2d195353580a5559c190`;
- feature tree `fd32905323e09e14cba3b3950322a0e2dc5b47f7`;
- feature root CI `35600355442` success;
- focused/root/full local checks: success (`8991` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`);
- audited `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pper02-main-integration@959586d1161f27a7a5bbec88b0d1672cac39bc90`
  from `main@4d2016267c246400ce0a6e025f9330eae820eef8`;
- feature/integration tree `fd32905323e09e14cba3b3950322a0e2dc5b47f7`
  identical;
- integration focused/root/full local checks: success (`8991` jobs);
- clean integration root CI `35601197925` success;
- proof PR #129 exact-head root CI `35601980474` success;
- proof main `1aa9d4c0dd745a2909903c8d1083676b0ec11751`;
- proof resulting-main root CI `35602757494` success.

## Previous FULL-GREEN checkpoint — 98/106

The P-EVO-03 ledger landed at
`main@4d2016267c246400ce0a6e025f9330eae820eef8` and its resulting-main root CI
`35582525823` succeeded. P-EVO-03 and all older counted P-IDs stay closed
absent source mismatch or main regression.

## Dynamic frontier after the 99 ledger closes

No next theorem branch is opened as part of this promotion. The exact remaining
set after a successful 99/106 ledger lifecycle is:

- P-QSD-01
- P-QSD-04
- P-CTL-02
- P-CTL-03
- P-KL-04
- P-KL-05
- P-ALI-01

The exact next lane must be selected from the new 99/106 FULL-GREEN `main`
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

1. finish this **99/106 ledger lifecycle**: full local build -> branch root CI ->
   ledger PR exact-head root CI -> merge -> resulting-main exact-head root CI;
2. only after every ledger gate succeeds, record **99/106 FULL-GREEN** in Issue
   #56;
3. safely retire the P-PER-02 feature/integration/ledger branches only after
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
