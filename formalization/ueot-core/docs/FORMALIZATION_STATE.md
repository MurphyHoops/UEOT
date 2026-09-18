# UEOT Core Lean — Live Formalization State

> Recovery entry point. Integrated source-count truth is `V3_COVERAGE_STATUS.md`.
> GitHub Issue #56 carries the live cross-chat construction log and overrides
> stale fallback snapshots.

Last synchronized: **2026-09-18**

## Environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`
- exact canonical bytes in public repo: pending synchronization

## Current staged checkpoint

| operational state | count |
|---|---:|
| integrated/proof-complete, staged by this checkpoint | **88** |
| source audit prepared for next lane | **1** |
| active theorem proof branch | **0** |
| blocked | **0** |
| pending/not yet counted after this promotion | **18** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **87/106**.
P-GOA-01 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@85cf2781c78b63b0f69981951eacc86f54015b50`; proof resulting-main root CI
`35341843473` succeeded.

This ledger branch stages **88/106**. Do not call 88/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-GOA-01

Frozen Core 3 §21.2 fixes a finite stochastic kernel `P`, arbitrary initial
probability `mu0`, and the exact positive-N Cesaro averages

- `bar_mu_N = N^(-1) * sum_{t=0}^{N-1} mu0 P^t`;
- at least one convergent subsequence exists;
- every convergent subsequential limit `nu` satisfies `nu P = nu`.

The formalization establishes at source strength:

1. arbitrary finite row-stochastic kernels via `Matrix.rowStochastic ℝ S`;
2. arbitrary initial laws in `stdSimplex ℝ S`;
3. exact orbit `mu0 P^t` with stochastic-row preservation;
4. exact `N=n+1` Cesaro averaging over `t=0,...,N-1`;
5. the exact telescope `bar_mu_N P - bar_mu_N = (mu0 P^N - mu0)/N`;
6. boundary-term convergence to zero from simplex coordinate bounds;
7. compact subsequence extraction and invariance of every convergent
   subsequential limit by residual continuity.

Canonical theorem:
- `UEOT.V3.FiniteCesaroInvariant.p_goa_01`.

Supporting modules:
- `UEOT.V3.FiniteCesaroInvariant`.

Promotion evidence:
- canonical frozen source hash independently verified against the project File Library original;
- feature commit `3920995eb111c01cffcd0c6369182f70bb78e7f3`;
- feature root target `lake build UEOT`: success (`8980` jobs);
- independent source-semantic re-audit: pass;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` for `FiniteCesaroInvariant.p_goa_01`: only standard `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pgoa01-main-integration@0f61d3539fae0c72b9465189122f5308b7079621`;
- feature/integration tree hash `91af9fcb4901be6719a9ac61cd502a1de11915d1`;
- clean integration root CI `35340642119`: success;
- proof PR #107 root CI `35341218386`: success;
- proof main `85cf2781c78b63b0f69981951eacc86f54015b50`;
- proof resulting-main root CI `35341843473`: success.

## Previous FULL-GREEN checkpoint — 87/106

P-QUO-05 and all earlier counted P-IDs remain closed. The 87/106 ledger landed
at `main@f3f7945ddae12ad95eedf3c7e773354456d59564` with resulting-main CI
`35335445145` success.

P-QUO-03 and P-TEL-01 are already counted and must not be reopened or
re-counted merely because older compilation reports predate their promotion.

## Next source-to-main lane after the 88 ledger closes

No theorem branch is opened by this ledger lifecycle. The next recommended lane
is P-GOA-02. Frozen §21.3 requires the finite Dobrushin coefficient, exact TV
contraction, uniqueness when `alpha(P)<1`, and the stationary perturbation bound
`epsilon/(1-alpha(P))`. Existing UEOT event-supremum total variation and finite
PMF bridges can be reused, but the finite row algebra must preserve the standard
`1/2` normalization. P-CORE-01 remains blocked until the required GOA stability
layer is established.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available,
   `V3_COVERAGE_STATUS.md`, this file, then the fallback handoff.
2. Reconcile live `main`, active branches, PRs and Actions before mutation.
3. Never reopen counted green P-IDs absent a substantive frozen-source mismatch
   or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green, integration green and proof-main green never increment
   coverage.
6. No `sorry`, Lean `admit`, `native_decide`, or unsourced `axiom`.
7. Use CI waiting time for source/API audit only; do not open a conflicting
   proof lane while a promotion lifecycle is active.
8. After a proof resulting-main succeeds, use a separate docs-only ledger
   lifecycle before incrementing source coverage.
