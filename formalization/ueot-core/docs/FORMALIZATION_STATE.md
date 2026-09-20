# UEOT Core Lean — Live Formalization State

> Recovery entry point. Integrated source-count truth is `V3_COVERAGE_STATUS.md`.
> GitHub Issue #56 carries the live cross-chat construction log and overrides
> stale fallback snapshots.

Last synchronized: **2026-09-19**

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
| integrated/proof-complete, staged by this checkpoint | **90** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **16** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **89/106**.
P-DDH-04 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@a0a92b015e4a95b97baa569e44ddbda41b1f3b0b`; proof resulting-main root CI
`35390116056` succeeded.

This ledger branch stages **90/106**. Do not call 90/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-DDH-04

Frozen Core 3 §23.4 requires one common differentiable map into `R^2`, shared
across all compared environment responses.  At the same budget point, every
response Jacobian factors through the same `Dz`, so the vertical stack has rank
at most two.

The formalization uses a common `z`, explicit differentiability of `z` at `B`
and each outer row at `z B`, `ContinuousLinearMap.pi` for the vertical stack,
the Fréchet chain rule, and the matrix rank bound through a two-column factor.
It neither stacks different budget points nor substitutes separate rank-two
conditions for the common bottleneck hypothesis.

Canonical theorem:
- `UEOT.V3.CommonBottleneckRank.p_ddh_04`.

Supporting module:
- `UEOT.V3.CommonBottleneckRank`.

Promotion evidence:
- canonical frozen source hash reverified before implementation;
- feature commit `91a5043899a843fe7a43c43e9aa827700636e461`;
- feature root CI `35364508901`: success;
- full local `lake build UEOT`: success (`8982` jobs);
- independent source-semantic audit: PASS;
- independent final Lean audit: PASS;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` for `CommonBottleneckRank.p_ddh_04`: only standard `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pddh04-main-integration@4f9df47cad85da878a528c08f05d64c8665b656d` from `main@aa9c2473849a960a3c25ad35410da68a79c9e164`;
- feature/integration tree hash `ac5bd0c2f12c89a333c5d56324a1706a0554401a` identical;
- clean integration root CI `35388778412`: success;
- proof PR #111 root CI `35389378056`: success;
- proof main `a0a92b015e4a95b97baa569e44ddbda41b1f3b0b`;
- proof resulting-main root CI `35390116056`: success.

## Previous FULL-GREEN checkpoint — 89/106

P-GOA-02 and all earlier counted P-IDs remain closed. The 89/106 ledger landed
at `main@aa9c2473849a960a3c25ad35410da68a79c9e164` with resulting-main CI
`35352566122` success.

P-QUO-03 and P-TEL-01 are already counted and must not be reopened or
re-counted merely because older compilation reports predate their promotion.

## Branchless frontier after the 90 ledger closes

No theorem branch is opened by this ledger lifecycle. Current read-only audits
place the leading uncounted fronts at:

- P-DDH-03: Class C, M; finite exponential-family moment-constrained KL
  minimization, with a viable `Measure.tilted` / log-likelihood-ratio route;
- P-DDH-02: Class C, M; finite log-partition gradient and Hessian/covariance;
- P-GOA-04: Class C, L; finite spectral infrastructure exists but several
  source-strength perturbation bridges remain;
- P-DDH-05: Class D, L after deeper singular-value perturbation audit;
- P-GOA-03: Class D, L-XL; recurrent decomposition and full Cesaro-mixture
  machinery are still missing.

P-CORE-01 remains hard-blocked by P-GOA-03. The next theorem lane must be
selected dynamically from the exact 90/106 FULL-GREEN main after this ledger
finishes, rather than being opened early from this staged branch.

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
