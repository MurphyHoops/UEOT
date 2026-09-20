# UEOT Core Lean — Live Formalization State

> Recovery entry point. Integrated source-count truth is `V3_COVERAGE_STATUS.md`.
> GitHub Issue #56 carries the live cross-chat construction log and overrides
> stale fallback snapshots.

Last synchronized: **2026-09-20**

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
| integrated/proof-complete, staged by this checkpoint | **92** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **14** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **91/106**.
P-DDH-02 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@dabc8da9076b1ab764b5c6f06aed2d32be42ccfc`; proof resulting-main root CI
`35519437495` succeeded.

This ledger branch stages **92/106**. Do not call 92/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-DDH-02

Frozen Core 3 §23.3 requires the finite exponential-family log-partition
gradient/Hessian identities under a finite state space, strictly positive
baseline PMF, arbitrary prescribed finite-dimensional feature map and arbitrary
finite parameter, including dimension zero.

The formalization differentiates the finite partition sum directly, derives the
log-partition gradient as the normalized tilted feature mean, differentiates the
gradient dual by the quotient rule, and proves the resulting continuous
bilinear operator is exactly the tilted covariance. It adds no rank,
feature-independence, strict-convexity, positive-definite covariance,
identifiability, unique-parameter, or interior hypothesis.

Canonical theorem:
- `UEOT.V3.ExponentialFamilyCalculus.p_ddh_02`.

Supporting module:
- `UEOT.V3.ExponentialFamilyCalculus`.

Promotion evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- feature commit `e8ae0d2d1b4c4a44d0c0437b46babf392d72626e`;
- feature root CI `35518289262`: success;
- full local `lake build UEOT`: success (`8984` jobs);
- two independent final source/proof audits: PASS;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` for `ExponentialFamilyCalculus.p_ddh_02`: only standard `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pddh02-main-integration@de23f78ec8136695a469e05160266d61e14e061b` from `main@8afa467eccd826a44d6251d7b318e9a4b9fd23cd`;
- feature/integration tree hash `1157210901f7b027cac3b3d1fe9279e1a4c2ada7` identical;
- clean integration root CI `35518715443`: success;
- proof PR #115 root CI `35519091198`: success;
- proof main `dabc8da9076b1ab764b5c6f06aed2d32be42ccfc`;
- proof resulting-main root CI `35519437495`: success.

## Previous FULL-GREEN checkpoint — 91/106

P-DDH-03 and all earlier counted P-IDs remain closed. The 91/106 ledger landed
at `main@8afa467eccd826a44d6251d7b318e9a4b9fd23cd` with resulting-main CI
`35516201948` success.

P-QUO-03 and P-TEL-01 are already counted and must not be reopened or
re-counted merely because older compilation reports predate their promotion.

## Branchless frontier after the 92 ledger closes

No theorem branch is opened by this ledger lifecycle. Current read-only audits
place the leading uncounted fronts at:

- P-GOA-04: Class C, L; finite spectral infrastructure exists but several
  source-strength perturbation bridges remain;
- P-DDH-05: Class D, L after deeper singular-value perturbation audit;
- P-GOA-03: Class D, L-XL; recurrent decomposition and full Cesaro-mixture
  machinery are still missing.

P-CORE-01 remains hard-blocked by P-GOA-03. The next theorem lane must be
selected dynamically from the exact 92/106 FULL-GREEN main after this ledger
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
