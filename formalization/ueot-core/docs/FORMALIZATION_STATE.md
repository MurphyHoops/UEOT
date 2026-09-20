# UEOT Core Lean — Live Formalization State

> Recovery entry point. Integrated source-count truth is `V3_COVERAGE_STATUS.md`.
> GitHub Issue #56 carries the live cross-chat construction log and overrides
> stale fallback snapshots.

Last synchronized: **2026-09-21**

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
| integrated/proof-complete, staged by this checkpoint | **93** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **13** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **92/106**.
P-GOA-04 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@0aa8f233724c04a937a6bd1e35eb7e312cd4ecff`; proof resulting-main root CI
`35525091956` succeeded.

This ledger branch stages **93/106**. Do not call 93/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-GOA-04

Frozen Core 3 §21.5 requires finite symmetric nonnegative irreducible
substochastic killed-kernel spectral stability under a genuine Euclidean
operator 2-norm perturbation bounded by `eta < g/2`, with exact principal-root
and squared-principal-law total-variation conclusions.

The formalization bridges matrix symmetry to self-adjoint Euclidean operators,
uses the exact L2 operator norm, proves the principal-root perturbation bound,
normalizes the squared eigenvector coordinates into PMFs, and derives the
canonical finite-space total-variation bound
`2 * sqrt(2) * eta / g`. It adds no Frobenius-norm substitution, hidden
closeness assumption, rank/positive-definite hypothesis, or identifiability
strengthening.

Canonical theorem:
- `UEOT.V3.SymmetricKilledSpectralStability.p_goa_04`.

Supporting module:
- `UEOT.V3.SymmetricKilledSpectralStability`.

Promotion evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- feature commit `ffdd703a02fcae801212c4a7a5f641684d940f64`;
- feature root CI `35523847252`: success;
- full local `lake build UEOT`: success (`8985` jobs);
- two independent final source/proof audits: PASS;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` for `SymmetricKilledSpectralStability.p_goa_04`: only standard `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pgoa04-main-integration@9b315810c7b5fcdff5f55504806f4c74eab8a079` from `main@cb6e960169994dc88e4a7f37e85f1c063607e3f9`;
- feature/integration tree hash `e6f0d0328be4e2f1c2d13a5c054e512503011132` identical;
- clean integration root CI `35524289735`: success;
- proof PR #117 root CI `35524709704`: success;
- proof main `0aa8f233724c04a937a6bd1e35eb7e312cd4ecff`;
- proof resulting-main root CI `35525091956`: success.

## Previous FULL-GREEN checkpoint — 92/106

P-DDH-02 and all earlier counted P-IDs remain closed. The 92/106 ledger landed
at `main@cb6e960169994dc88e4a7f37e85f1c063607e3f9` with resulting-main CI
`35520947479` success.

P-QUO-03 and P-TEL-01 are already counted and must not be reopened or
re-counted merely because older compilation reports predate their promotion.

## Branchless frontier after the 93 ledger closes

No theorem branch is opened by this ledger lifecycle. Current read-only audits
place the leading uncounted fronts at:

- P-DDH-05: Class D, L; executable direct singular-value/min-max probes are
  positive, but the indexed operator-norm Lipschitz/Weyl bridge remains;
- P-GOA-03: Class D, L-XL; recurrent decomposition and full Cesaro-mixture
  machinery are still missing.

P-CORE-01 remains hard-blocked by P-GOA-03. The next theorem lane must be
selected dynamically from the exact 93/106 FULL-GREEN main after this ledger
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
