# UEOT Core Lean — Live Formalization State

> Recovery entry point. Integrated source-count truth is `V3_COVERAGE_STATUS.md`.
> GitHub Issue #56 carries the live cross-chat construction log and overrides
> stale fallback snapshots.

Last synchronized: **2026-09-26**

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
| integrated/proof-complete, staged by this checkpoint | **105** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **1** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **104/106**.
P-QSD-04 has completed frozen-source audit, feature validation, clean
integration, proof PR, proof-main and proof resulting-main gates. Its proof is
on `main@5c88124a5c2f8ef0fd53d685c82f553917a1c6f7`; proof resulting-main
root CI `36243627501` succeeded.

This ledger branch stages **105/106**. Do not call 105/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-QSD-04

Frozen Core 3 §10.4 is the reversible killed-diffusion spectral QSD theorem.
The implementation retains a genuine continuous-time killed kernel semigroup,
ties its evolved laws to the spectral densities, keeps a compact symmetric
resolvent witness on `L²(m)`, and records only the standard
compact-self-adjoint spectral expansion/remainder estimate licensed by
Appendix C. Lean then proves the L²→L¹ step, eventual survival lower bound,
normalization and total-variation convergence at the exact spectral-gap rate.

Canonical theorem:
- `UEOT.V3.ReversibleKilledSpectralQSD.SpectralData.p_qsd_04`.

Promotion evidence:
- feature head `ee0d942c8c6e4913afd6fc803b8ecd0a1f26491c`;
- feature root CI `36242678627`: success;
- clean integration `7b37181280718b7ca73a3ba7cf46f39e75a13359`
  from `main@9a8a6261ca18c45cd2773c4cb1026bc450b32428`;
- feature/integration tree identity
  `0c88c8fd5d29281bdaf9896935d697127dbfa1da`;
- integration root CI `36242788142`: success;
- proof PR #141 exact-head root CI `36243218374`: success;
- proof main `5c88124a5c2f8ef0fd53d685c82f553917a1c6f7`;
- proof resulting-main root CI `36243627501`: success;
- full local build: success (`9010/9010`);
- prohibited-proof audit clean; audited axioms only `propext`,
  `Classical.choice`, `Quot.sound`.

## Previous FULL-GREEN checkpoint — 104/106

P-KL-05 and all earlier counted P-IDs remain closed. The 104/106 ledger landed
at `main@9a8a6261ca18c45cd2773c4cb1026bc450b32428` with resulting-main CI
`36234355278` success.

P-QSD-04 is proof-complete but remains staged, not counted FULL-GREEN, until
this separate ledger lifecycle completes.

## Branchless frontier after the 105 ledger closes

No theorem branch is opened by this ledger lifecycle. After a successful
105/106 promotion, the remaining P-ID is exactly P-CTL-03.

The final theorem lane must be opened only from the exact 105/106 FULL-GREEN
main after this ledger finishes.
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
