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
| integrated/proof-complete, staged by this checkpoint | **106** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **0** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **105/106**.
P-CTL-03 has completed frozen-source audit, feature validation, clean
integration, proof PR, proof-main and proof resulting-main gates. Its proof is
on `main@f12282642faf9477ed6afe3df4e630f5f38295ac`; proof resulting-main
root CI `36247887665` succeeded.

This final ledger branch stages **106/106**. Do not call 106/106 FULL-GREEN
until the ledger branch passes root CI, the ledger PR passes root CI, the
ledger lands on `main`, and that exact resulting-main root CI succeeds.

## Newly staged proof — P-CTL-03

Frozen Core 3 §19.4 is the classical continuous-time diffusion HJB
verification theorem. The implementation keeps a bounded `C²` HJB candidate,
positive discount, all-action HJB domination, a measurable maximizing
selector, and the process-specific Itô/localization/integrability output
licensed by Appendix C. It does not substitute a discrete control theorem.

Pinned Mathlib does not provide a full controlled-SDE Itô stack. Following the
already accepted `RecoveryDynkin`/`GirsanovPathKL` pattern, `ItoRun` records
only the finite-horizon stochastic-calculus output that a valid model-specific
diffusion theorem must supply. Lean itself proves the HJB residual sign,
selector equality, bounded terminal decay, arbitrary-control upper bound and
infinite-horizon selector optimality.

Canonical theorem:
- `UEOT.V3.DiffusionHJBVerification.p_ctl_03`.

Promotion evidence:
- feature head `c1f2f922b3f27c2d67cdb33a8158cc12d7d62f33`;
- feature root CI `36246442641`: success;
- clean integration `9f4374c165d7d442fbe7c2bc16ce1ca5bab8941c`
  from `main@9923223189e2ede79a2129a5efe86471a222028d`;
- feature/integration tree identity
  `5a104e5f1f3e7d83782a1cb0e22ab070b094e29a`;
- integration root CI `36246910887`: success;
- proof PR #143 exact-head root CI `36247419494`: success;
- proof main `f12282642faf9477ed6afe3df4e630f5f38295ac`;
- proof resulting-main root CI `36247887665`: success;
- full local build: success (`9011/9011`);
- focused module build: success (`3225/3225`);
- prohibited-proof audit clean; audited axioms only `propext`,
  `Classical.choice`, `Quot.sound`.

## Previous FULL-GREEN checkpoint — 105/106

P-QSD-04 and all earlier counted P-IDs remain closed. The 105/106 ledger landed
at `main@9923223189e2ede79a2129a5efe86471a222028d` with resulting-main CI
`36245730807` success.

P-CTL-03 is proof-complete but remains staged, not counted FULL-GREEN, until
this separate final ledger lifecycle completes.

## Final frontier after the 106 ledger closes

No theorem P-ID remains after successful promotion. A green final ledger
establishes 106 proved / 106 unique / 0 pending at source-theorem level.

The separate canonical-source-byte public-repository synchronization task is
reproducibility hygiene and does not alter the P-ID proof count.

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
