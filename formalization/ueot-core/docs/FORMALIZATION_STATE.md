# UEOT Core Lean — Formalization State and Frozen Ledger

## Current recovery scope — 2026-11-11

The repository-wide Core status entry is [core/status/CURRENT.md](../../../core/status/CURRENT.md).
This file connects that current entry to the retained frozen-source ledger; it
is not a live branch, owner, or CI feed. Resolve the actual `main`, worktree and
active task before resuming work.

| Layer | Adopted result and evidence |
|---|---|
| Frozen Core v3 source surface | **106/106 FULL-GREEN**, 106 unique, 0 partial, 0 pending; [source ledger](V3_COVERAGE_STATUS.md). This count remains fixed. |
| Classified Core definitive theory | **CLASSIFIED_CORE_CLOSED** under the preserved conditions and public revisions; [S0—S6 acceptance entry](compression/theory_completion/unified_closure/core_theory_closure_v1/README.md). |
| Finite reader hardening | PR #446: two-book clarification, written 2/3/4 task classification and source-specific rank-three boundary; [frozen evidence](../../../mathematics/review/CORE_DEFINITIVE_FREEZE_2026-11-11/README.md). These two additions have written proofs and exact checks, not dedicated new complete Lean endpoints. |
| Exact growth and internal attainment | PR #447: three production modules and the original `CoreTheoryClosure` public import, full permitted-policy upper bound and attainable growth contract, and the two internal-program attainment iff results; [source and validation](compression/theory_completion/unified_closure/core_growth_classification_v1/README.md). This work is complete, not a pending research candidate. |
| Empirical support | **UNVERIFIED**. Kernel proofs, finite exact checks and synthetic execution do not establish natural universality. |

The growth extension formalizes finite exponential upper and two-sided bounds,
the least positive common upper base, and internal attainment. The root-limit
and limsup interpretation is a written analysis consequence; it is not a
separate new Lean endpoint. The old `Valid` class, feedback contracts, PR441—443
and their disclosed trust boundaries remain intact.

The frozen [canonical source artifact](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md) is synchronized. The 2026-11-11 current-main byte check confirmed SHA-256 `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`. This closes the source-byte hygiene note retained in the historical snapshot below; it does not change the 106 count.

Use the relevant package's actual validation and source identity. Reuse
unchanged accepted evidence; a documentation refresh is not a new full Lean
build or a new CI run. The [current formalization README](../README.md) provides
source, public import and toolchain navigation.

## Retained frozen-ledger snapshot — 2026-09-26

The remainder records the original 106-P-ID completion lifecycle. Its Issue #56
references, staged-proof wording, historical branch fields and CI identifiers
belong to that lifecycle, not to the current post-106 task queue. The source-byte
synchronization note below is retained as the status at that checkpoint; use the
[current source record](../../../mathematics/README.md) for its successor.

---

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

## Current FULL-GREEN checkpoint

| operational state | count |
|---|---:|
| counted / FULL-GREEN | **106** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **0** |
| total | **106** |

The final P-CTL-03 proof and ledger lifecycles are closed. Proof main
`f12282642faf9477ed6afe3df4e630f5f38295ac` passed resulting-main root CI
`36247887665`. The final ledger then passed branch CI `36248485650`, PR #144
exact-head CI `36248944955`, merged at
`main@1e2a3924ef31b5dca589dca69c3838fc355b8850`, and passed exact
resulting-main root CI `36249418600`.

**Current counted state: 106/106 FULL-GREEN, 106 unique, 0 partial, 0 pending.**

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

P-CTL-03 is proof-complete and counted FULL-GREEN; the separate final ledger
lifecycle has completed through exact resulting-main CI.

## Final frontier after the 106 ledger closes

No theorem P-ID remains. The final ledger is green through resulting-main CI,
so the source-theorem state is 106 proved / 106 unique / 0 pending.

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
