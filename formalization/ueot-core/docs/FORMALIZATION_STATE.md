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
| integrated/proof-complete, staged by this checkpoint | **98** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **8** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **97/106**.
P-EVO-03 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@4d581a675f4057069dbe19db7d0e182bfdf91ff8`; proof resulting-main root CI
`35578270234` succeeded.

This ledger branch stages **98/106**. Do not call 98/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-EVO-03

Frozen Core 3 §25.4 takes a finite primitive nonnegative mean matrix `M` and the
full K-PF-01 Perron package. For every nonzero nonnegative initial count row it
requires the scaled mean limit `R⁻ⁿ z₀Mⁿ → (z₀r)l`, normalized mean composition
convergence to `l`, and uniqueness of every strictly positive linear
reproductive valuation.

The implementation keeps the K-PF interface tied to the same `M`, derives the
positive initial reproductive value, finite-sum scaled coordinate and mass
limits, eventual positive denominator and ratio convergence, then derives
`Mw = ρw` from the valuation identity by coordinate unit rows before invoking
the positive Perron eigenvector uniqueness clause. It adds no unsourced
constructor from primitiveness to the complete PF package.

Canonical theorem:
- `UEOT.V3.EvolutionPerronGrowth.p_evo_03`.

Supporting module:
- `UEOT.V3.EvolutionPerronGrowth`.

Promotion evidence:
- two independent final source/proof audits: GREEN;
- feature commit `340a56d4ca19236bba141b79b8471ed95a512995`;
- feature tree `7ee94553049f5d6de825a9883695719e2399a4a7`;
- feature root CI `35576131678`: success;
- focused/root/full feature checks: success (`8990` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- audited `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pevo03-main-integration@11e17eaab6385017c1515afaaff1a460a91e79c6`
  from `main@85b3e410ab9a1ef71ca512c0e8f8f6a2f9aa6cb2`;
- feature/integration tree hash identical:
  `7ee94553049f5d6de825a9883695719e2399a4a7`;
- integration focused/root/full local checks: success (`8990` jobs);
- integration root CI `35576926135`: success;
- proof PR #127 exact-head root CI `35577642954`: success;
- proof main `4d581a675f4057069dbe19db7d0e182bfdf91ff8`;
- proof resulting-main root CI `35578270234`: success.

## Previous FULL-GREEN checkpoint — 97/106

P-CORE-01 and all earlier counted P-IDs remain closed. The 97/106 ledger landed
at `main@85b3e410ab9a1ef71ca512c0e8f8f6a2f9aa6cb2` with resulting-main CI
`35573090853` success.

P-EVO-03 is proof-complete but remains staged, not counted FULL-GREEN, until
this separate ledger lifecycle completes.

## Branchless frontier after the 98 ledger closes

No theorem branch is opened by this ledger lifecycle. After a successful 98/106
promotion, the remaining P-IDs are exactly P-PER-02, P-QSD-01, P-QSD-04,
P-CTL-02, P-CTL-03, P-KL-04, P-KL-05, and P-ALI-01.

The next theorem lane must be selected dynamically from the exact 98/106
FULL-GREEN main after this ledger finishes, rather than being opened early from
this staged branch.

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
