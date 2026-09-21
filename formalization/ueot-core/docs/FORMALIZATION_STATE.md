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
| integrated/proof-complete, staged by this checkpoint | **99** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **7** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **98/106**.
P-PER-02 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@1aa9d4c0dd745a2909903c8d1083676b0ec11751`; proof resulting-main root CI
`35602757494` succeeded.

This ledger branch stages **99/106**. Do not call 99/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-PER-02

Frozen Core 3 §8.4 is the Krylov-Bogoliubov occupation-measure persistence
statement for a continuous-time Feller semigroup on a Polish space. The literal
marginal average `bar μ_T = T⁻¹ ∫₀ᵀ μ₀P_t dt` is tight for `T >= 1`; every
diverging time sequence therefore has a weakly convergent subsequence, every
weak limit is invariant, and closed support of all time marginals is retained
by every such limit. No sample-path empirical-frequency convergence is claimed.

The implementation ties all marginals to the same initial law and semigroup,
uses the `C_b` Feller action, proves the exact `2s||f||∞/T` shift bound, takes
weak limits via tightness/Prokhorov, proves invariance for arbitrary diverging
weak limits, and retains closed support by the closed-set Portmanteau bound.
The occupation interfaces are extensional faces of the literal time-average
measure rather than invariance or limit assumptions.

Canonical theorem:
- `UEOT.V3.PersistenceOccupation.FellerOccupationSystem.p_per_02`.

Supporting module:
- `UEOT.V3.PersistenceOccupation`.

Promotion evidence:
- final source/proof audits: GREEN;
- feature commit `2e12c0dbad89f8cddf8f2d195353580a5559c190`;
- feature tree `fd32905323e09e14cba3b3950322a0e2dc5b47f7`;
- feature root CI `35600355442`: success;
- focused/root/full feature checks: success (`8991` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`);
- audited `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pper02-main-integration@959586d1161f27a7a5bbec88b0d1672cac39bc90`
  from `main@4d2016267c246400ce0a6e025f9330eae820eef8`;
- feature/integration tree hash identical:
  `fd32905323e09e14cba3b3950322a0e2dc5b47f7`;
- integration focused/root/full local checks: success (`8991` jobs);
- integration root CI `35601197925`: success;
- proof PR #129 exact-head root CI `35601980474`: success;
- proof main `1aa9d4c0dd745a2909903c8d1083676b0ec11751`;
- proof resulting-main root CI `35602757494`: success.

## Previous FULL-GREEN checkpoint — 98/106

P-EVO-03 and all earlier counted P-IDs remain closed. The 98/106 ledger landed
at `main@4d2016267c246400ce0a6e025f9330eae820eef8` with resulting-main CI
`35582525823` success.

P-PER-02 is proof-complete but remains staged, not counted FULL-GREEN, until
this separate ledger lifecycle completes.

## Branchless frontier after the 99 ledger closes

No theorem branch is opened by this ledger lifecycle. After a successful 99/106
promotion, the remaining P-IDs are exactly P-QSD-01, P-QSD-04, P-CTL-02,
P-CTL-03, P-KL-04, P-KL-05, and P-ALI-01.

The next theorem lane must be selected dynamically from the exact 99/106
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
