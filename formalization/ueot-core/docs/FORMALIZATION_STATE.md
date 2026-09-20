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
| integrated/proof-complete, staged by this checkpoint | **95** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **11** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **94/106**.
P-GOA-03 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@6f9173ee290e01838e4746faba6429928399b98c`; proof resulting-main root CI
`35536908530` succeeded.

This ledger branch stages **95/106**. Do not call 95/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-GOA-03

Frozen Core 3 §21.4 requires finite recurrent-decomposition stability when the
transient set and recurrent-class partition are unchanged. With
`N=(I-Q)⁻¹`, `H=NR`, `‖Qhat-Q‖∞≤epsQ`, `‖Rhat-R‖∞≤epsR` and
`‖N‖∞ epsQ<1`, the source requires the exact rational `B_H` bound and the
same-initial-state Cesaro-limit TV estimate with coefficient `1/2` and
perturbed recurrent-class weights.

The formalization ties `Q` and `R` to two actual finite stochastic kernels
on one common `T ⊕ R` state space and one literal shared recurrent partition.
It derives class-law positivity and stationary proportionality from recurrent
class communication, proves periodic-safe full Cesaro convergence from
P-GOA-01 plus harmonic absorption potentials and class-law uniqueness, handles
the empty-transient-set case, and preserves the exact `B_H`, `1/2`, and
perturbed-weight orientation. It adds no arbitrary-mixture surrogate,
aperiodicity assumption, changed recurrent support, or primitive
stationary-class conclusion.

Canonical theorem:
- `UEOT.V3.FiniteRecurrentDecompositionStability.p_goa_03`.

Supporting module:
- `UEOT.V3.FiniteRecurrentDecompositionStability`.

Promotion evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- feature commits `8cd02864498ff369b59e9e4b1913082558bd2820` and
  `c1ff6baecdaa7c56a8ade42fbffaeeddf42ec909`;
- final feature root CI `35535448015`: success;
- full local `lake build UEOT`: success (`8987` jobs);
- two independent final source/proof audits: PASS;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` for
  `FiniteRecurrentDecompositionStability.p_goa_03`: only standard `propext`,
  `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pgoa03-main-integration@4d518420cd93e4130a1cd59ceccf888dc9638b6c`
  from `main@cf8aaa8b91b3096cd05d60ad148ada14cc773924`;
- feature/integration tree hash
  `3c956eadc54fd67a0784af9d46d21ecb88acd764` identical;
- clean integration root CI `35536081037`: success;
- proof PR #121 root CI `35536497250`: success;
- proof main `6f9173ee290e01838e4746faba6429928399b98c`;
- proof resulting-main root CI `35536908530`: success.

## Previous FULL-GREEN checkpoint — 94/106

P-DDH-05 and all earlier counted P-IDs remain closed. The 94/106 ledger landed
at `main@cf8aaa8b91b3096cd05d60ad148ada14cc773924` with resulting-main CI
`35530223703` success.

P-QUO-03 and P-TEL-01 are already counted and must not be reopened or
re-counted merely because older compilation reports predate their promotion.

## Branchless frontier after the 95 ledger closes

No theorem branch is opened by this ledger lifecycle. P-GOA-03 has discharged
the recurrent-structure blocker that previously prevented a source-faithful
P-CORE-01 attempt, so P-CORE-01 returns to the read-only frontier for an exact
95/106-main source/dependency re-audit. P-PER-02 / P-QSD-01 remain read-only
alternatives requiring new continuous-time semigroup / occupation-measure
infrastructure.

The next theorem lane must be selected dynamically from the exact 95/106
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
