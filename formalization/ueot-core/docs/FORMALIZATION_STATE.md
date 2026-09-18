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
| integrated/proof-complete, staged by this checkpoint | **89** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **17** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **88/106**.
P-GOA-02 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@c2e2f56736aa29965a4d964c28c13688d5b237c2`; proof resulting-main root CI
`35347998899` succeeded.

This ledger branch stages **89/106**. Do not call 89/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-GOA-02

Frozen Core 3 §21.3 uses canonical event-supremum total variation, equal on a
finite space to the standard `1/2 * L1` normalization.  For a finite stochastic
kernel `P`, it defines the literal Dobrushin coefficient

`alpha(P) = max_{x,x'} D_TV(P_x,P_x')`

and requires:

1. exact TV contraction
   `D_TV(mu P,nu P) <= alpha(P) D_TV(mu,nu)`;
2. uniqueness of an invariant probability whenever `alpha(P) < 1`;
3. for stationary `mu P = mu`, `muhat Phat = muhat`, and uniform same-state
   row error at most `epsilon`, the perturbation estimate
   `D_TV(mu,muhat) <= epsilon/(1-alpha(P))`.

The formalization defines the literal finite maximum over row pairs, preserves
the source TV normalization with no hidden factor two, obtains invariant-law
existence from P-GOA-01, proves uniqueness by contraction, and proves the
stationary perturbation bound with the baseline `alpha(P)`.  It does not assume
`alpha(Phat)<1`, irreducibility, aperiodicity, a Doeblin condition, or a
symmetric denominator.

Canonical theorem:
- `UEOT.V3.FiniteDobrushin.p_goa_02`.

Supporting module:
- `UEOT.V3.FiniteDobrushin`.

Promotion evidence:
- canonical frozen source hash reverified before implementation;
- feature commit `e04946d6ef9a9408a5e36aa67fa7a0c0f7cfdf96`;
- feature root CI `35345265060`: success;
- full local `lake build UEOT`: success (`8981` jobs);
- independent source-semantic re-audit: PASS against frozen §21.3;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` for `FiniteDobrushin.p_goa_02`: only standard `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pgoa02-main-integration@c3a0355e380a6d4e25179515599c2594db65d921` from `main@465796d119483f60eb2c1b296d78870a79f92522`;
- feature/integration tree hash `6aeeaab1e2abc61cee27ee8b7d470e0ba0226709` identical;
- clean integration root CI `35346669326`: success;
- proof PR #109 root CI `35347283556`: success;
- proof main `c2e2f56736aa29965a4d964c28c13688d5b237c2`;
- proof resulting-main root CI `35347998899`: success.

## Previous FULL-GREEN checkpoint — 88/106

P-GOA-01 and all earlier counted P-IDs remain closed. The 88/106 ledger landed
at `main@465796d119483f60eb2c1b296d78870a79f92522` with resulting-main CI
`35343788114` success.

P-QUO-03 and P-TEL-01 are already counted and must not be reopened or
re-counted merely because older compilation reports predate their promotion.

## Branchless frontier after the 89 ledger closes

No theorem branch is opened by this ledger lifecycle. Current read-only audits
rank the leading uncounted fronts by implementation risk as follows:

- P-DDH-04: Class C, S/M; common two-dimensional differentiable bottleneck
  implies stacked environment-response Jacobian rank at most 2;
- P-DDH-03: Class C, M; finite exponential-family KL minimization;
- P-GOA-04: Class C, L; symmetric killed-kernel spectral/Q-process stability;
- P-GOA-03: Class D, L-XL; finite transient/recurrent decomposition, absorption
  weights, and periodic-safe full Cesaro-mixture machinery are still missing.

P-CORE-01 remains hard-blocked by the recurrent-structure branch of P-GOA-03;
P-GOA-04 is not a hard dependency for that closure.  The next theorem lane must
be chosen dynamically from the exact 89/106 FULL-GREEN main after this ledger
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
