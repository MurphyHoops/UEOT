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
| integrated/proof-complete, staged by this checkpoint | **87** |
| source audit prepared for next lane | **1** |
| active theorem proof branch | **0** |
| blocked | **0** |
| pending/not yet counted after this promotion | **19** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **86/106**.
P-QUO-05 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@7d0f7dae8b6db34994707a3453a4c827a8dfd89e`; proof resulting-main root CI
`35332494188` succeeded.

This ledger branch stages **87/106**. Do not call 87/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-QUO-05

Frozen Core 3 §20.5 uses local state-action model errors

- `delta(x,a) = epsilon_r(x,a) + beta * epsilon_p(x,a) * span(Vbar*)`;
- `J(pi*;mu)-J(hatpi;mu) <=
  (E_{d_mu^{pi*}} delta + E_{d_mu^{hatpi}} delta)/(1-beta)`.

The formalization establishes at source strength on the finite discounted-control
branch:

1. pointwise local reward and pushed-forward transition-TV errors, with no
   uniform P-QUO-02 radius added;
2. `w = Vbar* o f` and the exact local source error `delta(x,a)`;
3. actionwise residual upper bounds for every micro action;
4. matching residual lower bounds for any designated macro-optimal selector,
   including tied macro optima;
5. arbitrary designated true-optimal stationary micro policies, including ties;
6. the exact P-QUO-04 discounted state-action occupancy identity for both
   `pi*` and the lifted `hatpi`;
7. the frozen two-occupancy regret inequality with exactly one `1/(1-beta)`.

Canonical theorem:
- `UEOT.V3.FiniteDiscountedControl.LocalApproxControlQuotient.p_quo_05`.

Supporting modules:
- `UEOT.V3.FiniteDiscountedPolicyResolvent`;
- `UEOT.V3.FiniteDiscountedOccupancy`;
- `UEOT.V3.FiniteDiscountedOccupancyRegret`.

Promotion evidence:
- canonical frozen source hash independently verified against the project File Library original;
- feature commit `66472785c54fc5863554455a6a717009679f11f3`;
- feature root target `lake build UEOT`: success (`8979` jobs);
- independent source-semantic re-audit: pass;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` for `LocalApproxControlQuotient.p_quo_05`: only standard `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pquo05-main-integration@3b647e3f078d7ef94377fe2139ecd9dfd910daeb`;
- clean integration root CI `35219313969`: success;
- proof PR #105 root CI `35332002471`: success;
- proof main `7d0f7dae8b6db34994707a3453a4c827a8dfd89e`;
- proof resulting-main root CI `35332494188`: success.

## Previous FULL-GREEN checkpoint — 86/106

P-QUO-04 and all earlier counted P-IDs remain closed. The 86/106 ledger landed
at `main@208d9758a90f6c28623b3adac82eb26ea030e5dd` with resulting-main CI
`35207737414` success.

P-QUO-03 and P-TEL-01 are already counted and must not be reopened or
re-counted merely because older compilation reports predate their promotion.

## Next source-to-main lane after the 87 ledger closes

No theorem branch is opened by this ledger lifecycle. The independent frontier
audit recommends P-GOA-01 next, followed by P-GOA-02. P-GOA-01 must preserve the
exact finite-kernel Cesaro subsequence/invariance statement of frozen §21.2; it
must not be replaced by a claim about attractivity or require full Cesaro
convergence. Existing `QSDPerron.rowApply` / `rowApply_mul`, finite probability
rows, Mathlib standard-simplex compactness and `IsCompact.tendsto_subseq` provide
the reusable base. P-CORE-01 remains blocked until the required GOA stability
layer is established.

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
