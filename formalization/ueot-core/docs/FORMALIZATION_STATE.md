# UEOT Core Lean — Live Formalization State

> Recovery entry point. Integrated source-count truth is `V3_COVERAGE_STATUS.md`.
> GitHub Issue #56 carries the live cross-chat construction log and overrides
> stale fallback snapshots.

Last synchronized: **2026-09-17**

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
| integrated/proof-complete, staged by this checkpoint | **86** |
| source audit prepared for next lane | **1** |
| active theorem proof branch | **0** |
| blocked | **0** |
| pending/not yet counted after this promotion | **20** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **85/106**.
P-QUO-04 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@c5cc58e49ef820fb3e9ed7d3555722578f4c4b9c`; proof resulting-main root CI
`35205157977` succeeded.

This ledger branch stages **86/106**. Do not call 86/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-QUO-04

Frozen Core 3 §20.4 requires, for fixed policy `pi` and bounded reference `w`,

- `b_pi = r^pi + beta P^pi w - w`;
- `d_mu^pi = (1-beta) * sum_{t>=0} beta^t mu(P^pi)^t`;
- `V^pi - w = (I-beta P^pi)^(-1)b_pi`;
- `mu(V^pi-w) = E_{d_mu^pi}[b_pi]/(1-beta)`.

The formalization establishes at source strength on the finite discounted-control
branch:

1. finite stationary randomized policies, with deterministic selectors embedded;
2. exact induced reward `r^pi` and stochastic transition kernel `P^pi`;
3. fixed-policy Bellman contraction and unique `V^pi`;
4. equality of that `V^pi` with the repository's existing causal infinite-horizon policy value;
5. the linear residual operator `I-beta P^pi` and a genuine two-sided inverse;
6. explicit summability of the Neumann series `sum_n beta^n (P^pi)^n b` and equality with the resolvent;
7. the exact source residual `b_pi` and first resolvent identity;
8. the exact discounted state occupancy geometric series, nonnegativity and total mass one;
9. occupancy row fixed point `d=(1-beta)mu+beta dP^pi` and its expectation form;
10. the exact source occupancy expectation identity;
11. state-action occupancy `d(x)pi(a|x)` with nonnegativity, state marginal and total mass one.

Canonical theorem:
- `UEOT.V3.FiniteDiscountedControl.Model.p_quo_04`.

Supporting modules:
- `UEOT.V3.FiniteDiscountedPolicyResolvent`;
- `UEOT.V3.FiniteDiscountedOccupancy`.

Promotion evidence:
- canonical frozen source hash independently verified against the project File Library original;
- feature commit `17a7d44d9d43b592f1aa35ecaeb6b8392707a9d3`;
- feature root target `lake build UEOT`: success (`8978` jobs);
- source-semantic audit: pass;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` for `Model.p_quo_04`: only standard `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pquo04-main-integration@8e3675e99f0959734d4a20257e90f1ad86a0ad63`;
- clean integration root CI `35203214739`: success;
- proof PR #103 root CI `35203814134`: success;
- proof main `c5cc58e49ef820fb3e9ed7d3555722578f4c4b9c`;
- proof resulting-main root CI `35205157977`: success.

## Previous FULL-GREEN checkpoint — 85/106

P-QUO-02 and all earlier counted P-IDs remain closed. The 85/106 ledger landed
at `main@aaea53a70902e138d123ef700a99c372214708d9` with resulting-main CI
`35165216681` success.

P-QUO-03 and P-TEL-01 are already counted and must not be reopened or
re-counted merely because older compilation reports predate their promotion.

## Next source-to-main lane after the 86 ledger closes

No theorem branch is opened by this ledger lifecycle. P-QUO-05 is source-audited
and depends on the state-action discounted occupancy established by P-QUO-04,
but remains a separate later proof lifecycle. Other source-strength lanes include
P-CTL-02/03, P-PER-02, P-ALI-01, P-DDH-02/03/04/05, P-KL-04/05,
P-EVO-03/04 and P-QSD-01/04. P-EVO-03 requires the full K-PF-01 primitive
Perron-Frobenius asymptotic package; assumed convergence is forbidden.

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
