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
| integrated/proof-complete, staged by this checkpoint | **85** |
| source audit prepared for next lane | **1** |
| active theorem proof branch | **0** |
| blocked | **0** |
| pending/not yet counted after this promotion | **21** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **84/106**.
P-QUO-02 has completed source audit, feature, clean-integration, proof PR,
proof-main and proof resulting-main gates. Its proof is on
`main@28b872857b2cd8b4a546433f858015443f861ce4`; proof resulting-main root CI
`35162246623` succeeded.

This ledger branch stages **85/106**. Do not call 85/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-QUO-02

Frozen Core 3 §20.2 span-sensitive approximate control quotient is formalized at
source strength on the finite discounted-control foundation.

The formalization establishes:

1. the same fibre/action correspondence as the exact quotient;
2. reward error `epsilonReward` for every micro state-action pair;
3. **genuine event-supremum total variation** between each all-action pushed-forward
   micro transition row and the corresponding macro row;
4. derivation of the continuation expectation error from P-MET-02, rather than
   assuming an expectation-gap surrogate;
5. `w = Vbar* ∘ f`;
6. `delta = epsilonReward + beta * epsilonTransition * span(Vbar*)`;
7. `D = delta / (1-beta)`;
8. the optimal Bellman residual bound and P-CTL-01 certificate
   `||V* - w||_infinity <= D`;
9. fixed lifted-policy residual control giving its own distance at most `D` from
   `w`;
10. causal optimal domination plus the two `D` bounds giving pointwise
    `0 <= V* - V^hatpi <= 2D`;
11. arbitrary tied macro stationary argmax selectors remain admissible; no
    unique-argmax assumption is introduced.

Canonical theorem:
- `UEOT.V3.FiniteDiscountedControl.ApproxControlQuotient.p_quo_02`.

Supporting modules:
- `UEOT.V3.FiniteDiscountedSelectorValue`;
- `UEOT.V3.FiniteDiscountedApproxQuotient`;
- `UEOT.V3.FiniteDiscountedApproxQuotientBounds`.

Promotion evidence:
- feature branch `formal/pquo02-span-approx-quotient-v1`;
- selector-value checkpoint `5b7d0e919c4800c27544b427ba41b0f61e123f67`, root CI `35125066423`: success;
- true-TV/span checkpoint `c8c21e39037f808fbc4559709f0aca92c8dc4cc8`, root CI `35125945423`: success;
- source-facing proof head `f2de244a32a29c336cb07a943489d00c5d11a3a8`, root CI `35128138029`: success;
- source-semantic audit: pass;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- clean integration `formal/pquo02-main-integration-v1@f2de244a32a29c336cb07a943489d00c5d11a3a8`;
- clean integration root CI `35128929614`: success;
- proof PR #98 root CI `35129778828`: success;
- proof main `28b872857b2cd8b4a546433f858015443f861ce4`;
- proof resulting-main root CI `35162246623`: success.

## Previous FULL-GREEN checkpoint — 84/106

P-QUO-01 and all earlier counted P-IDs remain closed. The 84/106 ledger landed
at `main@b9fc5751f4a04de210740f5df8a8699a0faada2d` with resulting-main CI
`35124093049` success.

P-QUO-03 and P-TEL-01 are already counted and must not be reopened or
re-counted merely because older compilation reports predate their promotion.

## Next source-to-main lane after the 85 ledger closes — P-QUO-04

Frozen §20.4 has been re-read during the P-QUO-02 CI window. No P-QUO-04 proof
branch is opened while this ledger lifecycle is active.

Required source contract for fixed policy `pi` and bounded reference `w`:

- `b_pi = r^pi + beta P^pi w - w`;
- `d_mu^pi = (1-beta) * sum_{t>=0} beta^t mu (P^pi)^t`;
- exact resolvent identity
  `V^pi - w = (I - beta P^pi)^(-1) b_pi`;
- exact discounted-occupancy identity
  `mu(V^pi-w) = E_{d_mu^pi}[b_pi] / (1-beta)`.

Source-first implementation direction:

1. introduce a finite stationary randomized policy interface and induced
   `r^pi`, `P^pi`, keeping deterministic selectors as a special case;
2. prove the policy kernel is stochastic and its expectation is sup-norm
   nonexpansive;
3. define the resolvent through the convergent Neumann/fixed-point construction
   and prove it is the inverse of `I-beta P^pi` at the source object level;
4. define the discounted state occupancy from an initial finite probability
   distribution and prove it is a probability row;
5. derive the occupancy expectation identity exactly, not as a sup-norm bound;
6. expose state-action discounted occupancy so P-QUO-05 can reuse the same
   infrastructure rather than creating a second policy semantics.

P-QUO-05 has also been source-audited, but it depends on P-QUO-04 and must not
open a conflicting proof lane. It uses local
`delta(x,a)=epsilon_r(x,a)+beta*epsilon_p(x,a)*span(Vbar*)` and the two policy
occupancies to bound quotient-policy regret.

## Grounded non-quick fronts

P-CTL-02/03, P-PER-02, P-ALI-01, P-DDH-02/03/04/05, P-KL-04/05,
P-EVO-03/04 and P-QSD-01/04 remain source-strength lanes. P-EVO-03 requires the
full K-PF-01 primitive Perron-Frobenius asymptotic package; assumed convergence
is forbidden.

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
