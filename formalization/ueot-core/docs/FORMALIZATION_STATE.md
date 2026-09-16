# UEOT Core Lean — Live Formalization State

> Recovery entry point. Integrated source-count truth is
> `V3_COVERAGE_STATUS.md`. GitHub Issue #56 carries the live cross-chat
> construction log and overrides stale fallback snapshots.

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
| integrated/proof-complete, staged by this checkpoint | **84** |
| source audit prepared for next lane | **1** |
| active proof branch | **0** |
| blocked | **0** |
| pending/not yet counted after this promotion | **22** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **83/106**.
P-QUO-01 has completed its source audit, feature, clean-integration, proof PR,
proof-main and proof resulting-main gates. Its proof is on
`main@25af2f3d8d537600453b5be3bcb30de6af6c0e3e`; proof resulting-main root CI
`35121419393` succeeded.

This ledger branch stages **84/106**. Do not call 84/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-QUO-01

Frozen Core 3 §20.1 exact control quotient is represented at source strength on
the finite discounted-control foundation already counted as P-CTL-01.

The formalization establishes:

1. a surjective micro-to-macro map `f`;
2. the same admissible action type for states in a common fibre;
3. exact reward closure for every state-action pair;
4. exact pushed-forward transition closure for **every** admissible action;
5. exact expectation and action-value intertwining on pulled-back macro values;
6. Bellman intertwining `T(vbar ∘ f) = (Tbar vbar) ∘ f`;
7. exact optimal-value pullback `V* = Vbar* ∘ f` from unique fixed points;
8. actionwise optimal-Q equality;
9. lifting of any macro stationary argmax selector, including tied argmax cases,
   to a micro stationary policy whose infinite discounted value is optimal
   against the full causal history-dependent randomized policy class.

Canonical theorem:
- `UEOT.V3.FiniteDiscountedControl.ExactControlQuotient.p_quo_01`.

Supporting modules:
- `UEOT.V3.FiniteDiscountedSelector`;
- `UEOT.V3.FiniteDiscountedExactQuotient`.

Promotion evidence:
- feature `formal/pquo01-exact-control-quotient@8ffa1e4cbbe73eeb3867c152630a1029c998e231`;
- selector checkpoint root CI `35113940062`: success;
- clean integration `formal/pquo01-main-integration-v1@0427733fe363ba3b0a697879df42d2d141786a72`;
- clean integration root CI `35118874289`: success;
- source-semantic re-audit: pass;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- proof PR #96 root CI `35120644387`: success;
- proof main `25af2f3d8d537600453b5be3bcb30de6af6c0e3e`;
- proof resulting-main root CI `35121419393`: success.

## Previous FULL-GREEN checkpoint — 83/106

P-CTL-01 and all earlier counted P-IDs remain closed. The 83/106 ledger landed
at `main@995c99683e0ae225f8df46108fd1442038c3963a` with resulting-main CI
`35109381744` success. The later branch-governance main
`2d1373a0eb417496cdd83bfc948e1806f4427587` preserved 83/106 and passed root CI
`35112629545`.

P-TEL-01 is already counted and must not be reopened merely because older
compilation reports predate its promotion.

## Next source-to-main lane after the 84 ledger closes — P-QUO-02

Frozen §20.2 was independently re-read during the P-QUO-01 CI window. No second
proof branch has been opened.

Required source contract:

- reward approximation error at most `epsilon_r`;
- pushed-forward transition TV error at most `epsilon_p` for every admissible
  action;
- same action correspondence and discount as the quotient control problem;
- `w = Vbar* ∘ f`;
- `delta = epsilon_r + beta * epsilon_p * span(Vbar*)`;
- `D = delta / (1-beta)`;
- `||V* - w||_infinity <= D`;
- lifted macro-optimal policy regret `0 <= V* - V^hatpi <= 2D`.

Reusable counted/main infrastructure:

- P-MET-02: exact span-times-TV expectation bound;
- P-CTL-01: `Model.valueError_le_residual` and causal-policy domination;
- P-QUO-01 support: generic stationary-selector policy-evaluation contraction.

Implementation route:

1. represent the source TV premise, not an already-derived expectation-gap
   surrogate;
2. derive all-action continuation expectation error via P-MET-02;
3. derive uniform actionwise Q error and optimal Bellman residual for `w`;
4. apply the existing residual certificate to obtain the first `D` bound;
5. evaluate a lifted macro optimal selector under its fixed policy Bellman map;
6. derive the same `D` distance from its value to `w`;
7. combine with causal-policy domination to obtain the pointwise `0 .. 2D`
   policy regret bound.

No unique-argmax assumption and no one-policy closure weakening are allowed.

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
