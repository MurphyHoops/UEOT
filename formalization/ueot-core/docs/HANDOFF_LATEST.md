# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **83/106**;
- this ledger branch stages: **84/106**;
- pending after successful ledger lifecycle: **22**;
- proof main: `25af2f3d8d537600453b5be3bcb30de6af6c0e3e`;
- P-QUO-01 proof PR: **#96**;
- proof PR root CI: `35120644387` — success;
- proof resulting-main root CI: `35121419393` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-QUO-01 is therefore **PROOF-COMPLETE** but is not called COUNTED / 84 FULL-GREEN
until this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and
the resulting-main CI succeeds.

## P-QUO-01 — proof-complete lifecycle

Frozen §20.1 source obligations retained:

1. surjective micro-to-macro quotient `f`;
2. identical admissible action type on a common fibre;
3. exact reward closure;
4. exact pushed-forward transition closure for every admissible action;
5. Bellman intertwining on pulled-back macro values;
6. exact fixed-point pullback `V* = Vbar* ∘ f`;
7. actionwise optimal-Q equality;
8. lifting of any macro stationary argmax selector, including ties, to a micro
   stationary policy optimal against the full causal history-dependent
   randomized policy class.

Canonical theorem:
- `UEOT.V3.FiniteDiscountedControl.ExactControlQuotient.p_quo_01`.

Proof evidence:
- feature `formal/pquo01-exact-control-quotient@8ffa1e4cbbe73eeb3867c152630a1029c998e231`;
- selector checkpoint root CI `35113940062` success;
- clean integration `formal/pquo01-main-integration-v1@0427733fe363ba3b0a697879df42d2d141786a72`;
- clean integration root CI `35118874289` success;
- source-semantic audit pass;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- proof PR #96 root CI `35120644387` success;
- proof main `25af2f3d8d537600453b5be3bcb30de6af6c0e3e`;
- proof resulting-main root CI `35121419393` success.

## Previous FULL-GREEN checkpoint — 83/106

The 83/106 ledger landed at
`main@995c99683e0ae225f8df46108fd1442038c3963a` and its resulting-main root CI
`35109381744` succeeded. The later audited branch-governance main
`2d1373a0eb417496cdd83bfc948e1806f4427587` preserved exactly the same source
coverage and passed root CI `35112629545`.

P-CTL-01 and all older counted P-IDs stay closed absent source mismatch or main
regression. P-TEL-01 is already counted and must not be double-counted.

## Next theorem lane after the 84 ledger closes — P-QUO-02

A fresh source audit is already complete; no proof branch has been opened during
this promotion.

Frozen §20.2 requires, with reward error `epsilon_r`, all-action pushed-forward
transition TV error `epsilon_p`, and

`w = Vbar* ∘ f`,
`delta = epsilon_r + beta * epsilon_p * span(Vbar*)`,
`D = delta / (1-beta)`,

both

`||V* - w||_infinity <= D`

and the lifted macro-optimal-policy guarantee

`0 <= V* - V^hatpi <= 2D`.

The proof route is source-locked: P-MET-02 supplies the span-times-TV
expectation error; P-CTL-01 supplies optimal Bellman residual control; the
P-QUO-01 selector layer supplies stationary policy-evaluation contraction. The
TV premise itself must be represented; it may not be replaced by an assumed
expectation error. All-action closure may not be weakened to one-policy
Markovity, and macro argmax ties must remain admissible.

## Larger pending foundations

P-CTL-02/03; P-PER-02; P-ALI-01; P-DDH-02/03/04/05; P-KL-04/05;
P-EVO-03/04; P-QSD-01/04 and the remaining quotient/GOA fronts remain distinct
source propositions unless a fresh audit finds an exact bridge. P-EVO-03 still
requires the full primitive nonnegative-matrix Perron-Frobenius asymptotic
package; assumed convergence is forbidden.

## Guards

- do not reopen counted green P-IDs absent source mismatch/CI regression;
- feature/integration/proof-main green never increments source coverage;
- no `sorry`, Lean `admit`, `native_decide`, or unsourced `axiom`;
- preserve frozen source strength; no finite/toy/assumed-conclusion replacement
  of a stronger source theorem;
- source-object identity must be explicit; generalization alone does not count
  without a bridge back to the frozen object;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-KL-04/05 stay at their frozen CTMC/Girsanov level;
- P-EVO-03 requires the full K-PF-01 asymptotic package.

## Exact continuation order

1. finish this **84/106 ledger lifecycle**: branch root CI -> ledger PR root CI -> merge -> resulting-main root CI;
2. only after all four gates succeed, record **84/106 FULL-GREEN** in Issue #56;
3. retire completed P-QUO-01 ephemeral branches when the available branch-hygiene mechanism permits;
4. open exactly one P-QUO-02 proof lane from the latest 84/106 full-green main;
5. implement source TV interface -> span expectation bridge -> actionwise Q error -> optimal Bellman residual -> D value bound -> lifted-selector policy residual -> 2D regret;
6. repeat the full proof and ledger promotion lifecycle before any further count increment.

## Recovery order

1. `NEW_CHAT_BOOTSTRAP.md`;
2. `docs/REPOSITORY_BRANCH_GOVERNANCE.md`;
3. `UEOT_CORE3_LEAN_OPERATIONS.md`;
4. Issue #56 when available;
5. `V3_COVERAGE_STATUS.md`;
6. `FORMALIZATION_STATE.md`;
7. this fallback handoff;
8. live main/branches/PR/CI reconciliation.
