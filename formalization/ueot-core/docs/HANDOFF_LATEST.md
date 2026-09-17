# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN before this ledger: **84/106**;
- this ledger branch stages: **85/106**;
- pending after successful ledger lifecycle: **21**;
- proof main: `28b872857b2cd8b4a546433f858015443f861ce4`;
- P-QUO-02 proof PR: **#98**;
- proof PR root CI: `35129778828` — success;
- proof resulting-main root CI: `35162246623` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active theorem proof lanes while this ledger runs: **0**.

P-QUO-02 is **PROOF-COMPLETE** but is not called COUNTED / 85 FULL-GREEN until
this docs-only ledger branch passes branch CI, PR CI, lands on `main`, and the
resulting-main CI succeeds.

## P-QUO-02 — proof-complete lifecycle

Frozen §20.2 source obligations retained:

1. same action correspondence on quotient fibres;
2. reward error `epsilon_r` for every admissible state-action pair;
3. all-action pushed-forward transition **total variation** error `epsilon_p`;
4. P-MET-02 derives, rather than assumes, the span-sensitive continuation error;
5. `w = Vbar* ∘ f`;
6. `delta = epsilon_r + beta * epsilon_p * span(Vbar*)`;
7. `D = delta / (1-beta)`;
8. `||V* - w||_infinity <= D` via the P-CTL-01 Bellman residual certificate;
9. the lifted macro-optimal stationary selector has policy value within `D` of
   `w`;
10. causal optimal domination plus the two `D` bounds yields pointwise
    `0 <= V* - V^hatpi <= 2D`;
11. tied macro argmax selectors remain admissible.

Canonical theorem:
- `UEOT.V3.FiniteDiscountedControl.ApproxControlQuotient.p_quo_02`.

Proof evidence:
- selector-value checkpoint `5b7d0e919c4800c27544b427ba41b0f61e123f67`, root CI `35125066423` success;
- true-TV/span checkpoint `c8c21e39037f808fbc4559709f0aca92c8dc4cc8`, root CI `35125945423` success;
- source-facing feature head `f2de244a32a29c336cb07a943489d00c5d11a3a8`, root CI `35128138029` success;
- clean integration `formal/pquo02-main-integration-v1@f2de244a32a29c336cb07a943489d00c5d11a3a8`;
- clean integration root CI `35128929614` success;
- source-semantic audit pass;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- proof PR #98 root CI `35129778828` success;
- proof main `28b872857b2cd8b4a546433f858015443f861ce4`;
- proof resulting-main root CI `35162246623` success.

## Previous FULL-GREEN checkpoint — 84/106

The P-QUO-01 ledger landed at
`main@b9fc5751f4a04de210740f5df8a8699a0faada2d` and its resulting-main root CI
`35124093049` succeeded. P-QUO-01, P-QUO-03, P-CTL-01, P-TEL-01 and all older
counted P-IDs stay closed absent source mismatch or main regression.

## Next theorem lane after the 85 ledger closes — P-QUO-04

Frozen §20.4 requires a fixed-policy exact identity, not a worst-case norm
substitute. For stationary policy `pi`, reference function `w`,

`b_pi = r^pi + beta P^pi w - w`,
`d_mu^pi = (1-beta) * sum_{t>=0} beta^t mu(P^pi)^t`,

and source theorem

`V^pi - w = (I-beta P^pi)^(-1)b_pi`,

`mu(V^pi-w) = E_{d_mu^pi}[b_pi]/(1-beta)`.

The intended implementation is deliberately broader than the deterministic
selector special case: define finite stationary randomized policies and their
induced reward/kernel, prove stochasticity and policy-evaluation contraction,
construct the Neumann/resolvent inverse, then construct discounted state and
state-action occupancy. This gives P-QUO-05 the exact occupancy semantics it
needs.

Frozen §20.5 is already source-audited and depends on P-QUO-04. It introduces
local `delta(x,a)=epsilon_r(x,a)+beta*epsilon_p(x,a)*span(Vbar*)` and requires

`J(pi*;mu)-J(hatpi;mu) <=
 (E_{d_mu^{pi*}} delta + E_{d_mu^{hatpi}} delta)/(1-beta)`.

Do not open P-QUO-05 as a separate proof lane before P-QUO-04 closes.

## Larger pending foundations

P-CTL-02/03; P-PER-02; P-ALI-01; P-DDH-02/03/04/05; P-KL-04/05;
P-EVO-03/04; P-QSD-01/04 and the remaining GOA fronts remain distinct source
propositions unless a fresh audit finds an exact bridge. P-EVO-03 still
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

1. finish this **85/106 ledger lifecycle**: branch root CI -> ledger PR root CI -> merge -> resulting-main root CI;
2. only after all four gates succeed, record **85/106 FULL-GREEN** in Issue #56;
3. retire completed P-QUO-02 ephemeral branches when the available branch-hygiene mechanism permits;
4. open exactly one P-QUO-04 proof lane from the latest 85/106 full-green main;
5. implement stationary-policy induced kernel/reward -> policy value -> exact
   resolvent/Neumann identity -> discounted state occupancy -> source-facing
   P-QUO-04;
6. only then use that exact occupancy layer for P-QUO-05;
7. repeat the full proof and ledger promotion lifecycle before any further count increment.

## Recovery order

1. `NEW_CHAT_BOOTSTRAP.md`;
2. `docs/REPOSITORY_BRANCH_GOVERNANCE.md`;
3. `UEOT_CORE3_LEAN_OPERATIONS.md`;
4. Issue #56 when available;
5. `V3_COVERAGE_STATUS.md`;
6. `FORMALIZATION_STATE.md`;
7. this fallback handoff;
8. live main/branches/PR/CI reconciliation.
