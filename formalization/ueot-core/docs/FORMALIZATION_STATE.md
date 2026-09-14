# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`. GitHub Issue #56
> carries the live cross-chat construction log when available.

Last synchronized: **2026-09-14**

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
| integrated proved, staged by this checkpoint | **74** |
| active proof / feature-green uncounted | **2** |
| source audit | **0** |
| blocked | **0** |
| pending/unclassified | **30** |
| total | **106** |

The authoritative full-green baseline before this ledger branch is **73/106** at
`main@0285b7b8da4c94cc7d8d890336cd97e5e64718cb`, CI `34808329108` success.
P-REF-02 has now completed all proof-side and proof-main gates and this branch
stages 74/106. Do not call 74/106 full-green until this ledger branch passes PR
CI, lands on `main`, and the resulting main CI succeeds.

## Newly staged proof — P-REF-02

Frozen §27.2 is implemented without weakening the declared belief-sufficiency
boundary:

- finite latent static parameter and hidden state model;
- predictive observation law determined by `(belief, action)`;
- exact positive-evidence Bayes update;
- zero evidence returns explicit `modelConflict`;
- arbitrary measurable observation spaces are covered through a
  Standard-Borel posterior/disintegration interface on the latent state;
- posterior plus observation marginal reconstruct the one-step joint law;
- posterior averaged over the next observation recovers the predicted latent
  law;
- one-step bounded-discount expected reward and continuation are written purely
  in belief coordinates;
- no generic Bellman theorem is smuggled into this P-ID.

Canonical source-facing theorem surface:
- `UEOT.V3.PRef02.p_ref_02_general_joint`;
- `UEOT.V3.PRef02.p_ref_02_general_update`;
- `UEOT.V3.PRef02.p_ref_02_discrete_observation`;
- `UEOT.V3.PRef02.p_ref_02_discrete_posterior`;
- `UEOT.V3.PRef02.p_ref_02_discrete_modelConflict`;
- `UEOT.V3.PRef02.p_ref_02_discounted_step`.

Evidence:
- clean integration `formal/pref02-main-integration-v1@0037fc0e494b46200ead20e2f5c3ce84a66eb577`;
- clean integration push CI `34808870460`: success;
- PR #71 PR-triggered CI `34810019287`: success;
- proof main `c1213a6014f37a84bdfe128cced1a472b682248e`;
- proof resulting-main CI `34810452071`: success;
- frozen-source semantic audit: complete;
- prohibited-proof audit: clean.

## Feature-green uncounted — P-REF-03

Frozen P-REF-03 requires arbitrary signal spaces, finite actions, integrable
payoffs, and free information that may be ignored. The branch
`formal/pref03-free-information-v1` models the signal as an arbitrary
sub-sigma-algebra and proves that the informed finite pointwise supremum of
conditional expectations weakly dominates the best fixed action.

- final feature head: `7ed287043f6da1e3d53bc67a95b7377bb989382a`;
- official feature CI `34809014590`: success;
- effective change relative to the prior green baseline: one source module plus
  one top-level import;
- feature history is divergent and **must not** be merged directly;
- exact next lifecycle step after 74 is full-green: fresh clean integration from
  that full-green main.

Feature green does not increment coverage.

## Active proof — P-BRG-01

Frozen §26.3 is source-locked to the finite fixed-positive-fitness no-mutation
replicator theorem. The contract includes all of:

1. exact recurrence and explicit closed form;
2. no creation of types absent from the initial support;
3. choose `R_*` as the maximum fitness on the initial positive-mass support;
4. each supported suboptimal type has geometric factor `(R_i/R_*)^n`;
5. the finite total suboptimal mass tends to zero exponentially;
6. support maximizers preserve their initial relative proportions.

Current branch: `formal/pbrg01-fixed-fitness-v1`.
Current feature head: `4a7facca5fc312568890ba547d343b7a04bbf2ef`.
Current official feature run: `34810851201`.

Implemented modules:
- `UEOT/V3/FixedFitnessSelection.lean`: exact algebraic recurrence/closed form,
  normalization, support preservation and equal-fitness ratio laws;
- `UEOT/V3/FixedFitnessConcentration.lean`: support maximizer, explicit
  geometric envelopes, finite suboptimal-mass convergence and maximizer ratio
  package.

This lane remains uncounted until its current CI and a final source-semantic
review both pass.

## Grounded non-quick fronts

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/03/04: source-locked distinct non-A results.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron-Frobenius asymptotic package; do not count an assumed-convergence
surrogate.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available,
   `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent audit/proof lane.
