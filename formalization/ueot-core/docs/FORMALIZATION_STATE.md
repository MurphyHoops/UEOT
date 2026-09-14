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
| integrated proved, staged by this checkpoint | **78** |
| active proof / feature-green uncounted | **0** |
| source audit | **0** |
| blocked | **0** |
| pending/unclassified | **28** |
| total | **106** |

The authoritative full-green baseline before this ledger branch is **77/106** at
`main@6561169fae9529a822642c5b6921d7d9c59aa250`. P-PER-04 has completed all
source, feature, clean-integration, PR and proof-main gates, including resulting
main CI `34863965181` success at
`main@ba9b9c350038dafa52afdda954d2294361a01fc7`. This ledger branch stages
**78/106**. Do not call 78/106 full-green until this ledger branch passes branch
CI, PR CI, lands on `main`, and the resulting main CI succeeds.

## Newly staged proof — P-PER-04

Frozen Core 3 §8.6 is implemented at its declared positive-time tangency scope:

1. `V` is retained as the frozen closed viability/identity domain;
2. the curve is differentiable at zero and remains in `V` for nonnegative time;
3. the source Bouligand cone is one-sided (`h ↓ 0`), so the Lean target is Mathlib `posTangentConeAt`, not the two-sided real tangent cone;
4. derivative slopes converge from the right by `HasDerivAt.tendsto_slope_zero_right`;
5. the trajectory increments themselves witness the tangent-cone membership;
6. closedness is source-contract data even though this local necessity proof does not consume it;
7. the ambient-space generalization from `ℝ^d` to an arbitrary real normed space is strength-preserving;
8. K-VIA-01 Marchaud/Nagumo sufficiency remains a separate theorem and is not claimed here.

Canonical theorem surface:
- `UEOT.V3.ViabilityTangency.p_per_04`.

Promotion evidence:
- feature branch `formal/pper04-tangency-necessity-v1`;
- final feature head `ce6eccf5ca4b6f30aae1dcd0416fc1b79286f2d2`;
- feature CI `34858878140`: success;
- source semantic audit: complete;
- pinned-Mathlib tangent-cone definition audit: complete;
- prohibited-proof audit: clean;
- clean integration branch `formal/pper04-main-integration-v1`;
- clean integration head `f5db4c5e547866e488ad1d33c0789bc0ce5ec48c`;
- clean integration CI `34862446244`: success;
- PR #83 PR-triggered CI `34863236502`: success;
- proof main `ba9b9c350038dafa52afdda954d2294361a01fc7`;
- proof resulting-main CI `34863965181`: success.

## Previous full-green checkpoint — 77/106

P-QSD-03 is closed and counted in the 77/106 baseline at
`main@6561169fae9529a822642c5b6921d7d9c59aa250`. Its full ledger resulting-main
CI `34856357799` succeeded on attempt 3. Earlier attempts were external HTTP 504
failures before UEOT compilation and are not repository regressions.

P-BRG-01 is also already counted. P-REF-04 and P-REF-05 were counted before
these cycles; wrapper work must not be double-counted.

## Grounded non-quick fronts

- P-PER-02: Polish/Feller occupation-law theorem with tightness, Prokhorov and Portmanteau; sample-path empirical-frequency weakening is forbidden.
- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/04: source-locked distinct non-A results.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron-Frobenius asymptotic package; do not count an assumed-convergence
surrogate.

## Candidate next fronts after 78 full-green

- **P-REC-03:** first-step Markov identity for the finite hitting-time potential;
  pinned Mathlib has discrete hitting-time infrastructure, but the Markov
  first-step decomposition must still be proved at source strength.
- **P-REC-04:** stopped drift inequality for `τ_A ∧ N` followed by monotone
  convergence; bounded optional-stopping infrastructure exists but is not itself
  the source theorem.
- **P-COMP-01:** binary conditional-mutual-info machinery already exists in
  main, while the source still requires arbitrary finite nontrivial partitions,
  multi-block conditional product laws and the finite-family minimum equivalence.

No proof branch for these candidates is opened while the P-PER-04 ledger gate is
active.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available,
   `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green or proof-main green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent source/API audit without opening a conflicting proof branch.
