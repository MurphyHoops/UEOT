# UEOT Core v3.0 Lean Coverage Status

This file is the **authoritative source-level P-ID ledger** for the frozen
`UEOT_Core_Mathematics_v3.0_Complete.md` specification.

Operational branch/CI state is tracked in `FORMALIZATION_STATE.md`.
Detailed promotion narratives from the 32-proof checkpoint are preserved
verbatim at `archive/2026-09-10/V3_COVERAGE_STATUS_32_PROVED.md`.

## 1. Source identity and verification contract

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- pinned Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

A P-ID is `proved` only after all of the following gates are satisfied:

1. the Lean declarations semantically match the literal v3.0 source statement;
2. the declarations are reachable from the official `UEOT` / `UEOT.V3` import graph;
3. the feature branch passes the official target against the pinned lock;
4. the integration PR passes the official target;
5. the proof is merged to `main`;
6. post-merge `main` CI passes;
7. this ledger is synchronized.

A green helper theorem, an unimported module, or a green feature branch alone
is not a source-level proof promotion.

## 2. Current source-level coverage

| status | count |
|---|---:|
| **proved** | **39** |
| **partial** | **0** |
| **pending** | **67** |
| **total** | **106** |

There are currently **no partial P-IDs**. Every unresolved source P-ID remains
explicitly pending until it passes the full gate above.

## 3. Proved P-ID set

The 39 source-matched, machine-checked P-IDs are:

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-02, P-STAT-03, P-STAT-04
- **Quotient:** P-QUO-03
- **Refinement / agency:** P-REF-04, P-REF-05
- **Telescoping reward:** P-TEL-01
- **Bridge:** P-BRG-02
- **Metric:** P-MET-01, P-MET-02
- **Internal/external factorization:** P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02
- **QSD:** P-QSD-02
- **Persistence:** P-PER-01, P-PER-03
- **Transport / identity:** P-ID-01
- **Representation covariance:** P-FAC-01

Count check: `4 + 6 + 3 + 4 + 3 + 1 + 2 + 1 + 1 + 2 + 2 + 1 + 2 + 1 + 2 + 1 + 2 + 1 + 1 = 39`.

## 4. 2026-09-10 promotion — P-FAC-01

P-FAC-01 is promoted from `pending` to `proved`.

The source-facing covariance chain is derived from primitive transported
objects rather than assuming final path/value equality. The integrated Lean
proof covers bimeasurable microscopic coordinate transport, exact macro
pushforward and trajectory-law covariance, predictive sufficiency covariance,
exact dynamic-closure covariance, feedback path-law naturality, transported
rewards, policy-by-policy value equality, and equality of the optimal supremum.

Verification evidence:

- final feature head: `8c5e451c10f58fa032af73c66b1bd52f2fee7620`
- branch full-target CI #461: success
- PR #14 full-target CI #460: success
- squash merge: `29bb6b3fb55cde2d7a87577f4d0ff15c14e29aa0`
- post-merge main CI #502 (`34493839447`): success

## 5. 2026-09-10 promotion — P-DYN-02

P-DYN-02 is promoted from `pending` to `proved`.

The integrated proof matches the finite CTMC source criterion: block-sum
criterion iff generator intertwining, construction and uniqueness of the macro
generator, preservation of the CTMC-generator conditions, propagation through
the matrix exponential, and the converse through the right derivative at
`t = 0` on nonnegative time.

Verification evidence:

- clean integration head: `8c0212f4bfbd0e7bf9ed0c445e4662eb02cf04ef`
- clean branch full-target CI #504 (`34495257491`): success
- PR #23 full-target CI #505 (`34497593139`): success
- squash merge: `8ac668253c4d8bc62ab22f250701bc0a190b6049`
- post-merge main CI #506 (`34497930427`): success

## 6. 2026-09-10 promotion — P-REC-02

P-REC-02 is promoted from `pending` to `proved`.

The source theorem assumes the usual generator-domain / Dynkin / localization /
integrability conditions that make `m(t) = E[W(X_t)]` locally absolutely
continuous with a.e. derivative `E[(L W)(X_t)]`, together with the pointwise
bounds

`L W(x) <= -a W(x) + b` and `c d(x,V)^2 <= W(x)`.

The integrated Lean chain matches those layers without strengthening the source
to pointwise differentiability:

- `UEOT.V3.RecoveryContinuous.le_initial_of_ac_ae_deriv_nonpos` proves the
  fundamental absolutely-continuous/a.e.-derivative comparison lemma;
- `exponential_recovery_bound_ac_ae` proves the exact integrating-factor /
  Grönwall estimate at the source regularity;
- `UEOT.V3.RecoveryDynkin.DynkinExpectationCertificate` records exactly the
  analytic output supplied by the source's Dynkin/localization assumptions;
- `expected_generator_drift_of_pointwise` integrates the source's pointwise
  generator drift inequality;
- `expected_distance_domination_of_pointwise` integrates the pointwise
  Lyapunov-distance domination;
- `UEOT.V3.RecoveryDynkin.p_rec_02` combines those ingredients into the literal
  source-facing mean-square recovery bound.

No process-specific Dynkin theorem is silently postulated inside Core; such a
model-specific theorem is precisely what discharges the explicit certificate.

Verification evidence:

- clean integration head: `4cfe8aad3f19070942e167fea9749595f1f196ee`
- clean branch full-target CI #515 (`34500846267`): success
- PR #24 full-target CI #517 (`34501636481`): success
- squash merge: `189fa6b476b0199b321c8d8c2b521f744c0b64ef`
- post-merge main CI #519 (`34502013388`): success

The older divergent PR #18 was closed and was not used for integration.

## 7. 2026-09-11 promotion — P-PER-01

P-PER-01 is promoted from `pending` to `proved`.

The integrated theorem matches the frozen source's one-sided continuous
semiflow statement: eventual residence in a closed persistence domain and
precompactness of the orbit imply a nonempty compact omega-limit contained in
the domain, with exact invariance under every nonnegative-time map.

The reverse inclusion is not obtained by adding negative time or assuming a
right inverse. It follows the source proof: for `phi_(t_n)(x) -> y` with
`t_n -> infinity`, shift by a fixed `s`, use precompactness to extract a
convergent subsequence of `phi_(t_n-s)(x)`, show the limit remains in the
omega-limit, and pass the semiflow law through continuity to obtain a
predecessor `z` with `phi_s(z)=y`.

Verification evidence:

- clean feature head: `16c7a614c03b9404737b1b524d1abfbec2e3cb57`
- branch full-target CI #533 (`34507651005`): success
- PR #25 full-target CI #536 (`34508338456`): success
- squash merge: `3d3ecb46416ea156e06fffd70684937f8d94caf3`
- post-merge main CI #540 (`34508718076`): success

The older incomplete PR #17 was closed as superseded and was not used for
integration.

## 8. 2026-09-11 promotion — P-ID-01

P-ID-01 is promoted from `pending` to `proved`.

The integrated proof matches the frozen source's finite-horizon TCIC
defect-accumulation estimate. It models each `K_t` as the source's frozen
endpoint predictive kernel, assumes coherent measurable transports
`Γ_{s→t}`, and proves the endpoint total-variation defect by induction. The
induction step uses only total-variation triangle inequality, contraction under
measurable pushforward, the adjacent TCIC bound, and transport composition.

The source's literal supremum over initial macrostates is exposed directly as
`FrozenTransportSystem.p_id_01`; it is not inferred merely from an unexported
pointwise helper. The module is reachable through `UEOT.V3`.

Verification evidence:

- clean feature head: `ea6bb69d92f505f2662ad4eac64405470370246f`
- clean branch full-target CI #544: success
- PR #26 full-target CI #545 (`34509874478`): success
- squash merge: `72b0703270df84d5a92f90d5e01c034777ff37dc`
- post-merge main CI #547 (`34510479466`): success

## 9. 2026-09-11 promotion — P-STAT-02

P-STAT-02 is promoted from `pending` to `proved`.

The integrated theorem isolates the deterministic finite-sample propagation
step: on one simultaneous response-level total-variation error event, the
carrier response diameter changes by at most the sum of the two endpoint
errors. Consequently every carrier defect satisfies
`|eHat(S) - e(S)| <= 2 * eta` on that same event, with no second union bound
over the family of carriers.

The Lean implementation proves the endpoint TV perturbation inequality from
the triangle inequality, defines the carrier defect as the supremum of
response distances inside one readout fiber at a fixed protocol, and proves
supremum stability in both directions. P-STAT-01 remains the separate
probabilistic layer that supplies the simultaneous response event.

Verification evidence:

- feature head: `0275f7ad43f8505eefeefaefa0fb29052cf5b523`
- branch full-target CI #560 (`34542020196`): success
- PR #27 full-target CI #561 (`34542249026`): success
- squash merge: `5886c7baa4d9b4936e21dbd5639d7c893af22053`
- post-merge main CI #563 (`34542472419`): success

## 10. 2026-09-11 promotion — P-INFO-01

P-INFO-01 is promoted from `pending` to `proved`.

The integrated proof matches the frozen information-retention chain for a
deterministic statistic `M=f(H)`. It proves the exact standard-Borel identity
`I(H;Y)=I(M;Y)+I(H;Y|M)`, the epsilon-retention inequality, and the source's
discrete entropy corollary without silently restricting `M` to a finite type.

For the discrete step the Lean development constructs the copied-state law,
uses channel data processing, proves the countable-discrete Radon--Nikodym
density and exact `copy-KL = H(M)` identity in `ℝ≥0∞`, and therefore preserves
the legitimate `H(M)=∞` case. Standard-Borel disintegration then yields
`I(M;Y) <= H(M)`, and the source-facing wrapper concludes
`I(H;Y)-epsilon <= H(M)` using ordered subtraction rather than an invalid
real-valued infinity subtraction. A finite-state specialization recovers the
existing PMF Shannon sum.

Verification evidence:

- final development head: `315a0aeafdc2807f65d68ada7b2be6c70c09eedf`
- development full-target CI #562 (`34542278658`): success
- clean-port head: `cfddeca9a99dc6466b69807940720aaafc48a119`
- clean-port branch CI #570 (`34542970826`): success
- PR #28 CI #571 (`34543199236`): success
- squash merge: `0dd65bc8ae40fdd1afbfdf0cf61c155585a5a2ac`
- post-merge main CI #572 (`34543427529`): success

## 11. Prior promotion evidence

The full theorem-by-theorem narratives and CI evidence for the previous
32-proof checkpoint are preserved in:

`docs/archive/2026-09-10/V3_COVERAGE_STATUS_32_PROVED.md`

That archived checkpoint includes the evidence for P-PER-03, P-QSD-02,
P-DYN-03, P-DYN-04, P-PRED-03, P-PROC-01, P-INFO-05, P-REC-01, P-INT-02,
P-INT-03, P-DYN-01, P-MET-01/02, P-REF-05, P-TEL-01, P-BRG-02,
P-PRED-01/02, P-RES-01/02/05/06, P-CAR-04, and the recovered baseline.

No previously proved P-ID is removed or downgraded by this ledger compaction.

## 12. Active unresolved front

The highest-priority pending lane after this checkpoint is **P-STAT-01**.
The canonical v3.0 source has now been recovered from the user's File Library
and its exact statement is grounded: for `L` fixed conditional responses on a
finite alphabet of size `K`, with `N` independent samples per response,

`P(max_j D_TV(p_j,pHat_j) > eta) <= L * 2^(K+1) * exp(-2*N*eta^2)`.

The source proof is the finite-event argument: for each subset of the response
alphabet the empirical mass is a Bernoulli average; two-sided Hoeffding gives
`2*exp(-2*N*eta^2)`, followed by union bounds over at most `2^K` subsets and
`L` response cells. The source also states the clipped confidence radius

`min 1 (sqrt (((K+1)*log 2 + log(L/alpha))/(2*N)))`.

Pinned Mathlib 4.33.1 already supplies the needed sub-Gaussian Hoeffding lemma,
independent-sum tail bound, and measure union bound. The next proof packet must
formalize this exact finite-alphabet simultaneous event and connect it directly
to `UEOT.V3.StatisticalDefect.p_stat_02` without introducing an extra carrier
union bound.

## 13. Completion rule

The v3.0 formalization is complete only when **all 106 source P-IDs** have been
semantically matched and machine-checked under the frozen source. A green
repository build proves only the declarations currently imported; it does not
by itself prove full manuscript coverage.