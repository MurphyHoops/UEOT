# UEOT Core v3.0 Lean Coverage Status

This file is the **authoritative source-level P-ID ledger** for the frozen
`UEOT_Core_Mathematics_v3.0_Complete.md` specification.

Operational branch/CI state is tracked in `FORMALIZATION_STATE.md`. Detailed
promotion narratives from the 32-proof checkpoint are preserved verbatim at
`archive/2026-09-10/V3_COVERAGE_STATUS_32_PROVED.md`; later history is also
preserved by Git.

## 1. Source identity and verification contract

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- pinned Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

A P-ID is `proved` only after all of the following gates are satisfied:

1. Lean declarations semantically match the literal frozen v3.0 source statement;
2. declarations are reachable from the official `UEOT` / `UEOT.V3` import graph;
3. feature-branch official-target CI passes against the pinned lock;
4. integration PR official-target CI passes;
5. the proof is merged to `main`;
6. post-merge `main` CI passes;
7. this ledger is synchronized.

A green helper theorem, an unimported module, or a green feature branch alone
is not a source-level proof promotion.

## 2. Current source-level coverage

| status | count |
|---|---:|
| **proved** | **44** |
| **partial** | **0** |
| **pending** | **62** |
| **total** | **106** |

There are currently **no partial P-IDs**. Every unresolved source P-ID remains
explicitly pending until it passes the full gate above.

## 3. Proved P-ID set

The 44 source-matched, machine-checked P-IDs are:

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-01, P-STAT-02, P-STAT-03, P-STAT-04, P-STAT-05, P-STAT-07, P-STAT-08, P-STAT-09
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

Count check: `4 + 6 + 3 + 4 + 8 + 1 + 2 + 1 + 1 + 2 + 2 + 1 + 2 + 1 + 2 + 1 + 2 + 1 + 1 = 44`.

## 4. 2026-09-11 promotion — P-STAT-01

P-STAT-01 is promoted from `pending` to `proved`.

The frozen source states that for `L` fixed conditional response laws on a
finite response alphabet of size `K`, with `N` independent samples inside each
response cell,

`P(max_j D_TV(p_j,pHat_j) > eta) <= L * 2^(K+1) * exp(-2*N*eta^2)`.

It also gives the clipped confidence radius

`eta_NKL(alpha) = min 1 (sqrt (((K+1)*log 2 + log(L/alpha))/(2*N)))`.

The integrated Lean proof constructs the empirical finite-alphabet probability
measure, proves the one-sided Bernoulli/Hoeffding event bound under the pinned
Mathlib API, obtains the lower tail by complement, derives the exact two-sided
factor `2`, unions over all finite alphabet subsets and fixed response cells,
and then performs the exact analytic inversion to the source radius. The
clipping branch is discharged using the deterministic probability-measure bound
`D_TV <= 1`.

The formal theorem deliberately assumes independence only among the `N` samples
within each response cell. No independence across response cells is assumed,
and no extra union factor over carrier candidates is introduced.

Verification evidence:

- final feature head: `c1cf34443572b0d7934f472d69018078fd24930a`
- feature branch full-target CI #596 (`34547929445`): success
- clean-port head: `954186a82d7be781a19cfd2e26fb1da0c8cee1bf`
- clean-port branch full-target CI #597 (`34548185047`): success
- PR #30 full-target CI #598 (`34548405598`): success
- squash merge: `9b3a65ee836e32fa99f6670530e3f7afe72ab070`
- post-merge main full-target CI #599 (`34548608501`): success
- integrated modules:
  - `UEOT/V3/FiniteAlphabetConcentration.lean`
  - `UEOT/V3/FiniteAlphabetSampling.lean`
  - `UEOT/V3/FiniteAlphabetPStat01.lean`
  - `UEOT/V3/FiniteAlphabetPStat01Radius.lean`

## 5. 2026-09-11 promotions — P-STAT-07, P-STAT-08, P-STAT-09

### P-STAT-07 — kernel-transport covariance

The source-matched theorem formalizes genuine MMD covariance under a
bimeasurable bijection and synchronously transported kernel; it does not replace
MMD by total variation.

Verification evidence:

- clean promotion branch full-target CI #622: success
- PR #31 full-target CI #625: success
- squash merge: `97533726d71e28b8f4aac1d956db7f65fe98ebda`
- post-merge main full-target CI #629: success
- integrated modules:
  - `UEOT/V3/MMDTransport.lean`
  - `UEOT/V3/MMDTransportSource.lean`

### P-STAT-08 — finite-candidate discovery

For a finite candidate class, `[0,1]` losses and `N` independent validation
observations, the integrated proof establishes the exact source radius

`u = sqrt(log(2*m/alpha)/(2*N))`

and proves that an empirical-risk minimizer has true risk at most the finite
class optimum plus `2*u`, with failure probability at most `alpha`. The proof
uses candidatewise two-sided Hoeffding concentration plus a finite union bound;
it assumes no independence between different candidates.

Verification evidence:

- source-complete feature head: `c681bd8208ac52d5a015ae2486162b506232af4f`
- feature branch full-target CI #640: success
- clean promotion head: `62b2007831659fa49cd04eb7b2babd4758f9c0a0`
- clean promotion full-target CI #643: success
- PR #33 full-target CI #644: success
- squash merge: `f03ea2ae9996228d86c742d7f787b95a85ad5898`
- post-merge main full-target CI #648: success
- integrated modules:
  - `UEOT/V3/FiniteCandidateDiscovery.lean`
  - `UEOT/V3/BoundedLossSampling.lean`
  - `UEOT/V3/BoundedLossTwoSided.lean`
  - `UEOT/V3/FiniteCandidatePStat08.lean`

### P-STAT-09 — average-error transport

The source-matched theorem proves both deployment-transport clauses: the
Radon–Nikodym density-ratio bound `E_nu[e] <= C E_mu[e]` under
`nu << mu, dnu/dmu <= C`, and the TV/span bound
`E_nu[e] <= E_mu[e] + delta` for `0 <= e <= 1` and
`D_TV(nu,mu) <= delta`. The RN branch does not replace the source assumption by
a stronger measure-domination hypothesis.

Verification evidence:

- feature branch full-target CI #630: success
- clean promotion full-target CI #633: success
- PR #32 full-target CI #637: success
- squash merge: `b21f91f233e7cb65c6f1d6ec928b4870ceee3db4`
- post-merge main full-target CI #641: success
- integrated module: `UEOT/V3/AverageErrorTransport.lean`

## 6. Recent promotion evidence since the archived 32-proof checkpoint

| P-ID | squash merge | post-merge main CI |
|---|---|---|
| P-FAC-01 | `29bb6b3fb55cde2d7a87577f4d0ff15c14e29aa0` | #502 success |
| P-DYN-02 | `8ac668253c4d8bc62ab22f250701bc0a190b6049` | #506 success |
| P-REC-02 | `189fa6b476b0199b321c8d8c2b521f744c0b64ef` | #519 success |
| P-PER-01 | `3d3ecb46416ea156e06fffd70684937f8d94caf3` | #540 success |
| P-ID-01 | `72b0703270df84d5a92f90d5e01c034777ff37dc` | #547 success |
| P-STAT-02 | `5886c7baa4d9b4936e21dbd5639d7c893af22053` | #563 success |
| P-INFO-01 | `0dd65bc8ae40fdd1afbfdf0cf61c155585a5a2ac` | #572 success |
| P-STAT-05 | `5e5071820a5e30554b23f8344b3315841b0e4b6a` | #584 success |
| P-STAT-01 | `9b3a65ee836e32fa99f6670530e3f7afe72ab070` | #599 success |
| P-STAT-07 | `97533726d71e28b8f4aac1d956db7f65fe98ebda` | #629 success |
| P-STAT-09 | `b21f91f233e7cb65c6f1d6ec928b4870ceee3db4` | #641 success |
| P-STAT-08 | `f03ea2ae9996228d86c742d7f787b95a85ad5898` | #648 success |

The full theorem-by-theorem narratives and CI evidence for the earlier
32-proof checkpoint remain in
`docs/archive/2026-09-10/V3_COVERAGE_STATUS_32_PROVED.md`. No previously proved
P-ID is removed or downgraded by this ledger synchronization.

## 7. Active unresolved parallel front

Proof development remains parallel while main promotion remains serialized.
The current high-priority lanes are:

### P-STAT-06 — simultaneous RKHS embedding error

Branch: `formal/pstat06-mmd-concentration`.

Frozen source statement: for `L` fixed response laws, each with `N` independent
samples, a separable RKHS, `k(y,y)<=1`, and Bochner-integrable feature map,

`max_j ||muHat_j-mu_j|| <= (1 + sqrt(2*log(L/alpha)))/sqrt(N)`

with probability at least `1-alpha`.

The completed helper layers include exact `2/N` replacement sensitivity,
independent centered Hilbert off-diagonal cancellation, and the deterministic
empirical-mean squared-norm expansion. The full source theorem remains pending
until the second-moment/Jensen/McDiarmid/finite-union chain is machine checked.

### P-INV-01 — equal-prior binary testing

Branch: `formal/pinv01-binary-testing`.

Frozen source statement:

`R* = (1/2) * (1 - D_TV(P0,P1))`.

The universal TV lower bound is machine-checked on the feature branch. The
general-space attainability layer is being proved via Hahn decomposition, the
measure-theoretic equivalent of the source density-comparison event. This P-ID
remains pending until the optimal event theorem and all promotion gates pass.

## 8. Completion rule

The v3.0 formalization is complete only when **all 106 source P-IDs** have been
semantically matched and machine-checked under the frozen source. A green
repository build proves only the declarations currently imported; it does not
by itself prove full manuscript coverage.
