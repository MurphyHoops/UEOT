# UEOT Core v3.0 Lean Coverage Status

This file is the **authoritative source-level P-ID ledger** for the frozen
`UEOT_Core_Mathematics_v3.0_Complete.md` specification. Historical detailed
promotion narratives remain in Git and in `docs/archive/`.

## Verification contract

- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

A P-ID is counted as `proved` only after semantic source matching, official
import reachability, feature CI, clean-port CI, PR CI, merge to `main`, green
post-main CI, and ledger synchronization.

## Current source-level coverage

| status | count |
|---|---:|
| **proved** | **47** |
| **partial** | **0** |
| **pending** | **59** |
| **total** | **106** |

There are no partial P-IDs.

## Proved P-ID set

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-01, P-STAT-02, P-STAT-03, P-STAT-04, P-STAT-05, P-STAT-07, P-STAT-08, P-STAT-09
- **Invariant / identifiability:** P-INV-01, P-INV-02, P-INV-04
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

Count check: `4 + 6 + 3 + 4 + 8 + 3 + 1 + 2 + 1 + 1 + 2 + 2 + 1 + 2 + 1 + 2 + 1 + 2 + 1 + 1 = 47`.

## Latest promotion — P-INV-04

Frozen statement: in the noiseless fixed linear model on the full parameter
space `R^d`, the design uniquely identifies the parameter iff the Gram matrix
`G_N` is positive definite.

The integrated Lean theorem uses the equivalent Gram quadratic form
`sum_t (phi_t^T v)^2` and proves that injectivity of the design map is
equivalent to strict positivity for every nonzero direction.

Verification evidence:

- clean feature commit: `2be89cd8e750ba24bbf5b29066e203aa423aca2c`
- feature CI #688: success
- official-import head: `8e0522d6376832109956843b6dfa5e4119724449`
- official-import CI #689: success
- PR #38 CI #693: success
- squash merge: `efd1f529e739aecd4b1331f7324ce5660384cd8c`
- post-main CI #697 (`34561611406`): success
- integrated module: `UEOT/V3/DesignIdentifiability.lean`

## Recent promotion evidence

| P-ID | squash merge | post-main CI |
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
| P-INV-01 | `e653401b51594d86f03c317bdd12decae1c27159` | #666 success |
| P-INV-02 | `cbfe8eff494a558f113d2e79136655b9ddb61ca7` | #682 success |
| P-INV-04 | `efd1f529e739aecd4b1331f7324ce5660384cd8c` | #697 success |

## Active unresolved parallel front

### P-STAT-06 — simultaneous RKHS embedding error

Branch: `formal/pstat06-mmd-concentration`.

Target:
`max_j ||muHat_j-mu_j|| <= (1 + sqrt(2*log(L/alpha)))/sqrt(N)`
with probability at least `1-alpha`.

Machine-checked layers already include exact `2/N` replacement sensitivity,
off-diagonal cancellation, empirical-mean squared-norm expansion,
`E||mean Z_i||^2 <= 1/N`, and the direct Hilbert first-moment bound. The
Azuma wrapper integration is being repaired against the pinned Mathlib API;
the bounded-difference/Doob bridge and final finite-union source wrapper remain
unpromoted.

### P-INV-03 — Fisher information accumulation

Branch: `formal/pinv03-fisher-intersection`.

The PSD kernel-intersection half is machine-checked. A reusable probability
lemma for centered independent scalar score cross terms is now under CI. The
remaining source obligation is to expand the finite total score/Fisher entries,
prove Fisher additivity, instantiate the PSD kernel theorem, and expose one
source-facing P-INV-03 wrapper.

### P-INV-05 — predictable-design OLS concentration

Queued next from the newest green main checkpoint. The frozen theorem requires
predictable bounded design, conditionally sub-Gaussian noise, and a Gram lower
bound; the static noiseless P-INV-04 theorem alone is not sufficient.

## Completion rule

UEOT Core v3.0 formalization is complete only when all **106** source P-IDs pass
the full verification contract above.
