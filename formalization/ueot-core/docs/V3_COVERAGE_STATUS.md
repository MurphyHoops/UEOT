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
import reachability, feature CI, clean-port CI, PR CI, main integration, green
post-main CI, and ledger synchronization.

## Current source-level coverage

| status | count |
|---|---:|
| **proved** | **49** |
| **partial** | **0** |
| **pending** | **57** |
| **total** | **106** |

There are no partial P-IDs.

## Proved P-ID set

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-01, P-STAT-02, P-STAT-03, P-STAT-04, P-STAT-05, P-STAT-07, P-STAT-08, P-STAT-09
- **Invariant / identifiability:** P-INV-01, P-INV-02, P-INV-03, P-INV-04, P-INV-05
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

Count check: `4 + 6 + 3 + 4 + 8 + 5 + 1 + 2 + 1 + 1 + 2 + 2 + 1 + 2 + 1 + 2 + 1 + 2 + 1 + 1 = 49`.

## Latest promotion — P-INV-05

Frozen statement: for bounded predictable linear design and conditionally
sub-Gaussian noise, on the samplewise Gram event `G_N ⪰ N*kappa*I`, the OLS
estimation error obeys

`||thetaHat-thetaStar||_2 <= (sigma*B/kappa) * sqrt(2*d*log(2*d/alpha)/N)`

outside an event of probability at most `alpha`.

The integrated Lean development machine-checks the full source-facing chain:
predictable random multiplier conditional-MGF control, product integrability,
strong adaptedness, martingale score accumulation, two-sided coordinate tails,
finite-`d` union control, exact threshold/radius normalization, source-time to
`Fin N` index identification, the OLS normal equation, the full matrix-form
good-Gram predicate, and the final Euclidean confidence theorem.

Semantic correction: the formal source theorem makes explicit that `xi (n+1)`
is measurable with respect to `F (n+1)`. This adaptedness is required for the
conditional-MGF iteration and is implicit in the standard filtered-process
formulation. No final-score sub-Gaussian black box is assumed in the promoted
source theorem.

Verification evidence:

- source-facing feature branch: `formal/pinv05-source-confidence`
- source-facing feature head: `1a698c743bce27d0e3d914cf3cec707a984eefb8`
- feature full-target CI run `34614373920`: success
- clean promotion branch: `formal/pinv05-clean-port`
- clean promotion head: `d6750f42a2994dadacc7678642518a7129f22e43`
- clean-port CI run `34625357569`: success
- PR #39 CI run `34625787902`: success
- integrated main commit: `7d52e949b9788a32e3c5ce7ab9eec0f4ad85e58d`
- post-main CI run `34626175917`: success
- source-facing module: `UEOT/V3/PredictableOLSSourceConfidence.lean`

## Recent promotion evidence

| P-ID | integrated commit | post-main CI |
|---|---|---|
| P-FAC-01 | `29bb6b3fb55cde2d7a87577f4d0ff15c14e29aa0` | #502 success |
| P-DYN-02 | `8ac668253c4d8bc62ab22f250701bc0a190b6049` | #506 success |
| P-REC-02 | `189fa6b476b0199b321c8d8c2b521f744c0b64ef` | #519 success |
| P-PER-01 | `3d3ecb46416ea156e06fffd70684937f8d94caf3` | #540 success |
| P-ID-01 | `72b0703270df84d5a92f90d5e01c034777ff37dc` | #547 success |
| P-STAT-02 | `5886c7baa4d94936e21dbd5639d7c893af22053` | #563 success |
| P-INFO-01 | `0dd65bc8ae40fdd1afbfdf0cf61c155585a5a2ac` | #572 success |
| P-STAT-05 | `5e5071820a5e30554b23f8344b3315841b0e4b6a` | #584 success |
| P-STAT-01 | `9b3a65ee836e32fa99f6670530e3f7afe72ab070` | #599 success |
| P-STAT-07 | `97533726d71e28b8f4aac1d956db7f65fe98ebda` | #629 success |
| P-STAT-09 | `b21f91f233e7cb65c6f1d6ec928b4870ceee3db4` | #641 success |
| P-STAT-08 | `f03ea2ae9996228d86c742d7f787b95a85ad5898` | #648 success |
| P-INV-01 | `e653401b51594d86f03c317bdd12decae1c27159` | #666 success |
| P-INV-02 | `cbfe8eff494a558f113d2e79136655b9ddb61ca7` | #682 success |
| P-INV-04 | `efd1f529e739aecd4b1331f7324ce5660384cd8c` | #697 success |
| P-INV-03 | `93de8c70353566e806a65afa3f29330cd69da29e` | `34576124342` success |
| P-INV-05 | `7d52e949b9788a32e3c5ce7ab9eec0f4ad85e58d` | `34626175917` success |

## Active unresolved parallel front

### P-STAT-06 — simultaneous RKHS embedding error

The main branch contains and compiles the four reusable infrastructure layers:

- exact one-replacement sensitivity `2/N`;
- independent centered Hilbert second-moment cancellation and
  `E||mean Z_i||^2 <= 1/N`;
- exact first-moment bridge `E||mean Z_i|| <= 1/sqrt(N)`;
- conditional-sub-Gaussian Azuma wrapper with the exact `1/N^2` increment
  parameter sum and tail `exp(-N epsilon^2/2)`.

These layers are integrated and post-main green, but **P-STAT-06 is not yet
counted proved**. The remaining source obligation is the concrete
bounded-difference/Doob increment construction for the RKHS statistic plus the
finite-`L` union wrapper yielding exactly
`(1 + sqrt(2*log(L/alpha)))/sqrt(N)`.

## Completion rule

UEOT Core v3.0 formalization is complete only when all **106** source P-IDs pass
the full verification contract above.
