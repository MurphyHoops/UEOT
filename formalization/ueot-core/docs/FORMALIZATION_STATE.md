# UEOT Core Lean — Live Formalization State

> Recovery entry point. Source-level truth is `V3_COVERAGE_STATUS.md`.

Last synchronized: **2026-09-12**

## Environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

Promotion requires semantic source match, official import reachability, green
feature CI, clean-port CI, PR CI, merge/integration to `main`, green post-main
CI, and ledger synchronization.

## Current integrated checkpoint

| status | count |
|---|---:|
| proved | **49** |
| partial | **0** |
| pending | **57** |
| total | **106** |

Latest completed proof promotion: **P-INV-05**.

Evidence:
- source-facing feature head `1a698c743bce27d0e3d914cf3cec707a984eefb8`
- feature CI run `34614373920`: success
- clean promotion head `d6750f42a2994dadacc7678642518a7129f22e43`
- clean CI run `34625357569`: success
- PR #39 CI run `34625787902`: success
- integrated main commit `7d52e949b9788a32e3c5ce7ab9eec0f4ad85e58d`
- post-main CI run `34626175917`: success
- integrated source-facing module `UEOT/V3/PredictableOLSSourceConfidence.lean`

P-INV-05 machine-checks the predictable-design OLS concentration theorem all
the way from source-time stochastic assumptions to the exact frozen Euclidean
radius. The promoted theorem explicitly adds the standard adaptedness condition
that `xi (n+1)` is `F (n+1)`-measurable; this is required for conditional-MGF
iteration and is documented as a source correction rather than hidden behind a
final-score black-box assumption.

## Active parallel lanes

### P-STAT-06 — RKHS/MMD simultaneous embedding error [HOT]

Main contains green reusable infrastructure:
- exact one-replacement sensitivity `2/N`;
- independent centered Hilbert off-diagonal cancellation;
- empirical-mean squared-norm expansion;
- exact second moment `E||mean Z_i||^2 <= 1/N`;
- direct first-moment bound `E||mean Z_i|| <= 1/sqrt(N)`;
- conditional-sub-Gaussian Azuma wrapper;
- exact parameter normalization `N*(1/N^2)=1/N`;
- exact scalar tail `exp(-N*epsilon^2/2)`.

Remaining source closure:
1. construct the concrete Doob increments for the RKHS norm statistic from the
   `2/N` bounded-difference lemma;
2. discharge the required conditional Hoeffding/sub-Gaussian hypotheses;
3. take the finite `L` union bound;
4. expose the exact source-facing radius
   `(1 + sqrt(2*log(L/alpha)))/sqrt(N)`.

P-STAT-06 is intentionally **not** counted proved yet.

### Information / structural packet [WARM]

Next low-overlap source audit:
- P-INFO-02, P-INFO-03, P-INFO-04 using the integrated KL/entropy/information
  stack;
- P-INT-01 after the information packet, reusing the existing prediction and
  conditional-information infrastructure rather than introducing a duplicate
  independence formalism.

### Remaining inverse / identifiability packet [WARM]

P-INV-01 through P-INV-05 are now fully promoted. The next inverse-problem work
should be selected from the remaining frozen source P-IDs only after a fresh
source/dependency audit, reusing the Fisher and predictable-OLS libraries now on
`main`.

## Promotion protocol

1. source audit;
2. feature full-target CI;
3. clean-port onto newest green Lean-affecting `main`;
4. clean-port CI;
5. PR CI;
6. serialized main integration;
7. post-main CI;
8. ledger synchronization.

Parallel proof development is allowed; main promotion remains serialized.

## Recent main promotions

- P-FAC-01 — #502
- P-DYN-02 — #506
- P-REC-02 — #519
- P-PER-01 — #540
- P-ID-01 — #547
- P-STAT-02 — #563
- P-INFO-01 — #572
- P-STAT-05 — #584
- P-STAT-01 — #599
- P-STAT-07 — #629
- P-STAT-09 — #641
- P-STAT-08 — #648
- P-INV-01 — #666
- P-INV-02 — #682
- P-INV-04 — #697
- P-INV-03 — post-main run `34576124342`
- P-INV-05 — PR #39, post-main run `34626175917`

## Mandatory recovery procedure

1. Read this file and `V3_COVERAGE_STATUS.md`.
2. Fetch current `main` SHA and latest main Action.
3. Compare every active branch with current main and inspect its latest CI.
4. Never count feature-green work as proved.
5. New proof modules must be reachable from `UEOT` / `UEOT.V3`.
6. For theorem wording/constants, use the frozen canonical source, never memory.
7. If documentation and merged green Lean disagree, repair the documentation
   before the next proof promotion.

## Repository truth hierarchy

- source ledger: `docs/V3_COVERAGE_STATUS.md`
- live state: `docs/FORMALIZATION_STATE.md`
- official import graph: `UEOT/V3.lean`
- execution roadmap: `docs/PARALLEL_FORMALIZATION_ROADMAP.md`
