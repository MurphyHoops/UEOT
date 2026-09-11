# UEOT Core Lean — Live Formalization State

> Recovery entry point. Source-level truth is `V3_COVERAGE_STATUS.md`.

Last synchronized: **2026-09-11**

## Environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

Promotion requires semantic source match, official import reachability, green
feature and clean-port CI, merge/integration to `main`, green post-main CI, and
ledger synchronization.

## Current integrated checkpoint

| status | count |
|---|---:|
| proved | **48** |
| partial | **0** |
| pending | **58** |
| total | **106** |

Latest completed proof promotion: **P-INV-03**.

Evidence:
- source-facing feature head `94541d36fd401d9779892446379ebb12d30f00f0`
- clean promotion head `93de8c70353566e806a65afa3f29330cd69da29e`
- clean CI run `34573930115`: success
- integrated main contains `UEOT/V3/FisherIntersection.lean`
- combined main head with P-STAT-06 infrastructure `dd77d56dd2c5d35440e4f3023ac7a22ab94830c3`
- post-main CI run `34576124342`: success
- ledger synchronization commit `16ebf4c201d3abd21b3dfba808eeefa8ae51b5d5`

P-INV-03 machine-checks the frozen Fisher accumulation statement: zero-mean
independent experiment score cross terms cancel, Fisher information adds, each
Fisher block is PSD, and the kernel of the total Fisher information equals the
intersection of the individual kernels.

## Active parallel lanes

### P-STAT-06 — RKHS/MMD simultaneous embedding error [HOT]

Main now contains green reusable infrastructure:
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

### P-INV-05 — predictable-design OLS concentration [HOT]

Branch: `formal/pinv05-predictable-ols`.

Frozen target:
`||thetaHat-thetaStar||_2 <= (sigma*B/kappa) * sqrt(2*d*log(2*d/alpha)/N)`
except on an event of probability at most `alpha`, under predictable bounded
design, conditionally sub-Gaussian noise, and the samplewise Gram lower bound.

Green machine-checked layers:
- Gram action/quadratic identity;
- finite-dimensional Cauchy-Schwarz;
- deterministic normal-equation/coercivity estimate
  `(N*kappa)^2 ||err||_2^2 <= ||Z||_2^2`;
- uniform coordinate threshold implies `||Z||_2^2 <= d*R^2`;
- resulting deterministic squared-error threshold bridge.

Next proof layers:
1. coordinate score sub-Gaussian theorem from predictable multipliers and
   conditional sub-Gaussian noise;
2. two-sided coordinate tail;
3. finite-`d` union bound;
4. exact frozen threshold substitution and square-root conversion;
5. source-facing `p_inv_05` wrapper and clean promotion.

## Promotion protocol

1. source audit;
2. feature full-target CI;
3. clean-port onto newest green Lean-affecting `main`;
4. clean-port CI;
5. serialized main integration;
6. post-main CI;
7. ledger synchronization.

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
