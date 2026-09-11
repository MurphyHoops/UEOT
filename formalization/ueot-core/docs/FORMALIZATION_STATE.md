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
feature and clean-port CI, green PR CI, merge to `main`, green post-main CI,
and ledger synchronization.

## Current integrated checkpoint

| status | count |
|---|---:|
| proved | **47** |
| partial | **0** |
| pending | **59** |
| total | **106** |

Latest completed proof promotion: **P-INV-04**.

Evidence:
- clean feature commit `2be89cd8e750ba24bbf5b29066e203aa423aca2c`
- feature CI #688: success
- official-import head `8e0522d6376832109956843b6dfa5e4119724449`
- official-import CI #689: success
- PR #38 CI #693: success
- squash merge `efd1f529e739aecd4b1331f7324ce5660384cd8c`
- post-main CI #697: success
- ledger synchronization commit `2e1bbcbd7163cb63b7f695b2352330b8e1a8bd0f`

P-INV-04 machine-checks the frozen noiseless full-parameter linear-design
statement: the fixed design is injective iff its Gram quadratic form is
strictly positive for every nonzero direction.

## Active parallel lanes

### P-STAT-06 — RKHS/MMD simultaneous embedding error

Branch: `formal/pstat06-mmd-concentration`.

Frozen target:
`max_j ||muHat_j-mu_j|| <= (1 + sqrt(2*log(L/alpha)))/sqrt(N)`
with probability at least `1-alpha`.

Implemented layers:
- exact one-replacement sensitivity `2/N`;
- independent centered Hilbert off-diagonal cancellation;
- empirical-mean squared-norm expansion;
- exact second moment `E||mean Z_i||^2 <= 1/N`;
- direct Hilbert first-moment bound;
- imported Mathlib conditional-sub-Gaussian Azuma wrapper.

The pinned-Mathlib Azuma wrapper is green at
`237f5c0ccc18166977ba0143e3763de5ab7e767d` (full official target). Remaining
source closure is the explicit bounded-difference/Doob increment bridge,
normalization of the `1/N^2` sub-Gaussian parameter sum to the source tail
`exp(-N t^2/2)`, and the finite `L` union wrapper yielding the exact source
radius.

### P-INV-03 — Fisher information accumulation

Branch: `formal/pinv03-fisher-intersection`.

Frozen claim:
- conditionally/independently generated experiment scores with zero mean have
  additive Fisher information;
- for PSD Fisher blocks, `ker(sum I_e) = intersection_e ker(I_e)`.

Machine-checked and green:
- abstract PSD kernel-intersection mechanism;
- centered independent scalar score cross terms have zero integral;
- cross-term helper full-target CI at
  `3d0ae444ef810f2f0d8808c966f6982cf1860c4e`.

Current development head
`be6140d0c9ad0aceb83c53660498f35a15af9ad1` expands finite summed scores into
Fisher matrix entries and cancels off-diagonal experiment terms. After that
layer is green, finish the Fisher-action equality, instantiate the PSD kernel
mechanism, and expose one source-facing `p_inv_03` wrapper before promotion.

### P-INV-05 — predictable-design OLS concentration [WARM]

Queued from the P-INV-04 checkpoint. The frozen source theorem requires
predictable bounded design, conditionally sub-Gaussian noise, a samplewise Gram
lower bound, and the exact `sqrt(2 d log(2d/alpha)/N)` rate. The static
P-INV-04 identifiability result alone is not sufficient.

## Promotion protocol

1. source audit;
2. feature full-target CI;
3. clean-port onto newest green Lean-affecting `main`;
4. clean-port CI;
5. PR CI;
6. squash merge;
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
