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
| proved | **45** |
| partial | **0** |
| pending | **61** |
| total | **106** |

Latest completed proof promotion: **P-INV-01**.

Evidence:
- feature CI #653: success
- clean head `e5d185cafc6897981b4d70b664dd30cc4ab7774e`
- clean CI #659: success
- PR #35 CI #664: success
- squash merge `e653401b51594d86f03c317bdd12decae1c27159`
- post-main CI #666: success

P-INV-01 now machine-checks the exact equal-prior general-space identity
`R* = (1/2) * (1 - D_TV(P0,P1))`, including existence and optimality of a
measurable attaining event.

## Active parallel lanes

### P-STAT-06 — RKHS/MMD simultaneous embedding error

Branch: `formal/pstat06-mmd-concentration`.

Frozen target:
`max_j ||muHat_j-mu_j|| <= (1 + sqrt(2*log(L/alpha)))/sqrt(N)`
with probability at least `1-alpha`.

Green layers:
- exact one-replacement sensitivity `2/N`;
- independent centered Hilbert off-diagonal cancellation;
- empirical-mean squared-norm expansion;
- exact second moment `E||mean Z_i||^2 <= 1/N` (CI #649);
- exact scalar first/second moment bridge (CI #660).

Current work: direct Hilbert first-moment theorem
`E||mean Z_i|| <= 1/sqrt(N)`, followed by McDiarmid and finite union.

### P-INV-02 — Fisher gauge zero directions

Branch: `formal/pinv02-fisher-gauge`.

Frozen target: a tangent to a smooth likelihood-invariant group orbit has zero
directional score and is annihilated by Fisher information.

Current work: the Fisher-action kernel core and local smooth-orbit derivative
bridge are implemented. The previous CI failure was only pointwise zero-function
normalization; commit `c5146ed0b3827d2c4fa2b0b116c39651ad91fb28` repairs it.
P-INV-02 remains pending until source audit and the entire promotion train pass.

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
