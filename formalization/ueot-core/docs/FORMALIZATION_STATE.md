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
| proved | **46** |
| partial | **0** |
| pending | **60** |
| total | **106** |

Latest completed proof promotion: **P-INV-02**.

Evidence:
- feature head `945d58c9ba35c71f319f37e2fa7ffbec06304397`
- feature CI #671: success
- clean head `b4ef000384a581400ebcf132e86adcfa14926849`
- clean CI #677: success
- PR #37 CI #679: success
- squash merge `cbfe8eff494a558f113d2e79136655b9ddb61ca7`
- post-main CI #682: success

P-INV-02 now machine-checks the frozen Fisher gauge statement: likelihood
invariance along a smooth orbit forces zero directional score almost
everywhere, hence the Fisher action annihilates the orbit tangent.

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
- exact scalar/Azuma tail algebra.

Current state: the pre-import Azuma commit CI #680 is green, but importing the
Azuma layer into the official V3 target at head `9fb2da89...` makes CI #681
fail during `lake build UEOT`. Repair this integration before adding the final
bounded-difference/Doob bridge and finite union wrapper.

### P-INV-03 — Fisher information accumulation

Branch: `formal/pinv03-fisher-intersection`.

Current head is based directly on the P-INV-02 main checkpoint. CI #683 and
#684 are green. `FisherIntersection.lean` proves the PSD kernel-intersection
mechanism. Remaining source obligation: derive total Fisher additivity from
conditional independence and zero-mean experiment scores, then connect it to
the kernel theorem in one source-facing wrapper.

### P-INV-04 — noiseless design identifiability

Development branch: `formal/pinv04-design-identifiability`.

The source-facing theorem `p_inv_04` is implemented and latest branch CI #678
is green. It proves injectivity of the fixed noiseless design map iff the Gram
quadratic form is strictly positive away from zero, exactly matching
`G_N ≻ 0`. The development branch is behind current main and is queued for a
clean promotion port.

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
