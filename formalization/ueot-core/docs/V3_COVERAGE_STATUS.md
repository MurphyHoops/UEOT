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
- exact frozen source bytes in public repo: **pending synchronization**

A P-ID is counted as `proved` only after semantic source matching, official
import reachability, feature CI, clean-port CI, PR CI, main integration, green
post-main CI, and ledger synchronization. While the canonical source artifact is
not synchronized into the repository, mathematically complete new P-IDs remain
uncounted until the exact-hash source audit can be executed.

## Current source-level coverage

| status | count |
|---|---:|
| **proved** | **50** |
| **partial** | **0** |
| **pending** | **56** |
| **total** | **106** |

There are no partial P-IDs. `pending` means only “not yet counted proved”; it
does not imply that no mathematical or Lean proof exists on a feature branch or
on `main`.

## Proved P-ID set

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-01, P-STAT-02, P-STAT-03, P-STAT-04, P-STAT-05, P-STAT-06, P-STAT-07, P-STAT-08, P-STAT-09
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

Count check: `4 + 6 + 3 + 4 + 9 + 5 + 1 + 2 + 1 + 1 + 2 + 2 + 1 + 2 + 1 + 2 + 1 + 2 + 1 + 1 = 50`.

## Latest counted promotion — P-STAT-06

Canonical source-facing theorem:
`UEOT.V3.HilbertMeanSourceFeatureRaw.source_feature_tail_exact_radius_raw_assumptions`.

Promotion evidence: PR #40, main
`d17d0e78ec7bf9cd35b1d314afa93aaeecdcb092`, post-main CI `34685534516`
success. P-STAT-06 is closed and counted.

## Integrated but not yet source-counted information work

### P-INFO-02 — predictive TV bound

The source-faithful predictive-TV theorem is mathematically complete and
integrated on `main`:

- canonical theorem: `UEOT.V3.InformationPInfo02.p_info_02_ennreal`;
- main commit: `c1d0d94b7d01a5d6f370d2de4f40e8c1674bcd8f`;
- post-main CI `34692828935`: success.

It remains outside the proved count solely because the exact frozen source
artifact is not yet synchronized into the repository for the final literal
source/hash audit.

### P-INFO-04 — both frozen clauses complete

P-INFO-04 is now mathematically and mechanically complete on `main`.

**Multiway sharp Fano**

- canonical theorem: `UEOT.V3.InformationPInfo04.p_info_04`;
- PR #47;
- main commit: `94e16dfb9cc9a2db6e000d8f5394c1b07869ce40`;
- post-main CI `34693509298`: success.

**Conditional binary identity-information lower bound**

- canonical theorem:
  `UEOT.V3.InformationConditionalBinaryMutualEntropy.p_info_04_conditional_binary`;
- finite KL/entropy bridge:
  `UEOT.V3.InformationConditionalBinaryMutualEntropy.conditionalBinaryMutualInfo_eq_ofReal_entropyForm_of_ne_top`;
- full compose CI `34705230951`: success;
- clean commit `8c76777e78e8d7f73b0d71397f8c81aeaa6e9c54`;
- clean CI `34705560077`: success;
- PR #51 CI `34706303512`: success;
- integrated main commit `e19eee7082418f1826650316b533c0380a9a451f`;
- post-main CI `34706528781`: success.

The binary proof handles reference-probability boundary cases, uses the actual
measurable decoder rather than a MAP substitution, and treats `CMI=⊤`
separately, so the frozen source theorem does not acquire a finite-CMI
assumption.

P-INFO-04 still remains outside the source-level proved count **only** because
the exact canonical source bytes are not synchronized into the public repo.
The final gate is exact SHA verification plus literal statement audit of both
clauses.

## Active unresolved front

- **P-INFO-03 — ACTIVE PROOF:** construct genuine countable-discrete
  `H(C|U)` by disintegration, then the random-encoder zero-distortion
  rate-distortion theorem. Active branch:
  `formal/pinfo03-countable-conditional`, current head
  `53573b6483fd05e836be1ff89445706d766f6029`, CI `34706765170` in progress at
  this synchronization point.
- **P-INFO-02 — SOURCE-ARTIFACT BLOCKED:** proof is complete; wait only for
  exact source-byte synchronization and final literal audit.
- **P-INFO-04 — SOURCE-ARTIFACT BLOCKED:** both proof clauses are complete,
  merged and post-main green; wait only for exact source-byte/hash audit.
- **P-INT-01 — BLOCKED:** reuse the general conditional-information interface
  produced by P-INFO-03; do not build a duplicate stack.

The machine-readable live details are in `docs/PID_STATUS.yaml`.

## Completion rule

UEOT Core v3.0 formalization is complete only when all **106** source P-IDs pass
the full verification contract above, with no theorem counted from a helper or
feature-green branch alone.
