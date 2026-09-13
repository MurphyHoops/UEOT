# UEOT Core v3.0 Lean Coverage Status

This file is the **authoritative source-level P-ID ledger** for the frozen
`UEOT_Core_Mathematics_v3.0_Complete.md` specification.

## Verification contract

- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`
- canonical source object: available in the project File Library for semantic audit
- exact canonical source bytes in public repo: **pending synchronization**

A P-ID is counted `proved` only after semantic matching against the canonical
frozen source object, official import reachability, required CI gates, main
integration, green post-main CI, prohibited-proof/axiom audit, and ledger
synchronization.

Public source-artifact reproducibility is tracked separately. The canonical SHA
must not be claimed as independently recomputed until the exact raw bytes are
present in the public repository.

## Current source-level coverage

| status | count |
|---|---:|
| **proved** | **57** |
| **partial** | **0** |
| **pending** | **49** |
| **total** | **106** |

`pending` means only “not yet counted proved”; it does not mean no relevant
mathematics or Lean code exists.

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
- **Internal/external factorization:** P-INT-01, P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-02, P-INFO-03, P-INFO-04, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02
- **QSD:** P-QSD-02
- **Persistence:** P-PER-01, P-PER-03
- **Transport / identity:** P-ID-01, P-ID-02
- **Representation covariance:** P-FAC-01
- **Omega / integrity:** P-OMG-01, P-OMG-02

Count check: `55 + 2 = 57`.

## Newly counted promotions — P-OMG-01 and P-OMG-02

### P-OMG-01 — minimal destructive-set reconstruction

Frozen source contract: in the finite deletion model, failure is monotone under
adding deleted mechanisms and every failing deletion set contains an
inclusion-minimal failing deletion set. Equivalently the failure family is the
upward closure of its minimal destructive sets.

Canonical theorem:

- `UEOT.V3.OmegaMinimalFailure.p_omg_01`.

Implementation facts:

- reuses `UEOT.Finite.exists_minimal_subset`; no duplicate blocker theory;
- represents the source Boolean clause `χ(D)=0` by a generic monotone failure
  predicate;
- the theorem is slightly more general than the finite-universe presentation:
  only each deletion set must be finite, which includes the frozen source case.

### P-OMG-02 — causal-integrity margin

Frozen source contract: for a fixed nonempty failure set `F`,
`Γ(T)=inf_{x∈F} d(T,x)` is 1-Lipschitz.

Canonical theorem:

- `UEOT.V3.OmegaIntegrityMargin.p_omg_02`.

Implementation facts:

- `integrityMargin F T = Metric.infDist T F`;
- reuses Mathlib's exact point-to-set theorem `Metric.lipschitz_infDist_pt`;
- retains the source nonempty-set hypothesis even though the library result is
  stronger.

Joint verification evidence:

- P-OMG-01 feature `formal/pomg01-minimal-failure` head
  `effa5bf10787095b2dd1bb86e68f100cb907f0af`, CI `34750708593`: success;
- P-OMG-02 feature `formal/pomg02-integrity-margin` head
  `8d5ddee1faff1ae588a478e2a1c58235852d7500`, CI `34750765181`: success;
- combined clean integration commit
  `4db94c39dddce53a5543e40568e5fc104321e88b`;
- integration CI `34751042701`: success;
- `main` fast-forwarded to the same clean integration commit;
- post-main CI `34751300612`: success;
- prohibited-proof audit: zero `sorry`, zero `admit`, zero `native_decide`,
  zero unsourced `axiom` in the two new source-facing proof files;
- canonical-source semantic audit completed 2026-09-13.

**Status: BOTH PROVED / COUNTED.**

## Previously counted promotions

### P-INT-01

Frozen source contract: for Standard-Borel variables and structured statistics
`M=f(H^S)`, `U=g(H^E)`, with `Z=(M,U)`,

`Y_f^+ ⟂ H | (M,U)  ↔  C^f = Psi(M,U) a.s.`

for every protocol in the declared countable intervention family, using common
versions on one common conull set.

Canonical source-facing theorems:

- `UEOT.V3.InformationPInt01.p_int_01`;
- `UEOT.V3.InformationPInt01Common.p_int_01_common`;
- `UEOT.V3.InformationPInt01Common.p_int_01_common_decoder`.

Evidence: feature CI `34747270058`, clean integration CI `34749908649`, main
commit `d757ea0dd14755233b94d40763f457773a52089f`, post-main CI
`34750114264`; prohibited-proof and source-semantic audits complete.

### P-INFO-03

Canonical theorem:
`UEOT.V3.InformationPredictiveRateZero.predictiveObjectRateZero_eq_sourceEntropy`.

Evidence: feature head `b90cb81f5ae600ba961e2948f304aa87472c8ea9`, feature CI
`34744325632`, integration CI `34744658528`, main
`57e987a18a5dd8feca224b91e3e78b93c2a44de8`, post-main CI
`34744919310`; canonical-source semantic and prohibited-proof audits complete.

### P-ID-02

Canonical source-facing theorems:
`development_error_step`, `development_pipeline`,
`development_pipeline_uniform_geom`, and
`development_pipeline_uniform_contraction` in
`UEOT.V3.DevelopmentTransport`.

Evidence: feature CI `34716348615`, PR #54, main
`4a29c2d5aa6a805d867e1934f6013aa49f1dc431`, post-main CI `34717095993`.

### P-INFO-02 / P-INFO-04

P-INFO-02 canonical theorem: `UEOT.V3.InformationPInfo02.p_info_02_ennreal`;
main `c1d0d94b7d01a5d6f370d2de4f40e8c1674bcd8f`, post-main CI `34692828935`.

P-INFO-04 canonical theorems:
`UEOT.V3.InformationPInfo04.p_info_04` and
`UEOT.V3.InformationConditionalBinaryMutualEntropy.p_info_04_conditional_binary`;
main `e19eee7082418f1826650316b533c0380a9a451f`, post-main CI `34706528781`.

## Active unresolved front

There are **49 not-yet-counted P-IDs**. Three independent source-facing proof
lanes are currently active:

- **P-DDH-01:** `formal/pddh01-gauge-cancellation`;
- **P-ALI-03:** `formal/pali03-coordination-threshold`;
- **P-EVO-01:** `formal/pevo01-price-decomposition`.

The remaining **46** are still in source-to-main A/B/C/D audit or later proof
queues. Feature-green work does not change the 57/106 ledger.

Known non-A fronts include P-PER-02, P-PER-04, P-REC-03, P-REC-04,
P-QSD-01, P-QSD-03 and P-QSD-04. The QSD numbering is source-locked:
P-QSD-01 is the conditional-stabilization/QSD theorem; P-QSD-03 is the
simultaneous persistence-window theorem.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing the bytes and independently recomputing the SHA-256 remains a
separate repository reproducibility task and does not change proof count by
itself.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** source P-IDs pass the
source-theorem proof contract, with no theorem counted from a helper or
feature-green branch alone.