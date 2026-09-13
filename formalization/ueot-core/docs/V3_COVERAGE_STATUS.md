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
| **proved** | **59** |
| **partial** | **0** |
| **pending** | **47** |
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
- **Dual-drive / alignment:** P-DDH-01, P-ALI-03

Count check: `57 + 2 = 59`.

## Newly counted promotions — P-DDH-01 and P-ALI-03

### P-DDH-01 — dual-drive gauge freedom

Frozen source contract:

`Pi' = Pi + lambda chi`, `Phi' = Phi + chi`

leaves the combined objective `Pi - lambda Phi` invariant.

Canonical source-facing theorem:

- `UEOT.V3.DualDriveGauge.p_ddh_01`.

Implementation facts:

- exact real-algebra identity with a pointwise functional wrapper;
- no additional regularity or identifiability assumptions were introduced;
- the theorem formalizes the source non-identifiability/gauge statement only,
  leaving empirical semantic anchoring of the two drives separate.

Feature evidence:

- branch `formal/pddh01-gauge-cancellation`;
- source-closed head `71a26d2fce4087fb4c7ed763b42f74118186a739`;
- feature CI `34751815827`: success.

### P-ALI-03 — coordination threshold

Frozen source contract: in a real Hilbert space, for
`G_eta = (1-eta)G + eta g`, `0 <= eta <= 1`, and misalignment
`<g,G> < 0`, the parent-value instantaneous derivative is positive exactly when

`eta > -<g,G> / (||g||^2 - <g,G>)`.

Canonical source-facing theorem:

- `UEOT.V3.AlignmentThreshold.p_ali_03`.

Implementation facts:

- the final theorem is stated directly at the Hilbert-space level;
- the scalar inequality is retained only as an algebraic helper;
- the denominator positivity is derived from `<g,G><0` and `||g||^2>=0`;
- the source domain `0 <= eta <= 1` is retained.

Feature evidence:

- branch `formal/pali03-coordination-threshold`;
- source-closed head `bbb9f7b1cc8f202fedf5d096fe2707f760d83c4a`;
- feature CI `34751936845`: success.

### Joint promotion evidence

- authoritative clean integration branch:
  `formal/pddh01-pali03-integration-v3`;
- clean atomic integration/main proof commit:
  `9bff83a544929a0191596f6a1b9c7c8d2a6f87b7`;
- exact integration diff: two source-facing proof files plus the corresponding
  top-level imports;
- integration CI `34752277556`: success;
- `main` safely non-force fast-forwarded to the same proof commit;
- post-main CI `34752528830`: success;
- prohibited-proof audit in both new proof files:
  `sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`;
- canonical-source semantic audit completed 2026-09-13.

**Status: BOTH PROVED / COUNTED.**

## Previously counted promotions

### P-OMG-01 / P-OMG-02

P-OMG-01 canonical theorem:
`UEOT.V3.OmegaMinimalFailure.p_omg_01`.

P-OMG-02 canonical theorem:
`UEOT.V3.OmegaIntegrityMargin.p_omg_02`.

Evidence: feature CIs `34750708593` and `34750765181`, combined clean
integration `4db94c39dddce53a5543e40568e5fc104321e88b`, integration CI
`34751042701`, post-main CI `34751300612`; source-semantic and
prohibited-proof audits complete.

### P-INT-01

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

There are **47 not-yet-counted P-IDs**. Two source-facing lanes are currently
active:

- **P-EVO-01:** source-faithful explicit `M=D_b K`, deterministic
  `p'=pM/bar_b` Price-decomposition lane; latest feature head
  `1a17175b7a7bf2338c5bcc648085bf5e7ef09a30`;
- **P-COMP-03:** source-closed finite-cut composition-margin lane; feature head
  `7e074e694c26e52901342336b5e57b666df4fa8c`, feature CI `34752374454`:
  success; awaiting clean integration to latest main.

The remaining **45** are still in source-to-main A/B/C/D audit or later proof
queues. Feature green does not change the 59/106 ledger.

A high-value audit finding is that P-KL-01 may be an A-class closure: `main`
already contains `UEOT.V3.InformationEventBernoulli.bernoulliKL_event_le`,
which proves event-indicator KL data processing after exactly identifying the
event pushforward with a Bernoulli law. Exact matching to the frozen
`d_Bern` definition is still required before any P-KL-01 count.

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
