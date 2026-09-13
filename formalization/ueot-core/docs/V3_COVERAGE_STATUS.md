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
| **proved** | **54** |
| **partial** | **0** |
| **pending** | **52** |
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
- **Internal/external factorization:** P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-02, P-INFO-03, P-INFO-04, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02
- **QSD:** P-QSD-02
- **Persistence:** P-PER-01, P-PER-03
- **Transport / identity:** P-ID-01, P-ID-02
- **Representation covariance:** P-FAC-01

Count check: `4 + 6 + 3 + 4 + 9 + 5 + 1 + 2 + 1 + 1 + 2 + 2 + 1 + 5 + 1 + 2 + 1 + 2 + 1 + 2 = 54`.

## Newly counted promotion — P-INFO-03

Frozen source contract:

`R_obj(0)=H(C|U)` for the discrete canonical predictive core
`C=P(Y∈·|H,U)`, with the source allowing genuinely randomized encoders
`P(M|H,U)` and arbitrary decoders `Q(.|M,U)` under zero expected total-variation
distortion.

Canonical theorem:

`UEOT.V3.InformationPredictiveRateZero.predictiveObjectRateZero_eq_sourceEntropy`.

Source-faithful implementation facts:

- the encoder is a Markov kernel `P(M|H,U)`, not a deterministic statistic;
- the encoder type contains `(H,U)` but not future `Y`, so future access is excluded structurally;
- arbitrary code alphabets are Standard Borel and are **not** restricted to countable spaces;
- countability is imposed only on the canonical core labels used to represent distinct future laws;
- zero expected TV gives almost-sure predictive-law equality and measurable recovery of `C` from `(M,U)`;
- the converse proves every zero-distortion scheme satisfies `H(C|U) <= I(H;M|U)`;
- the canonical deterministic encoder `M=C` and canonical decoder attain equality;
- `R_obj(0)` is the `sInf` over bundled code-space + encoder + decoder + zero-distortion schemes, rather than a fixed-code-space infimum;
- the Lean theorem is ENNReal-valued and does not need the source's explicit finiteness hypothesis, so the frozen finite-entropy case is included;
- code-space quantification is universe-polymorphic within the ambient Lean universe, which is the standard predicative implementation boundary and not a fixed-`M` restriction.

Verification evidence:

- final proof branch `formal/pinfo03-rate-zero` head
  `b90cb81f5ae600ba961e2948f304aa87472c8ea9`;
- final proof full-target CI `34744325632`: success;
- clean main-integration CI `34744658528`: success;
- main commit `57e987a18a5dd8feca224b91e3e78b93c2a44de8`;
- post-main full-target CI `34744919310`: success;
- prohibited-proof audit: zero `sorry`, zero `native_decide`, zero unsourced `axiom` in the integrated P-INFO-03 diff;
- canonical source semantic audit completed 2026-09-13.

**Status: PROVED / COUNTED.**

## Previously counted promotions

### P-ID-02

Canonical source-facing theorems:

- `UEOT.V3.DevelopmentTransport.development_error_step`;
- `UEOT.V3.DevelopmentTransport.development_pipeline`;
- `UEOT.V3.DevelopmentTransport.development_pipeline_uniform_geom`;
- `UEOT.V3.DevelopmentTransport.development_pipeline_uniform_contraction`.

Evidence: feature CI `34716348615`, PR #54, main commit
`4a29c2d5aa6a805d867e1934f6013aa49f1dc431`, post-main CI `34717095993`,
canonical-source semantic audit complete.

### P-INFO-02

Canonical theorem:
`UEOT.V3.InformationPInfo02.p_info_02_ennreal`.

Evidence: PR #46, main
`c1d0d94b7d01a5d6f370d2de4f40e8c1674bcd8f`, post-main CI `34692828935`
success, canonical-source semantic audit complete.

### P-INFO-04

Canonical theorems:

- `UEOT.V3.InformationPInfo04.p_info_04`;
- `UEOT.V3.InformationConditionalBinaryMutualEntropy.p_info_04_conditional_binary`.

Evidence includes PR #47 for multiway Fano and PR #51 for the conditional
binary clause, integrated main commit
`e19eee7082418f1826650316b533c0380a9a451f`, post-main CI `34706528781`
success, and canonical-source semantic audit complete.

## Active unresolved front

- **P-INT-01 — ACTIVE PROOF:** general Standard-Borel Predictive Factorization
  Characterization Theorem
  `Y ⟂ H | (M,U) ↔ C*=Psi(M,U) a.s.`. It now reuses the regular-conditional
  infrastructure stabilized by P-INFO-03; no duplicate information stack is allowed.
- **Remaining 51 unclassified P-IDs — SOURCE-TO-MAIN AUDIT:** identify
  source-facing theorems already on main before starting new proof stacks.
- **Public canonical source synchronization — REPRODUCIBILITY TASK:** copy the
  exact canonical bytes into the public repository and independently recompute
  SHA-256; this task does not change proof count by itself.

The machine-readable live details are in `docs/PID_STATUS.yaml`.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** source P-IDs pass the
source-theorem proof contract, with no theorem counted from a helper or
feature-green branch alone. Full third-party reproducibility additionally
requires the exact canonical source artifact and independently reproducible
frozen SHA-256.
