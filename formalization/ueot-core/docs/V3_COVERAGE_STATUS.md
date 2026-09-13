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
- canonical source object: project File Library
- exact canonical source bytes in public repo: pending synchronization

A P-ID is counted `proved` only after frozen-source semantic matching, official
import reachability, feature/integration/post-main CI gates, prohibited-proof
audit, safe main integration, and ledger synchronization. Feature-green work
alone never changes this ledger.

## Current source-level coverage

| status | count |
|---|---:|
| **proved** | **67** |
| **partial** | **0** |
| **pending** | **39** |
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
- **Dual-drive / alignment:** P-DDH-01, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01
- **Evolution:** P-EVO-01

Count check: `66 + 1 = 67`.

## Newly counted promotion — P-COMP-04

Frozen source §15.4 is retained exactly: with side information packaging the
child canonical cores and interface `(C_{1:m},U)`, exact sufficiency/minimality
supplies a deterministic parent core `C_P = g(M_P,U)`, and therefore

`H(C_P | C_{1:m},U) <= H(M_P | C_{1:m},U)`.

The source-facing Lean map deliberately cannot inspect the child-core tuple;
finite alphabets discharge the frozen finite-conditional-entropy requirement.

Canonical theorem: `UEOT.V3.CompositionParentInformation.p_comp_04`.

Promotion evidence:
- feature branch `formal/pcomp04-parent-info`;
- feature head `d7b3446dcac54f62f7d28a141dd8649793b2586c`;
- feature CI `34757571535`: success;
- clean integration branch `formal/pcomp04-main-integration`;
- clean integration/main proof commit `412815d611fc3c20e867fdf245fc15fbf1f9266f`;
- exact integration diff: theorem file plus one top-level import;
- integration CI `34758385777`: success;
- post-main CI `34758642764`: success;
- prohibited-proof audit: clean;
- frozen-source semantic audit: complete.

**Status: PROVED / COUNTED pending this ledger commit's own main CI.**

## Active unresolved front

There are **39 not-yet-counted P-IDs**.

### Active proof — P-KL-03

Frozen source §22.3 requires a finite-horizon path-space KL chain rule for
genuinely history-dependent discrete kernels. The same-initial-law theorem is
green, and the source-explicit different-initial-law extension adds the initial
KL term.

- branch `formal/pkl03-path-chain`;
- same-initial theorem `UEOT.V3.PathKLChain.p_kl_03` was green at
  `ad67c92db2e9bf6fce561e16dcd0c9680072731f`, CI `34758129042`: success;
- latest proof head `6f3e3e3a458da9ef3324783ae0e9423d48a78814` fixes the two exact errors in
  `p_kl_03_general`;
- CI `34761786961`: in progress at ledger creation;
- homogeneous-Markov-only replacement is forbidden;
- feature green does not increment coverage.

### Source audit — P-EVO-02

Frozen target remains the exact shared-label identity for finite `T` independent
of `(F,F')` and copied without error:
`I((F,T);(F',T)) = I(F;F') + H(T)`.
Existing product/KL-chain/deterministic-copy infrastructure must be reused before
adding new foundations.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers or feature-green branches never count
on their own.
