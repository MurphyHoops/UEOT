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
- canonical source object: available in the project File Library for semantic audit
- exact canonical source bytes in public repo: **pending synchronization**

A P-ID is counted as `proved` only after semantic matching against the canonical
frozen source object, official import reachability, relevant feature/clean/PR
CI gates, main integration, green post-main CI, prohibited-proof/axiom audit,
and ledger synchronization.

**Public source-artifact reproducibility is tracked separately.** Absence of the
exact canonical Markdown bytes from the public repository does not invalidate a
source-theorem proof that has already been audited against the canonical source
object and integrated with green post-main CI. However, the repository must not
claim that the canonical SHA was independently recomputed until those raw bytes
are actually present and hashed. No regenerated substitute is accepted.

The detailed evidence for the 2026-09-13 P-INFO-02/P-INFO-04 semantic audit is
`docs/SOURCE_AUDIT_EVIDENCE_2026-09-13.md`.

## Current source-level coverage

| status | count |
|---|---:|
| **proved** | **52** |
| **partial** | **0** |
| **pending** | **54** |
| **total** | **106** |

There are no partial P-IDs. `pending` means only “not yet counted proved”; it
does not imply that no mathematical or Lean proof exists on a feature branch.

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
- **Information:** P-INFO-01, P-INFO-02, P-INFO-04, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02
- **QSD:** P-QSD-02
- **Persistence:** P-PER-01, P-PER-03
- **Transport / identity:** P-ID-01
- **Representation covariance:** P-FAC-01

Count check: `4 + 6 + 3 + 4 + 9 + 5 + 1 + 2 + 1 + 1 + 2 + 2 + 1 + 4 + 1 + 2 + 1 + 2 + 1 + 1 = 52`.

## Newly counted source promotions — P-INFO-02 and P-INFO-04

### P-INFO-02 — predictive TV bound

Frozen source contract:

`E TV(P(Y|H), P(Y|M,U)) <= sqrt(I(H;Y|M,U)/2)`

for standard Borel `H,Y,M,U` with `M,U` measurable history statistics.

Canonical theorem:
`UEOT.V3.InformationPInfo02.p_info_02_ennreal`.

Verification evidence:

- exact source semantics re-audited against the canonical source object on
  2026-09-13;
- all-cases PR #46;
- main commit `c1d0d94b7d01a5d6f370d2de4f40e8c1674bcd8f`;
- post-main CI `34692828935`: success.

The theorem has no finite-information source assumption; `I=top` is handled
explicitly. `[Nonempty Y]` is a Mathlib disintegration/elaboration condition
implied by existence of the source probability law.

**Status: PROVED / COUNTED.**

### P-INFO-04 — both frozen clauses

**Multiway sharp Fano**

- canonical theorem: `UEOT.V3.InformationPInfo04.p_info_04`;
- source semantics re-audited on 2026-09-13;
- PR #47;
- main commit `94e16dfb9cc9a2db6e000d8f5394c1b07869ce40`;
- post-main CI `34693509298`: success.

**Conditional binary identity-information lower bound**

- canonical theorem:
  `UEOT.V3.InformationConditionalBinaryMutualEntropy.p_info_04_conditional_binary`;
- finite KL/entropy bridge:
  `UEOT.V3.InformationConditionalBinaryMutualEntropy.conditionalBinaryMutualInfo_eq_ofReal_entropyForm_of_ne_top`;
- source semantics re-audited on 2026-09-13;
- full compose CI `34705230951`: success;
- clean commit `8c76777e78e8d7f73b0d71397f8c81aeaa6e9c54`;
- clean CI `34705560077`: success;
- PR #51 CI `34706303512`: success;
- integrated main commit `e19eee7082418f1826650316b533c0380a9a451f`;
- post-main CI `34706528781`: success.

The binary proof handles reference-probability boundary cases, uses the actual
measurable decoder rather than a MAP substitution, and treats `CMI=top`
separately, so the frozen source theorem does not acquire a finite-CMI
assumption.

**Status: PROVED / COUNTED.**

For both P-INFO-02 and P-INFO-04, `public_source_artifact_synced = false` remains
a separate reproducibility flag. The canonical SHA has not been recomputed from
local raw bytes in the current audit session.

## Active unresolved front

- **P-INFO-03 — ACTIVE PROOF:** prove genuine countable-discrete `H(C|U)` by
  disintegration, random-encoder joint-law semantics, zero-distortion
  recoverability, conditional DPI, and attainability. The first countable
  conditional-entropy module has already passed official full-target CI
  `34706765170`.
- **P-INT-01 — BLOCKED:** reuse the general conditional-information interface
  produced by P-INFO-03; do not build a duplicate stack.
- **Public canonical source synchronization — REPRODUCIBILITY TASK:** copy the
  exact canonical bytes into the public repository and independently recompute
  SHA-256. This task no longer changes the proof count by itself.

The machine-readable live details are in `docs/PID_STATUS.yaml`.

## Completion rule

UEOT Core v3.0 formalization is complete only when all **106** source P-IDs pass
the source-theorem proof contract, with no theorem counted from a helper or
feature-green branch alone. Full project reproducibility additionally requires
the exact canonical source artifact to be present in the public repository and
the frozen SHA-256 to be independently reproducible there.
