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
| **proved** | **68** |
| **partial** | **0** |
| **pending** | **38** |
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
- **KL / path information:** P-KL-01, P-KL-03
- **Evolution:** P-EVO-01

Count check: `67 + 1 = 68`.

## Newly counted promotion — P-KL-03

Frozen source §22.3 is retained at the required level: finite-horizon path laws
are built from genuinely history-dependent kernels, and KL decomposes into the
initial-law divergence plus the time-summed expected conditional-kernel KL.
The same-initial-law corollary is also exposed explicitly. No homogeneous-Markov
replacement was used.

Canonical theorems:
- `UEOT.V3.PathKLChain.p_kl_03_same_initial`;
- `UEOT.V3.PathKLChain.p_kl_03_general`;
- source-facing alias `UEOT.V3.PathKLChain.p_kl_03`.

Promotion evidence:
- feature branch `formal/pkl03-path-chain`;
- feature proof head `336e67f...` (feature CI green before clean integration);
- clean integration branch `formal/pkl03-main-integration-v3`;
- clean integration commit `d4126fbb3a9d7cd288d261de8898ee103eee85a0`;
- clean integration CI `34762400971`: success;
- rebase promotion PR #57;
- main proof commit `b3e1c152e42b4e2a2b7001776214ecaaa35aae18`;
- post-main CI `34763070439`: success;
- exact integration diff: `UEOT/V3/PathKLChain.lean` plus one top-level import;
- prohibited-proof audit: clean;
- frozen-source semantic audit: complete.

**Status: PROVED / COUNTED pending this ledger commit's own main CI.**

## Active unresolved front

There are **38 not-yet-counted P-IDs**.

### Active proof — P-EVO-02

Frozen source §25.3 requires the exact shared-label identity for finite `T`
independent of `(F,F')` and copied without error:

`I((F,T);(F',T)) = I(F;F') + H(T)`.

The feature implementation encodes independence structurally as a product law
and exact copying through the diagonal copy law; coordinate repacking is a
measurable bijective regrouping only.

- branch `formal/pevo02-shared-label`;
- repaired feature head `9969ed9c4a8fdd11eec26908c0f2b7a0a89b3916`;
- initial CI `34762544028` exposed only Lean/API issues;
- repaired CI `34763101765` is the current feature gate;
- feature green does not increment coverage.

### Source audit — P-KL-02

Frozen source §22.2 requires the sharp event I-projection over **all** path laws
`Q ≪ P0` satisfying `Q(A) ≥ p`, not merely P-KL-01's data-processing lower
bound. The Lean proof must retain:

- `p ≤ q`: infimum `0`, attained by `P0`;
- `p > q`: infimum `d_Bern(p || q)`;
- the explicit two-region reweighted optimizer;
- probability, absolute continuity, exact event mass and exact KL checks;
- the `p = 1` boundary case.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers or feature-green branches never count
on their own.
