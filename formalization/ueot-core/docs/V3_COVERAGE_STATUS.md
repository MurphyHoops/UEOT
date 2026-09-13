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
| **proved** | **69** |
| **partial** | **0** |
| **pending** | **37** |
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
- **Evolution:** P-EVO-01, P-EVO-02

Count check: `68 + 1 = 69`.

## Newly counted promotion — P-EVO-02

Frozen source §25.3 is retained exactly: for a finite label `T` independent of
the joint parent/offspring pair `(F,F')` and copied without error,

`I((F,T);(F',T)) = I(F;F') + H(T)`.

The implementation does not replace independence with pairwise assumptions or
replace exact copying by a noisy channel. Independence is encoded structurally
as `ρ.prod (copyJoint τ)` and `sharedRepack` only regroups coordinates.

Canonical theorem:
- `UEOT.V3.EvolutionSharedLabel.p_evo_02`.

Promotion evidence:
- feature branch `formal/pevo02-shared-label`;
- feature head `bfe0c3f43728a9ae5a07f1729c143039d16d7cff`;
- feature CI `34763489145`: success;
- clean integration head `0a3691ef1d97cae1a8017adae47bd8aa7ea49c47`;
- clean integration PR #59;
- clean integration CI `34765061853`: success;
- main proof commit `17f7ca2070a439a7e4c99622d3c27095431a1571`;
- post-main CI `34765399086`: success;
- exact integration diff: `UEOT/V3/EvolutionSharedLabel.lean` plus one top-level import;
- prohibited-proof audit: clean;
- frozen-source semantic audit: complete.

**Status: PROVED / COUNTED pending this ledger/recovery checkpoint's own main CI.**

## Previously counted promotion — P-KL-03

Frozen source §22.3 remains implemented at full strength: finite-horizon path
laws use genuinely history-dependent kernels, with the initial-law KL term in
the distinct-initial theorem and the same-initial corollary exposed explicitly.

Canonical theorem family:
- `UEOT.V3.PathKLChain.p_kl_03_same_initial`;
- `UEOT.V3.PathKLChain.p_kl_03_general`;
- `UEOT.V3.PathKLChain.p_kl_03`.

Main proof commit `b3e1c152e42b4e2a2b7001776214ecaaa35aae18`, post-main CI
`34763070439`, and 68/106 ledger main CI `34763815124` are all successful.

## Active unresolved front — P-KL-02

Frozen source §22.2 requires the sharp event I-projection over **all** path laws
`Q ≪ P0` with `Q(A) ≥ p`, where `q = P0(A)` and `0 < q < 1`:

- `p ≤ q`: infimum `0`, attained by `P0`;
- `p > q`: infimum exactly `d_Bern(p || q)`;
- explicit RN optimizer
  `(p/q) 1_A + ((1-p)/(1-q)) 1_{Aᶜ}`;
- probability, absolute continuity, exact event mass and exact KL checks;
- the `p = 1` boundary case.

Current lane:
- branch `formal/pkl02-event-iprojection`;
- explicit optimizer implemented via `Measure.withDensity`;
- helper construction/RN layer green at `333a3e9ffa0cadbaaa0b167ec0ccdc7d8685317a`, CI `34765080012`;
- event-mass/probability layer under CI at head `1378efc916e894057cd4cd38cedbfd9c5eac9f80`, run `34765567421`;
- no P-KL-02 coverage change yet.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers or feature-green branches never count
on their own.
