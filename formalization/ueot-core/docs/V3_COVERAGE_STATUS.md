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
| **proved, staged by this ledger checkpoint** | **72** |
| **partial** | **0** |
| **pending / not yet counted** | **34** |
| **total** | **106** |

This branch stages **72/106** after P-ALG-01 completed its feature,
clean-integration, source-semantic, prohibited-proof and post-main proof gates.
**72/106 is not called full-green until this ledger checkpoint itself passes PR
CI, lands on `main`, and the resulting main CI succeeds.**

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
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01

Count check: `71 + P-ALG-01 = 72`.

## Newly staged promotion — P-ALG-01

Frozen source §28.5 is implemented at full stated strength:

- finite state set and common finite action set;
- known exact transition matrices, rewards and output labels;
- initial partition by equal output plus the complete action-reward vector;
- exact refinement by current block plus every-action transition mass to every
  current block;
- finite termination through a strictly decreasing finite relation-pair
  measure;
- terminal controlled stability/lumpability;
- coarsest stable refinement of the initial partition;
- quotient preservation of output, reward, every-action one-step block laws and
  stochastic normalization;
- all corresponding finite-horizon output-word laws by recursion.

The implementation keeps the source boundary explicit: this is the exact stable
quotient on the specified finite Markov state domain. It is not unconditionally
identified with a full-history FFIPS object, does not inject §28.4 constraint
data, and does not replace exact equality by floating tolerance.

Canonical theorem:
- `UEOT.V3.PAlg01.p_alg_01`.

Promotion evidence:
- layered branch `formal/palg01-layered@e28c9dbb4882b936889a9aedf5ec42796eed7c86`;
- layered CI `34776635531`: success;
- quotient branch `formal/palg01-quotient-law@4f5390e4eac897bae9930ebf58149971d040b851`;
- quotient CI `34774150913`: success;
- clean integration branch `formal/palg01-main-integration-v1`;
- clean integration head `cd0a36f2663adb1ac17fc30776d6a48e3e8dbb52`;
- clean integration PR #66;
- clean integration CI `34777304473`: success;
- proof main commit `9c638eee8448059221232fa764a2f3ebf00d46bd`;
- post-main CI `34777649215`: success;
- prohibited-proof audit: clean;
- frozen-source semantic audit: complete.

**Status: PROVED / COUNTED pending this ledger/recovery checkpoint's own PR and
main CI.**

## Previous full-green checkpoint — 71/106

P-API-01 and all earlier counted theorems — including P-BRG-02 — are fully
green. The full-green 71/106 baseline before P-ALG-01 proof promotion was
`main@5218e615d852c1ffee72107f35435ee378709166` with ledger/main CI
`34771573465` successful. Counted P-IDs are not reopened absent a substantive
source mismatch or CI regression.

During this recovery, a redundant P-BRG-02 feature branch was briefly opened
before the old 71 ledger list was rechecked. It is **not part of the promotion
plan and must not be merged or counted again**.

## Current source-audit lane — P-REF-01

P-REF-01 requires arbitrary causal policies and uniqueness of the augmented
state path law from the initial law and measurable controlled kernel. The pinned
Mathlib contains Ionescu--Tulcea `traj`/`trajMeasure`, so this lane should reuse
that foundation rather than introduce an axiom or weaken to deterministic or
Markov-only policies. Deterministic structural modification is a special case,
not the general theorem.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers or feature-green branches never count
on their own.
