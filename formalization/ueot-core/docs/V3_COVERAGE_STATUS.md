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
| **proved, staged by this ledger checkpoint** | **71** |
| **partial** | **0** |
| **pending / not yet counted** | **35** |
| **total** | **106** |

This branch stages 71/106 after P-API-01 completed its feature, clean-integration,
and post-main proof gates. **71/106 is not called full-green until this ledger
checkpoint itself passes PR CI, lands on `main`, and the resulting main CI
succeeds.**

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

Count check: `70 + 1 = 71`.

## Newly staged promotion — P-API-01

Frozen source §28.3 is implemented at full strength:

- a typed process interface carries the contravariant protocol lift and the
  covariant measurable path readout;
- exact naturality is required for every declared protocol;
- exact interfaces compose with
  `J_AC = J_AB ∘ J_BC` and `C_AC = C_BC ∘ C_AB`;
- approximate TV defects compose with the source bound
  `TV ≤ min 1 (ε_AB + ε_BC)`;
- control actions, policy lifts, rewards and constraints from frozen §28.4 are
  deliberately not smuggled into the §28.3 process-interface contract.

Canonical theorems:
- `UEOT.V3.ProcessInterface.p_api_01_exact`;
- `UEOT.V3.ProcessInterface.p_api_01_approx`.

Promotion evidence:
- feature branch `formal/papi01-process-interface-fresh`;
- feature head `0f76d04a4dcc34b2d2aaa806d5803e4823561bbc`;
- feature CI `34769177051`: success;
- clean integration branch `formal/papi01-clean-int-70`;
- clean integration head `697df634e502bbd5407fc7f832963ac0afe1203d`;
- clean integration PR #64;
- clean integration CI `34770423058`: success;
- proof main commit `f72e2a7448c88b8c90dbf5856522f71a588886ce`;
- proof post-main CI `34770728978`: success;
- exact clean-integration diff: `UEOT/V3/ProcessInterface.lean` plus one
  top-level import;
- prohibited-proof audit: clean;
- frozen-source semantic audit: complete.

**Status: PROVED / COUNTED pending this ledger/recovery checkpoint's own PR and
main CI.**

## Previous full-green checkpoint — P-KL-02 / 70 of 106

P-KL-02 is fully counted. Its all-feasible-law event I-projection theorem,
explicit two-region RN optimizer, exact Bernoulli KL value and `p=1` endpoint
are on main. Feature CI `34768634473`, clean-integration CI `34769135038`, proof
post-main CI `34769394882`, ledger PR CI `34769830990`, and ledger main CI
`34770086580` all succeeded. The resulting full-green 70/106 baseline was
`main@8f29d29a0fe32bf9cccb7cbc12c84676768d9592`.

## Active proof lane — P-ALG-01

Frozen §28.5 is source-locked as an exact finite partition-refinement theorem.
The active feature branch `formal/palg01-refinement-core` implements a finite
controlled Markov model, the exact output/complete-reward initial partition,
block transition masses and exact one-round signature refinement. The intended
termination proof uses a strictly decreasing finite related-pair measure; the
coarsestness proof uses the frozen argument that every coarser current block is
a disjoint union of stable finer blocks. Pinned Mathlib's
`Finpartition.ofSetoid` is being used for that finite disjoint-union bridge.

P-ALG-01 remains **not counted** until it also proves finite termination,
terminal stability, coarsestness among stable refinements, one-step quotient-law
preservation, and all corresponding finite-horizon output laws, then completes
the full promotion protocol. Exact equality is mandatory; floating-tolerance
clustering is not a substitute.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers or feature-green branches never count
on their own.
