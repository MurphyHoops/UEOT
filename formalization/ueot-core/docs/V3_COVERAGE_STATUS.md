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
| **proved, staged by this ledger checkpoint** | **73** |
| **partial** | **0** |
| **pending / not yet counted** | **33** |
| **total** | **106** |

This branch stages **73/106** after P-REF-01 completed feature,
clean-integration, source-semantic, prohibited-proof and post-main proof gates.
**73/106 is not called full-green until this ledger checkpoint itself passes PR
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
- **Refinement / agency:** P-REF-01, P-REF-04, P-REF-05
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

Count check: `72 + P-REF-01 = 73`.

## Newly staged promotion — P-REF-01

Frozen source §27.1 is implemented at full stated strength:

- reflexive state `Z=(X,S)`;
- arbitrary complete-history-dependent randomized causal policies;
- an initial probability law and measurable controlled Markov kernel determine
  one unique infinite `Z` path law for each fixed causal policy;
- existence is built through pinned Mathlib Ionescu--Tulcea trajectory kernels;
- uniqueness is non-vacuous and follows from equality of all recursively
  generated finite prefixes/projective limits;
- measurable structural modification
  `S_{t+1}=F(S_t,X_t,a_t,xi_t)` is realized as a noise-driven controlled Markov
  kernel without restricting the policy;
- a further compression `phi(Z)` requires a separate action-wise controlled
  strong-lumpability/closure condition; reflexivity does not imply closure.

The source-facing theorem works on arbitrary measurable spaces once the supplied
kernels are Markov. This is stronger than the Core-wide Standard-Borel default,
not a weakening of the frozen P-REF-01 contract.

Canonical theorem surface:
- `UEOT.V3.ReflexivePRef01.p_ref_01`;
- `UEOT.V3.ReflexivePRef01.p_ref_01_structureModification`;
- `UEOT.V3.ReflexivePRef01.p_ref_01_compression_closure_iff_kernel`;
- `UEOT.V3.ReflexivePRef01.p_ref_01_compression_closure_iff_pathLaw`.

Promotion evidence:
- final strengthened feature branch `formal/pref01-source-assembly-v2`;
- final feature head `8649c0763ac2326177812209bab3f32ad92680f7`;
- final feature CI `34803657950`: success;
- complete pre-strengthening assembly CI `34802710747`: success;
- clean integration branch `formal/pref01-main-integration-v1`;
- clean integration head `85148ee2e9cba8afa5e23406a51c09515d45e052`;
- clean integration PR #69;
- clean integration CI `34804007035`: success;
- proof main commit `1c4de9fc60b653e8c3594bba1a01a0eed510578a`;
- proof post-main CI `34804335400`: success;
- prohibited-proof audit: clean;
- frozen-source semantic audit: complete.

**Status: PROVED / COUNTED pending this ledger/recovery checkpoint's own PR and
main CI.**

## Previous full-green checkpoint — 72/106

P-ALG-01 and all earlier counted theorems are fully green. The authoritative
72/106 baseline before P-REF-01 proof promotion was
`main@8d3124b03b6e04cdde8fc5c42d76751967d043c1`, with official main CI
`34795931776` successful. Counted P-IDs are not reopened absent a substantive
source mismatch or CI regression.

## Active proof lanes — P-REF-02 and P-REF-03

### P-REF-02 — finite Bayes belief sufficiency

The active branch `formal/pref02-belief-core-v1` is implementing frozen §27.2.
The already-green first layer provides the finite latent-parameter/state model,
normalized joint beliefs, predictive masses, positive-evidence Bayes posterior,
and explicit `modelConflict` on zero evidence. The current second layer adds a
normalized next-observation law and a complete one-step `BeliefStep` determined
only by `(b,a)`. The bounded-discount belief-control rewrite remains mandatory
before P-REF-02 can be promoted or counted.

### P-REF-03 — free information weak improvement

The parallel branch `formal/pref03-free-information-v1` represents the signal
by an arbitrary sub-sigma-algebra, keeps only the action set finite, and proves
the pointwise conditional-expectation maximum dominates every fixed action.
This preserves the frozen arbitrary-signal-space requirement. Feature work is
uncounted until all promotion gates succeed.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers or feature-green branches never count
on their own.
