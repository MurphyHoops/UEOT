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
| **proved** | **66** |
| **partial** | **0** |
| **pending** | **40** |
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
- **Composition:** P-COMP-03, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01
- **Evolution:** P-EVO-01

Count check: `64 + 2 = 66`.

## Newly counted promotions — P-ALI-02 and P-COMP-07

### P-ALI-02 — child updates and parent value

Frozen contract retained as a finite **heterogeneous** real Hilbert direct sum
`H = ⊕ᵢ Hᵢ`.  Parent and child objectives carry actual `HasGradientAt`
certificates; the update is an actual `HasDerivAt` trajectory.  The parent
value derivative is produced by the chain rule, then expanded componentwise and
bounded by Cauchy--Schwarz.  No scalar derivative identity is assumed.

Canonical theorem: `UEOT.V3.AlignmentParentValue.p_ali_02`.

### P-COMP-07 — compact composition window

Frozen contract retained exactly: compact coupling interval, continuous
nondecreasing integration diagnostic, continuous nonincreasing fidelity,
nonempty threshold-feasible sets, attained threshold boundaries derived from
compactness/closedness, and a joint feasible set equal to the closed interval
between the boundaries when ordered and empty otherwise.  No boundary witness
is added as an assumption.

Canonical theorem: `UEOT.V3.CompositionWindow.p_comp_07`.

Joint promotion evidence:
- P-ALI-02 feature `formal/pali02-parent-value@3c882f0801b3e6b00ebd86dc13da0f5b5d7c38b8`;
- P-ALI-02 feature CI `34756782788`: success;
- P-COMP-07 feature `formal/pcomp07-composition-window@76401f58d3877e8326e8417b7e56c9b4bf79b12b`;
- P-COMP-07 feature CI `34756769679`: success;
- clean integration branch `formal/ali02-comp07-main-integration`;
- clean integration/main proof commit `5f9a36d25c5e35fafe5379a5a2ff47b14e77cce8`;
- exact integration diff: two theorem files plus two top-level imports;
- integration CI `34757135510`: success;
- safe non-force main fast-forward;
- post-main CI `34757507969`: success;
- prohibited-proof audit: `sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`;
- frozen-source semantic audit: complete.

**Status: PROVED / COUNTED pending this ledger commit's own main CI.**

## Active unresolved front

There are **40 not-yet-counted P-IDs**.

### Integration-ready — P-COMP-04

- branch `formal/pcomp04-parent-info`;
- head `d7b3446dcac54f62f7d28a141dd8649793b2586c`;
- theorem `UEOT.V3.CompositionParentInformation.p_comp_04`;
- feature CI `34757571535`: success;
- exact source shape retained: with side information packaging `(C_{1:m},U)`, the canonical parent map is constrained to `C_P = g(M_P,U)` and cannot inspect the child-core tuple;
- proof is fiberwise deterministic-statistic entropy monotonicity over the true conditional kernel;
- feature green does **not** increment coverage; next gate is clean integration onto the latest full-green main.

### Active proof — P-KL-03

- branch `formal/pkl03-path-chain`;
- head `e4a242c18a7448fd0352f8284b36a0d608094a8b`;
- theorem candidate `UEOT.V3.PathKLChain.p_kl_03`;
- CI `34757721974`: in progress at ledger creation;
- theorem remains finite-horizon and genuinely history-dependent; a homogeneous-Markov surrogate is forbidden.

### Source audit — P-EVO-02

Frozen target remains the exact shared-label identity for finite `T` independent
of `(F,F')` and copied without error:
`I((F,T);(F',T)) = I(F;F') + H(T)`.  Existing KL chain/product and deterministic
copy infrastructure must be reused before adding new foundations.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers or feature-green branches never count
on their own.
