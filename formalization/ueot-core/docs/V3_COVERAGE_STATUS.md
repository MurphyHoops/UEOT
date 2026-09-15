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
audit, safe main integration, and ledger synchronization. Feature-green or
proof-main work alone never changes the full-green count.

## Current source-level coverage

| status | count |
|---|---:|
| **proved, staged by this ledger checkpoint** | **80** |
| **partial** | **0** |
| **pending / not yet counted** | **26** |
| **total** | **106** |

This branch stages **80/106** after P-REC-03 completed source-semantic, feature,
clean-integration, PR and proof-main gates, including successful resulting-main
CI. **80/106 is not called full-green until this ledger checkpoint itself passes
branch CI, PR CI, lands on `main`, and the resulting main CI succeeds.**

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
- **Refinement / agency:** P-REF-01, P-REF-02, P-REF-03, P-REF-04, P-REF-05
- **Telescoping reward:** P-TEL-01
- **Bridge:** P-BRG-01, P-BRG-02
- **Metric:** P-MET-01, P-MET-02
- **Internal/external factorization:** P-INT-01, P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-02, P-INFO-03, P-INFO-04, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02, P-REC-03, P-REC-04
- **QSD:** P-QSD-02, P-QSD-03
- **Persistence:** P-PER-01, P-PER-03, P-PER-04
- **Transport / identity:** P-ID-01, P-ID-02
- **Representation covariance:** P-FAC-01
- **Omega / integrity:** P-OMG-01, P-OMG-02
- **Dual-drive / alignment:** P-DDH-01, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01

Count check: `79 + P-REC-03 = 80`.

## Newly staged promotion — P-REC-03

Frozen Core 3 P-REC-03 defines the first-hitting-time potential
`V_A(x)=E_x τ_A` for a homogeneous discrete-time Markov kernel and requires,
for `x ∉ A` with finite `V_A(x)`, the Poisson equation
`P V_A(x)-V_A(x)=-1`.

The Lean implementation preserves the source mechanism. `RecoveryHittingFirstStep`
proves the pathwise first-step recursion and measurability; `RecoveryHittingInitial`
proves the initial-law mixture bridge; `RecoveryHittingRestart` derives the
homogeneous path-shift restart law from the Ionescu–Tulcea construction; and
`RecoveryHittingPoisson` assembles the ENNReal first-step identity, finiteness
bridge and source-facing real equation. It neither specializes to a finite state
space nor assumes the Markov restart/Poisson identity as an extra axiom.

Canonical theorem surface:
- `UEOT.V3.RecoveryHittingPoisson.p_rec_03`.

Promotion evidence:
- feature branch: `formal/prec03-first-step-v1`;
- final feature head: `1e01c64824f2e3441b8492cc1f8731895eed467f`;
- feature official root CI `34985193231`: success;
- source-semantic audit: complete against frozen Core 3 P-REC-03;
- prohibited-proof audit: clean (`sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`);
- clean integration branch: `formal/prec03-main-integration-v1`;
- clean integration head: `5142964d87fe53be7b0598d428c49991f50c837f`;
- clean integration CI `34985962098`: success;
- proof PR #87;
- PR-triggered CI `34986723827`: success;
- proof main commit `b337cb8a15e0996f6c285bd073773832fb21500e`;
- proof resulting-main CI `34987526584`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger/recovery
checkpoint.**

## Previous promotion — P-REC-04

P-REC-04 is already counted in the authoritative **79/106 full-green** baseline.
It proves the source-strength Markov drift-to-hitting-time bound
`E_x τ_A <= V(x)/c` through survival-tail telescoping and monotone convergence.

Canonical theorem surface:
- `UEOT.V3.RecoveryHittingBound.p_rec_04_hitting_time_bound`.

Completed evidence:
- feature `formal/prec04-drift-hitting-time-v1@3ea9086976ac595eb034a125390d69264e12772e`, CI `34875538212` success;
- clean integration `formal/prec04-main-integration-v1@50ac5834ff74fe4aa5229b60be87a256e762c778`, CI `34877803577` success;
- proof PR #85 CI `34880820942` success;
- proof main `4946a4435d3c15efbf0ca13aed7b44e65defc79c`, resulting-main CI `34882613059` success;
- ledger main `a7d1804ea8149230526b8e8473389997f2469ede`, ledger resulting-main CI `34886982624` success.

## Recovery group status

At this staged checkpoint the complete Recovery set is present at source-facing
proof strength: **P-REC-01, P-REC-02, P-REC-03, P-REC-04**. P-REC-01 and
P-REC-02 were already counted before this cycle; P-REC-04 is in the 79/106
baseline; P-REC-03 is the only new P-ID staged here.

## Previous full-green checkpoint — 79/106

The authoritative full-green baseline before this P-REC-03 promotion is
`main@a7d1804ea8149230526b8e8473389997f2469ede`, with ledger resulting-main CI
`34886982624` success. All 79 counted P-IDs at that checkpoint remain closed
absent a substantive frozen-source mismatch or CI regression. P-REC-03 proof
code subsequently landed at `main@b337cb8a15e0996f6c285bd073773832fb21500e`
and passed resulting-main CI `34987526584`; that proof-main commit does not by
itself increment the ledger.

P-REF-04 and P-REF-05 were already members of the earlier counted baseline.
Source-facing wrapper branches audited during prior cycles are interface
hardening only and must **not** be double-counted as new P-IDs.

## Grounded pending fronts

After this staged promotion, 26 P-IDs remain not yet counted and require fresh
source-first audits. Known non-quick fronts include:

- P-PER-02: Polish-space Feller semigroup + tight occupation laws + Prokhorov/Portmanteau weak-convergence infrastructure;
- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds;
- P-DDH-02/03: finite exponential-family calculus and KL variational duality;
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis;
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations;
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation;
- P-QSD-01/04: source-locked distinct non-A results.

P-COMP-01 is the provisional next medium lane after this ledger closes. Its
frozen contract requires arbitrary finite nontrivial partitions and a genuine
equivalence between conditional KL zero and the corresponding multi-block
conditional product law. Existing binary conditional-mutual-information
wrappers do not by themselves discharge that source theorem.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron-Frobenius asymptotic package; an assumed-convergence surrogate is not
countable.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers, feature-green branches, source
audits or proof-main commits never count on their own.
