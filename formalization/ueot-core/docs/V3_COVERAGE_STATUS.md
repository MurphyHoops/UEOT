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
| **proved, staged by this ledger checkpoint** | **81** |
| **partial** | **0** |
| **pending / not yet counted** | **25** |
| **total** | **106** |

This branch stages **81/106** after P-COMP-01 completed source-semantic, feature,
clean-integration, PR and proof-main gates, including successful resulting-main
CI. **81/106 is not called full-green until this ledger checkpoint itself passes
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
- **Composition:** P-COMP-01, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01

Count check: `80 + P-COMP-01 = 81`.

## Newly staged promotion — P-COMP-01

Frozen Core 3 P-COMP-01 uses one common conditional joint path law for all
finite nontrivial partitions and defines

`I_π = E_U D_KL(P_{X_{1:m}|U} || ⊗_{B∈π} P_{X_B|U})`.

The source-facing Lean theorem starts from a single joint probability law
`ρ : Measure (U × (∀ i, X i))`, uses Mathlib's canonical `ρ.condKernel`, and
records the explicit disintegration bridge `ρ.fst ⊗ₘ ρ.condKernel = ρ`.
Actual finite set partitions reblock the same child-coordinate path law; the
reblocking and inverse are constructed in Lean. The block-product kernel is
built from the conditional block marginals of that same common kernel. The
implementation proves `I_π = 0` iff the corresponding blocks are conditionally
independent given `U`, and proves that the exact minimum over the complete
finite family of all nontrivial partitions is positive iff no such partition
factorizes.

This closes the historical semantic defect in the rejected exploratory design:
different partitions do **not** receive unrelated conditional kernels.
Standard-Borel/nonempty assumptions are used only for the regular conditional
probability/disintegration bridge required by the source-facing joint-law form.

Canonical theorem surface:
- `UEOT.V3.CompositionPathSource.p_comp_01`.

Promotion evidence:
- feature branch: `formal/pcomp01-multiblock-v1`;
- final feature head: `70a9dc7a26e0f80ed03633efda00a48927a80e5e`;
- feature official root CI `35011604866`: success;
- source-semantic + historical-conversation audit: complete;
- prohibited-proof audit on the proof PR diff: clean (`sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`);
- clean integration branch: `formal/pcomp01-main-integration-v1`;
- clean integration head: `5f0e0b0ba56c1f97024ac8568275e1bc9db257a4`;
- clean integration official root CI `35014183716`: success;
- proof PR #89;
- PR-triggered CI `35014787206`: success;
- proof main commit `c5ae119adad2e533205f58e9b95d8ffc5d6713df`;
- proof resulting-main CI `35015386126`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger/recovery
checkpoint.**

## Previous promotion — P-REC-03

P-REC-03 is already counted in the authoritative **80/106 full-green** baseline.
It proves the source-strength first-hitting-potential Poisson equation
`P V_A(x)-V_A(x)=-1` outside `A` under the source finiteness hypothesis.

Canonical theorem surface:
- `UEOT.V3.RecoveryHittingPoisson.p_rec_03`.

Completed evidence:
- feature `formal/prec03-first-step-v1@1e01c64824f2e3441b8492cc1f8731895eed467f`, CI `34985193231` success;
- clean integration `formal/prec03-main-integration-v1@5142964d87fe53be7b0598d428c49991f50c837f`, CI `34985962098` success;
- proof PR #87 CI `34986723827` success;
- proof main `b337cb8a15e0996f6c285bd073773832fb21500e`, resulting-main CI `34987526584` success;
- ledger main `e8749f66cf88817ae7df7703c6c55b1fc9c2cdd1`, ledger resulting-main CI `34991002841` success.

## Previous full-green checkpoint — 80/106

The authoritative full-green baseline before this P-COMP-01 promotion is
`main@e8749f66cf88817ae7df7703c6c55b1fc9c2cdd1`, with ledger resulting-main CI
`34991002841` success. All 80 counted P-IDs at that checkpoint remain closed
absent a substantive frozen-source mismatch or CI regression. P-COMP-01 proof
code subsequently landed at `main@c5ae119adad2e533205f58e9b95d8ffc5d6713df`
and passed resulting-main CI `35015386126`; that proof-main commit does not by
itself increment the ledger.

P-REF-04 and P-REF-05 were already members of the earlier counted baseline.
Source-facing wrapper branches audited during prior cycles are interface
hardening only and must **not** be double-counted as new P-IDs.

## Grounded pending fronts

After this staged promotion, 25 P-IDs remain not yet counted and require fresh
source-first audits. Known non-quick fronts include:

- P-PER-02: Polish-space Feller semigroup + tight occupation laws + Prokhorov/Portmanteau weak-convergence infrastructure;
- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds;
- P-DDH-02/03: finite exponential-family calculus and KL variational duality;
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis;
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations;
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation;
- P-QSD-01/04: source-locked distinct non-A results.

P-COMP-02 is the natural next Composition-family source-first audit candidate,
but it must be independently matched to the frozen source rather than treated
as a corollary of P-COMP-01 without an explicit source bridge.

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
