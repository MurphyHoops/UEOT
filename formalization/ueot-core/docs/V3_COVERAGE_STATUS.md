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
| **proved, staged by this ledger checkpoint** | **83** |
| **partial** | **0** |
| **pending / not yet counted** | **23** |
| **total** | **106** |

This branch stages **83/106** after P-CTL-01 completed source-semantic, feature,
clean-integration, PR and proof-main gates, including successful resulting-main
CI. **83/106 is not called full-green until this ledger checkpoint itself passes
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
- **Control:** P-CTL-01
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
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01

Count check: `82 + P-CTL-01 = 83`.

## Newly staged promotion — P-CTL-01

Frozen Core 3 P-CTL-01 is the finite discounted control theorem at its full
source scope: finite state space, finite nonempty state-dependent feasible action
sets, bounded reward, and `0 < beta < 1`. The formalization proves the Bellman
optimality operator has a unique fixed point, value iteration from an arbitrary
initial value converges to it, and the Bellman residual yields the declared
stopping/error bound.

The control-optimality endpoint is also source-faithful: a deterministic
stationary greedy policy attains the optimal infinite-horizon discounted value
at every state **against the full class of arbitrary causal policies**, not only
against stationary or Markov policies.

Canonical theorem surface:
- `UEOT.V3.FiniteDiscountedControl.p_ctl_01_causal_optimality`.

Supporting source-facing facts include:
- `UEOT.V3.FiniteDiscountedControl.Model.fixedPoint_unique`;
- `UEOT.V3.FiniteDiscountedControl.Model.valueIteration_tendsto`;
- `UEOT.V3.FiniteDiscountedControl.Model.valueError_le_residual`;
- `UEOT.V3.FiniteDiscountedControl.CausalPolicy.infiniteValue_le_optimal`;
- `UEOT.V3.FiniteDiscountedControl.greedy_infiniteValue_eq_optimal`.

Promotion evidence:
- feature branch: `formal/pcomp01-multiblock-v1`;
- final feature head: `47218ef06c63ed81ab3974d107f0d3d46cc49ecb`;
- feature official root CI `35098260086`: success;
- source-semantic audit: complete;
- prohibited-proof audit: clean (`sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`);
- clean integration branch: `formal/pcomp01-main-integration-v1`;
- clean integration head: `45440746a7086b74bc65ba741611f98a8da92f27`;
- clean integration official root CI `35099296408`: success;
- proof PR #93;
- PR-triggered CI `35102272835`: success;
- proof main commit `3efe7ebc74d8f2a6705c12a5218a7880f5a3688c`;
- proof resulting-main CI `35104140440`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger
checkpoint.**

## Previous full-green checkpoint — 82/106

P-COMP-02 is already counted in the authoritative **82/106 full-green** baseline
at `main@86a2cd21e4693ae084e7bc904d38046f9b3a1519`, whose ledger resulting-main
CI `35083749972` succeeded. P-COMP-02 itself landed at
`main@61135398787bb49e1a19f54903dcb75beea870d4` and its proof resulting-main CI
`35080641545` succeeded.

All previously counted P-IDs remain closed absent a substantive frozen-source
mismatch or CI regression. Source-facing wrapper work must not be double-counted
as new P-IDs. In particular, **P-TEL-01 is already counted and must not be
reopened as a new coverage item.**

## Grounded pending fronts

After this staged promotion, **23** P-IDs remain not yet counted and require
fresh source-first audits. Known non-quick fronts include:

- P-PER-02: Polish-space Feller semigroup + tight occupation laws + Prokhorov/Portmanteau weak-convergence infrastructure;
- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds;
- P-DDH-02/03: finite exponential-family calculus and KL variational duality;
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis;
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations;
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation;
- P-QSD-01/04: source-locked distinct non-A results.

**P-QUO-01 is the next high-leverage source-to-main audit candidate.** Current
main already contains `StructuredQuotient`, finite stable-partition
infrastructure, and now the counted P-CTL-01 Bellman/control foundation. It may
only close if an explicit source-object bridge proves Bellman intertwining,
value pullback `V* = Vbar* o f`, and actionwise-Q/argmax policy lifting at the
frozen controlled quotient object. Generic quotient-law preservation alone is
insufficient. P-QUO-02 remains separate and additionally depends on the frozen
span-sensitive residual/metric contract.

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
