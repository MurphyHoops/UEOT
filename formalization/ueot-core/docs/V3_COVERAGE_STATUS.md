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
- **Control:** P-CTL-01
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
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01

Count check: `82 + P-CTL-01 = 83`.

## Newly staged promotion — P-CTL-01

Frozen Core 3 P-CTL-01 is the finite discounted-control existence and optimality
theorem. The source assumptions are preserved literally at the model level:
finite state space, a finite nonempty admissible action type at every state,
bounded one-stage reward, stochastic transitions, and discount `0 < beta < 1`.

The Lean implementation proves the complete source chain rather than only a
stationary-policy surrogate:

1. the finite Bellman operator is globally `beta`-Lipschitz in the sup metric and therefore a contraction;
2. Banach's theorem supplies the canonical Bellman fixed point `V*`, and any Bellman fixed point equals it;
3. value iteration converges to `V*` from every initial value function;
4. the residual certificate `dist v V* <= dist v (T v) / (1-beta)` is machine checked;
5. an arbitrary causal randomized policy carries an arbitrary time-indexed memory type, so the quantifier can encode the complete observed history rather than only Markov memory;
6. finite-horizon causal values satisfy the Bellman domination inequality with an explicit geometric terminal tail;
7. bounded rewards give a geometric bound on successive finite-horizon values, hence every such causal policy has a well-defined infinite discounted value;
8. passing the finite-horizon domination inequality to the limit gives `J^pi <= V*` for every causal history-dependent randomized policy;
9. a finite Bellman argmax is represented as a stationary deterministic causal policy, its policy-evaluation Bellman map is a contraction, and its infinite value equals `V*` at every state.

Canonical source-facing theorem:
- `UEOT.V3.FiniteDiscountedControl.p_ctl_01_causal_optimality`.

Supporting source-facing facts:
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

P-COMP-02 and all earlier counted P-IDs are already closed in the authoritative
**82/106 full-green** baseline at
`main@86a2cd21e4693ae084e7bc904d38046f9b3a1519`, whose ledger resulting-main CI
`35083749972` succeeded. P-COMP-02 itself landed at
`main@61135398787bb49e1a19f54903dcb75beea870d4` and its proof resulting-main CI
`35080641545` succeeded.

All previously counted P-IDs remain closed absent a substantive frozen-source
mismatch or CI regression. In particular, P-TEL-01 is already counted and must
not be reopened or double-counted merely because older compilation reports
predate its later full promotion.

## Grounded pending fronts

After this staged promotion, **23** P-IDs remain not yet counted and require
fresh source-first audits. Known non-quick fronts include:

- P-CTL-02: compact-metric/Feller discounted control with continuous reward, weakly continuous transition kernel, continuity-preserving Bellman operator and measurable stationary optimal selection;
- P-PER-02: Polish-space Feller semigroup + tight occupation laws + Prokhorov/Portmanteau weak-convergence infrastructure;
- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds;
- P-DDH-02/03: finite exponential-family calculus and KL variational duality;
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis;
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations;
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation;
- P-QSD-01/04: source-locked distinct non-A results.

P-QUO-01 is now a particularly high-leverage source-to-main audit candidate:
the frozen theorem assumes the Chapter 19 Bellman existence/uniqueness layer
just completed by P-CTL-01 and requires a surjective control quotient preserving
same-fiber actions, rewards and every-action pushed-forward transition laws. Its
source proof is Bellman intertwining plus fixed-point uniqueness and argmax
lifting. P-QUO-02 additionally requires the span-sensitive P-MET-02 residual
bound. Generic quotient-law theorems alone remain insufficient.

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
