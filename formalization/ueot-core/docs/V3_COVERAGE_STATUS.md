# UEOT Core v3.0 Lean Coverage Status

This file is the **authoritative source-level P-ID ledger** for the frozen
`UEOT_Core_Mathematics_v3.0_Complete.md` specification.

Operational branch/CI state is tracked in `FORMALIZATION_STATE.md`.
Detailed promotion narratives from the 32-proof checkpoint are preserved
verbatim at `archive/2026-09-10/V3_COVERAGE_STATUS_32_PROVED.md`.

## 1. Source identity and verification contract

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- pinned Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

A P-ID is `proved` only after all of the following gates are satisfied:

1. the Lean declarations semantically match the literal v3.0 source statement;
2. the declarations are reachable from the official `UEOT` / `UEOT.V3` import graph;
3. the feature branch passes the official target against the pinned lock;
4. the integration PR passes the official target;
5. the proof is merged to `main`;
6. post-merge `main` CI passes;
7. this ledger is synchronized.

A green helper theorem, an unimported module, or a green feature branch alone
is not a source-level proof promotion.

## 2. Current source-level coverage

| status | count |
|---|---:|
| **proved** | **34** |
| **partial** | **0** |
| **pending** | **72** |
| **total** | **106** |

There are currently **no partial P-IDs**. Every unresolved source P-ID remains
explicitly pending until it passes the full gate above.

## 3. Proved P-ID set

The 34 source-matched, machine-checked P-IDs are:

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-03, P-STAT-04
- **Quotient:** P-QUO-03
- **Refinement / agency:** P-REF-04, P-REF-05
- **Telescoping reward:** P-TEL-01
- **Bridge:** P-BRG-02
- **Metric:** P-MET-01, P-MET-02
- **Internal/external factorization:** P-INT-02, P-INT-03
- **Information:** P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01
- **QSD:** P-QSD-02
- **Persistence:** P-PER-03
- **Representation covariance:** P-FAC-01

Count check: `4 + 6 + 3 + 4 + 2 + 1 + 2 + 1 + 1 + 2 + 2 + 1 + 1 + 1 + 1 + 1 + 1 = 34`.

## 4. 2026-09-10 promotion — P-FAC-01

P-FAC-01 is promoted from `pending` to `proved`.

The source-facing covariance chain is derived from primitive transported
objects rather than assuming final path/value equality. The integrated Lean
proof covers:

- bimeasurable microscopic coordinate transport of kernels and readouts;
- exact macro pushforward and homogeneous trajectory-law covariance;
- predictive-family factorization/sufficiency covariance;
- controlled strong-lumpability / exact dynamic-closure covariance;
- finite causal feedback path-law naturality derived horizon-by-horizon from
  transported primitive causal kernels;
- transported rewards, policy-by-policy value equality, and equality of the
  optimal supremum.

The key source-safety point is that feedback-policy path-law covariance is a
**derived theorem**, not an independent hypothesis.

Verification evidence:

- final feature head: `8c5e451c10f58fa032af73c66b1bd52f2fee7620`
- branch full-target CI #461: success
- PR #14 full-target CI #460: success
- squash merge: `29bb6b3fb55cde2d7a87577f4d0ff15c14e29aa0`
- post-merge main CI #502 (`34493839447`): success

## 5. 2026-09-10 promotion — P-DYN-02

P-DYN-02 is promoted from `pending` to `proved`.

The integrated proof matches the finite continuous-time Markov-chain source
criterion:

- the block-sum criterion is equivalent to generator intertwining
  `L F = F Lbar`;
- under a surjective partition and fiber-constant block sums, the common values
  define a unique macro matrix;
- if `L` is a CTMC generator, the constructed macro matrix is also a CTMC
  generator;
- generator intertwining propagates to all powers and hence to the matrix
  exponential semigroup;
- the converse uses the **right derivative at `t = 0` on `Ici 0`**, matching
  physical CTMC time `t >= 0` rather than silently assuming negative times;
- derivative uniqueness is performed entrywise in `ℝ`, eliminating a Lean-only
  hidden norm-instance mismatch on rectangular matrix spaces.

The source-facing declarations are centered on:

- `UEOT.V3.CTMCLumpability.generator_intertwines_iff_blockSum`
- `exists_macro_ctmcGenerator_of_blockSum_constant`
- `UEOT.V3.CTMCSemigroup.semigroup_intertwines_of_generator`
- `UEOT.V3.CTMCSemigroupNonnegative.generator_intertwines_of_semigroup_nonneg`
- `p_dyn_02_nonnegative_semigroup_iff_blockSum`
- `exists_macro_ctmc_semigroup_of_blockSum_constant`

Verification evidence:

- clean integration head: `8c0212f4bfbd0e7bf9ed0c445e4662eb02cf04ef`
- clean branch full-target CI #504 (`34495257491`): success
- PR #23 full-target CI #505 (`34497593139`): success
- squash merge: `8ac668253c4d8bc62ab22f250701bc0a190b6049`
- post-merge main CI #506 (`34497930427`): success

The earlier diverged development PR #22 is retained as audit history but was
not used for integration; its verified proof content was transplanted onto the
clean branch directly from current `main`.

## 6. Prior promotion evidence

The full theorem-by-theorem narratives and CI evidence for the previous
32-proof checkpoint are preserved in:

`docs/archive/2026-09-10/V3_COVERAGE_STATUS_32_PROVED.md`

That archived checkpoint includes the evidence for P-PER-03, P-QSD-02,
P-DYN-03, P-DYN-04, P-PRED-03, P-PROC-01, P-INFO-05, P-REC-01, P-INT-02,
P-INT-03, P-DYN-01, P-MET-01/02, P-REF-05, P-TEL-01, P-BRG-02,
P-PRED-01/02, P-RES-01/02/05/06, P-CAR-04, and the recovered baseline.

No previously proved P-ID is removed or downgraded by this ledger compaction.

## 7. Active unresolved front

The highest-priority pending lanes after this checkpoint are:

- **P-INFO-01**: close the finite/discrete `copy KL = Shannon entropy` bridge,
  then combine it with the already machine-checked statistic data processing
  and chain identity;
- **P-REC-02**: instantiate the continuous stochastic recovery certificate from
  the literal Dynkin/localization/absolute-continuity hypotheses;
- **P-PER-01**: resolve the reverse-inclusion issue for omega-limit strong
  invariance under a one-sided semiflow without silently strengthening the
  source to a two-sided flow.

Additional pending P-IDs are refilled only after near-closure lanes are not left
half-integrated.

## 8. Completion rule

The v3.0 formalization is complete only when **all 106 source P-IDs** have been
semantically matched and machine-checked under the frozen source. A green
repository build proves only the declarations currently imported; it does not
by itself prove full manuscript coverage.
