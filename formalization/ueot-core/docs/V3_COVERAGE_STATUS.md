# UEOT Core v3.0 Lean Coverage Status

This file is the **authoritative source-level P-ID ledger** for the frozen
`UEOT_Core_Mathematics_v3.0_Complete.md` specification.

Operational branch/CI state is tracked in `FORMALIZATION_STATE.md`. Detailed
promotion narratives from the 32-proof checkpoint are preserved verbatim at
`archive/2026-09-10/V3_COVERAGE_STATUS_32_PROVED.md`; later history is also
preserved by Git.

## 1. Source identity and verification contract

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- pinned Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

A P-ID is `proved` only after all of the following gates are satisfied:

1. Lean declarations semantically match the literal frozen v3.0 source statement;
2. declarations are reachable from the official `UEOT` / `UEOT.V3` import graph;
3. feature-branch official-target CI passes against the pinned lock;
4. integration PR official-target CI passes;
5. the proof is merged to `main`;
6. post-merge `main` CI passes;
7. this ledger is synchronized.

A green helper theorem, an unimported module, or a green feature branch alone
is not a source-level proof promotion.

## 2. Current source-level coverage

| status | count |
|---|---:|
| **proved** | **40** |
| **partial** | **0** |
| **pending** | **66** |
| **total** | **106** |

There are currently **no partial P-IDs**. Every unresolved source P-ID remains
explicitly pending until it passes the full gate above.

## 3. Proved P-ID set

The 40 source-matched, machine-checked P-IDs are:

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-02, P-STAT-03, P-STAT-04, P-STAT-05
- **Quotient:** P-QUO-03
- **Refinement / agency:** P-REF-04, P-REF-05
- **Telescoping reward:** P-TEL-01
- **Bridge:** P-BRG-02
- **Metric:** P-MET-01, P-MET-02
- **Internal/external factorization:** P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02
- **QSD:** P-QSD-02
- **Persistence:** P-PER-01, P-PER-03
- **Transport / identity:** P-ID-01
- **Representation covariance:** P-FAC-01

Count check: `4 + 6 + 3 + 4 + 4 + 1 + 2 + 1 + 1 + 2 + 2 + 1 + 2 + 1 + 2 + 1 + 2 + 1 + 1 = 40`.

## 4. 2026-09-11 promotion — P-STAT-05

P-STAT-05 is promoted from `pending` to `proved`.

The frozen source defines the finite-history response distance

`d(h,h') = max_i D_TV(p_{h,i}, p_{h',i})`

and states that if distinct true predictive classes are separated by at least
`gamma > 0`, every response law is estimated within TV error `eta`, and
`2*eta < gamma/2`, then empirical threshold `gamma/2` recovers exactly the true
predictive equivalence classes.

The integrated Lean development defines the protocol-distance supremum, proves
its perturbation by at most `2*eta`, proves true-equivalent histories have zero
true distance, and derives the exact threshold equivalence. It does not use
single-linkage transitive closure or an uncontrolled nearest-neighbour step.

Verification evidence:

- final feature head: `259b69ece2be22ead8e22b04c02fcf0bd9170da8`
- branch full-target CI #580 (`34544593542`): success
- PR #29 full-target CI #583 (`34544873693`): success
- squash merge: `5e5071820a5e30554b23f8344b3315841b0e4b6a`
- post-merge main CI #584 (`34545279143`): success
- integrated module: `UEOT/V3/PredictiveClassRecovery.lean`

## 5. Recent promotion evidence since the archived 32-proof checkpoint

| P-ID | squash merge | post-merge main CI |
|---|---|---|
| P-FAC-01 | `29bb6b3fb55cde2d7a87577f4d0ff15c14e29aa0` | #502 success |
| P-DYN-02 | `8ac668253c4d8bc62ab22f250701bc0a190b6049` | #506 success |
| P-REC-02 | `189fa6b476b0199b321c8d8c2b521f744c0b64ef` | #519 success |
| P-PER-01 | `3d3ecb46416ea156e06fffd70684937f8d94caf3` | #540 success |
| P-ID-01 | `72b0703270df84d5a92f90d5e01c034777ff37dc` | #547 success |
| P-STAT-02 | `5886c7baa4d9b4936e21dbd5639d7c893af22053` | #563 success |
| P-INFO-01 | `0dd65bc8ae40fdd1afbfdf0cf61c155585a5a2ac` | #572 success |
| P-STAT-05 | `5e5071820a5e30554b23f8344b3315841b0e4b6a` | #584 success |

The full theorem-by-theorem narratives and CI evidence for the earlier
32-proof checkpoint remain in
`docs/archive/2026-09-10/V3_COVERAGE_STATUS_32_PROVED.md`. No previously proved
P-ID is removed or downgraded by this ledger compaction.

## 6. Active unresolved front — P-STAT-01

The highest-priority pending lane is **P-STAT-01**, the exact finite-alphabet
simultaneous TV concentration theorem. For `L` fixed conditional responses on a
finite response alphabet of size `K`, with `N` independent samples per response,
the frozen source states

`P(max_j D_TV(p_j,pHat_j) > eta) <= L * 2^(K+1) * exp(-2*N*eta^2)`.

The source proof is the finite-event argument: each subset mass is a Bernoulli
average; two-sided Hoeffding gives `2*exp(-2*N*eta^2)`; union over at most `2^K`
subsets and then `L` response cells. The source also states the clipped radius

`min 1 (sqrt (((K+1)*log 2 + log(L/alpha))/(2*N)))`.

The deterministic `2^K`/`L` union layer has already compiled on its development
branch. The sampling/Hoeffding layer remains under active CI and is **not**
counted as proved. Once the simultaneous response event is established it must
feed directly into P-STAT-02, with no extra union bound over carrier candidates.

## 7. Completion rule

The v3.0 formalization is complete only when **all 106 source P-IDs** have been
semantically matched and machine-checked under the frozen source. A green
repository build proves only the declarations currently imported; it does not
by itself prove full manuscript coverage.
