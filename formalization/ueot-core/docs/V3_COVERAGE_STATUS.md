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
| **proved, staged by this ledger checkpoint** | **79** |
| **partial** | **0** |
| **pending / not yet counted** | **27** |
| **total** | **106** |

This branch stages **79/106** after P-REC-04 completed source-semantic, feature,
clean-integration, PR and proof-main gates, including successful resulting-main
CI. **79/106 is not called full-green until this ledger checkpoint itself passes
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
- **Recovery:** P-REC-01, P-REC-02, P-REC-04
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

Count check: `78 + P-REC-04 = 79`.

## Newly staged promotion — P-REC-04

Frozen Core 3 P-REC-04 is the discrete-time Markov recovery theorem. For a
measurable target set `A`, a nonnegative finite-valued Lyapunov potential `V`,
and a strictly positive drift constant `c`, the drift inequality outside `A`
is equivalently `PV + c <= V`; the conclusion is `E_x tau_A <= V(x)/c`.

The Lean implementation preserves the source mechanism. It derives the
homogeneous Markov trajectory from the state kernel, builds the nonnegative
hitting-time tail model in `ENNReal`, proves the one-step survival-potential
drift, telescopes every finite horizon, and passes to the full expectation by
monotone convergence. It does not assume the stopped inequality, specialize to
a finite state space, or add a global future-integrability premise.

Canonical theorem surface:
- `UEOT.V3.RecoveryHittingBound.p_rec_04_hitting_time_bound`.

Promotion evidence:
- feature branch: `formal/prec04-drift-hitting-time-v1`;
- final feature head: `3ea9086976ac595eb034a125390d69264e12772e`;
- feature CI `34875538212`: success;
- source-semantic audit: complete against frozen Core 3 P-REC-04;
- prohibited-proof audit: clean (`sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`);
- clean integration branch: `formal/prec04-main-integration-v1`;
- clean integration head: `50ac5834ff74fe4aa5229b60be87a256e762c778`;
- clean integration CI `34877803577`: success;
- proof PR #85;
- PR-triggered CI `34880820942`: success;
- proof main commit `4946a4435d3c15efbf0ca13aed7b44e65defc79c`;
- proof resulting-main CI `34882613059`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger/recovery
checkpoint.**

## Previous promotion — P-PER-04

P-PER-04 is already counted in the authoritative **78/106 full-green** baseline.
Frozen Core 3 §8.6 defines the Bouligand contingent cone with positive-time
increments `h ↓ 0` and states the local tangency necessity theorem: if a viable
trajectory starts at `x`, remains in the closed viability/identity domain and is
differentiable at time zero, then its initial velocity lies in that positive
contingent cone.

The Lean theorem uses Mathlib `posTangentConeAt = tangentConeAt NNReal`, not the
two-sided real-scalar tangent cone, and keeps K-VIA-01 separate.

Canonical theorem surface:
- `UEOT.V3.ViabilityTangency.p_per_04`.

Completed evidence:
- feature `formal/pper04-tangency-necessity-v1@ce6eccf5ca4b6f30aae1dcd0416fc1b79286f2d2`, CI `34858878140` success;
- clean integration `formal/pper04-main-integration-v1@f5db4c5e547866e488ad1d33c0789bc0ce5ec48c`, CI `34862446244` success;
- proof PR #83 CI `34863236502` success;
- proof main `ba9b9c350038dafa52afdda954d2294361a01fc7`, resulting-main CI `34863965181` success;
- ledger main `22f536ea27eecf78de5005f47ecfea21edd001c6`, ledger resulting-main CI `34866495921` success.

## Previous promotion — P-QSD-03

P-QSD-03 is already counted. Frozen Core 3 §10.3 is formalized without swapping
it with P-QSD-01 or P-QSD-04. For one fixed initial law `μ`, the source-facing
theorem retains the exact closed mixing/survival window and endpoint equality.

Canonical theorem surface:
- `UEOT.V3.QSDDurationWindow.p_qsd_03`;
- `UEOT.V3.QSDDurationWindow.window_nonempty_iff`.

Completed evidence:
- feature `formal/pqsd03-duration-window-v1@11076f31eec199a4e80ba13e00e037c5e62a2de2`, CI `34831456183` success;
- clean integration `formal/pqsd03-main-integration@8e85e687ea11a8dac89ebe7ebbab8240551d8f99`, CI `34847211649` success;
- proof PR #79 CI `34848043040` success;
- proof main `bab0b0718afaee90e858d71e41340066ba1774d8`, resulting-main CI `34848676178` success;
- ledger main `6561169fae9529a822642c5b6921d7d9c59aa250`, ledger resulting-main CI `34856357799` attempt 3 success.

## Previous full-green checkpoint — 78/106

The authoritative full-green baseline before this P-REC-04 promotion is
`main@22f536ea27eecf78de5005f47ecfea21edd001c6`. All 78 counted P-IDs at that
checkpoint remain closed absent a substantive frozen-source mismatch or CI
regression. P-REC-04 proof code subsequently landed at
`main@4946a4435d3c15efbf0ca13aed7b44e65defc79c` and passed resulting-main CI
`34882613059`; that proof-main commit does not by itself increment the ledger.

P-REF-04 and P-REF-05 were already members of the earlier counted baseline.
Source-facing wrapper branches audited during prior cycles are interface
hardening only and must **not** be double-counted as new P-IDs.

## Grounded pending fronts

After this staged promotion, 27 P-IDs remain not yet counted and require fresh
source-first audits. Known non-quick fronts include:

- P-PER-02: Polish-space Feller semigroup + tight occupation laws + Prokhorov/Portmanteau weak-convergence infrastructure;
- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds;
- P-DDH-02/03: finite exponential-family calculus and KL variational duality;
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis;
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations;
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation;
- P-QSD-01/04: source-locked distinct non-A results.

P-REC-03 is the natural recovery follow-up: the finite hitting-time potential
must satisfy the genuine Markov first-step equation `PV_A - V_A = -1` outside
`A`. P-COMP-01 still requires its finite-partition/multi-block product-law
bridge and is not discharged by binary conditional-mutual-info wrappers.

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
