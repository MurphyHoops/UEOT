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
- canonical source object: available in the project File Library for semantic audit
- exact canonical source bytes in public repo: **pending synchronization**

A P-ID is counted `proved` only after frozen-source semantic matching, official
import reachability, feature/integration/post-main CI gates, prohibited-proof
audit, safe main integration, and ledger synchronization. Feature-green work
alone never changes this ledger.

## Current source-level coverage

| status | count |
|---|---:|
| **proved** | **61** |
| **partial** | **0** |
| **pending** | **45** |
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
- **Dual-drive / alignment:** P-DDH-01, P-ALI-03
- **Composition:** P-COMP-03
- **KL / path information:** P-KL-01

Count check: `59 + 2 = 61`.

## Newly counted promotions — P-COMP-03 and P-KL-01

### P-COMP-03 — composition margin

Frozen contract: for a finite nonempty cut family with each `K_pi`
`L_pi`-Lipschitz,

`Gamma_comp(T) = min_pi d(T, K_pi T)`

is `(1 + max_pi L_pi)`-Lipschitz.

Canonical theorem:

- `UEOT.V3.CompositionMargin.p_comp_03`.

Evidence:

- feature branch `formal/pcomp03-composition-margin`;
- feature head `7e074e694c26e52901342336b5e57b666df4fa8c`;
- feature CI `34752374454`: success;
- finite minimum/maximum represented explicitly by `Finset.inf'` / `Finset.sup'`;
- exact `(1+L)` constant retained; it was not weakened to `2`.

### P-KL-01 — event/Bernoulli KL lower bound

Frozen contract: for baseline path law `P0`, reachable `Q ≪ P0`, and measurable
event `A`, writing `q=P0(A)` and `p=Q(A)`,

`D_KL(Q || P0) >= d_Bern(p || q)`.

Canonical theorem:

- `UEOT.V3.PathEventKL.p_kl_01`.

Evidence:

- feature branch `formal/pkl01-event-bernoulli`;
- feature head `c691145fc6ef8a1fa9332abebf09f3659a5cb2eb`;
- feature CI `34753031461`: success;
- reuses the already machine-checked event-indicator pushforward and KL
  data-processing layer in `InformationEventBernoulli`;
- the frozen source hypothesis `Q ≪ P0` is retained even though the reused
  data-processing result is stronger.

### Joint promotion evidence

- clean integration branch `formal/pcomp03-pkl01-integration`;
- clean atomic integration/main proof commit
  `08ec1bfa1af3dd1d90ff0d046b8cf3472e16fdf9`;
- exact integration diff: two source-facing theorem files plus their two
  top-level imports;
- integration CI `34753554298`: success;
- `main` safely non-force fast-forwarded to the same proof commit;
- post-main CI `34753815801`: success;
- prohibited-proof audit in both new files:
  `sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`;
- frozen-source semantic audit: complete.

**Status: BOTH PROVED / COUNTED.**

## Recent earlier counted promotions

- **P-DDH-01 / P-ALI-03:** integration/main proof commit
  `9bff83a544929a0191596f6a1b9c7c8d2a6f87b7`; integration CI
  `34752277556`; post-main CI `34752528830`.
- **P-OMG-01 / P-OMG-02:** integration commit
  `4db94c39dddce53a5543e40568e5fc104321e88b`; integration CI
  `34751042701`; post-main CI `34751300612`.
- **P-INT-01:** main `d757ea0dd14755233b94d40763f457773a52089f`;
  post-main CI `34750114264`.
- **P-INFO-03:** main `57e987a18a5dd8feca224b91e3e78b93c2a44de8`;
  post-main CI `34744919310`.
- **P-ID-02:** main `4a29c2d5aa6a805d867e1934f6013aa49f1dc431`;
  post-main CI `34717095993`.

## Active unresolved front

There are **45 not-yet-counted P-IDs**. Two source-facing proof lanes are
currently active:

- **P-EVO-01:** source-faithful finite Price-decomposition lane on
  `formal/pevo01-price-decomposition`; current blocker is only the Lean API for
  commuting the two finite Fintype sums. Frozen `M=D_bK`, deterministic
  `p'=pM/bar_b`, zero-growth-row semantics, and the deterministic/random-ratio
  distinction are already preserved.
- **P-COMP-05:** canonical finite Booleanization/signature-atom lane on
  `formal/pcomp05-boolean-atoms`; feature CI is running. The implementation uses
  `BooleanSubalgebra.closure (Set.range V)` directly and targets partition,
  region reconstruction, atom equivalence, and least-generated-algebra clauses.

The remaining **43** are in source-to-main audit or later proof queues. Feature
green does not change 61/106.

High-value audited future lane: **P-KL-03** can reuse
`UEOT.V3.InformationKernelKL.klDiv_compProd_right_eq_lintegral` and pinned
Mathlib's compProd KL chain rule; the remaining work is finite-horizon
history-dependent path recursion/iteration, not a ground-up KL development.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing the exact bytes and independently recomputing the SHA-256 remains
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** source P-IDs pass the
source-theorem proof contract, with no theorem counted from a helper or
feature-green branch alone.
