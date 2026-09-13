# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`. GitHub Issue #56
> carries the live cross-chat construction log between archival checkpoints.

Last synchronized: **2026-09-13**

## Environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`
- exact canonical bytes in public repo: pending synchronization

## Current counted checkpoint

| operational state | count |
|---|---:|
| integrated proved, staged by this checkpoint | **69** |
| active source-facing proof lanes | **1** |
| integration/promotion lanes | **0** |
| blocked | **0** |
| pending/unclassified | **36** |
| total | **106** |

This recovery commit stages **69 proved / 37 not yet counted**. It must itself
pass PR CI, land on `main`, and pass the resulting main CI before 69/106 is
called full-green.

## Newly promoted proof — P-EVO-02

Frozen source §25.3:

`I((F,T);(F',T)) = I(F;F') + H(T)`

for finite `T` independent of the joint pair `(F,F')` and copied without error.

Evidence:
- theorem `UEOT.V3.EvolutionSharedLabel.p_evo_02`;
- feature `formal/pevo02-shared-label@bfe0c3f43728a9ae5a07f1729c143039d16d7cff`;
- feature CI `34763489145`: success;
- clean integration head `0a3691ef1d97cae1a8017adae47bd8aa7ea49c47`;
- PR #59 clean-integration CI `34765061853`: success;
- main proof commit `17f7ca2070a439a7e4c99622d3c27095431a1571`;
- post-main CI `34765399086`: success;
- source semantic audit complete and prohibited-proof audit clean.

No noisy-copy, pairwise-independence, or coordinate-loss weakening is used.

## Previous full-green checkpoint — P-KL-03 / 68 of 106

P-KL-03 is already fully counted. Its history-dependent finite-horizon path KL
chain rule is on main, proof post-main CI `34763070439` succeeded, and the
68/106 ledger main CI `34763815124` succeeded.

## Active proof lane — P-KL-02

Frozen source §22.2 requires the exact event I-projection over all absolutely
continuous path laws, not just P-KL-01's event data-processing lower bound.
For `q=P0(A)`, `0<q<1`, `0≤p≤1`:

- `p≤q`: infimum `0`, baseline `P0` is feasible;
- `p>q`: infimum is `d_Bern(p||q)`;
- active-case optimizer has RN density
  `(p/q) 1_A + ((1-p)/(1-q)) 1_{Aᶜ}`;
- optimizer must be a probability law, satisfy `Q*≪P0`, have `Q*(A)=p`, and
  attain exact KL;
- `p=1` must be retained.

Current branch `formal/pkl02-event-iprojection`:
- explicit `eventTiltDensity` and `eventIProjection` are implemented;
- construction / measurability / AC / RN derivative layer green at
  `333a3e9ffa0cadbaaa0b167ec0ccdc7d8685317a`, CI `34765080012`;
- current head `1378efc916e894057cd4cd38cedbfd9c5eac9f80` repairs the pinned Mathlib
  `withDensity_apply` namespace after adding exact event/complement masses and a
  probability instance theorem;
- CI `34765567421` is the current gate at synchronization;
- next isolated layers are exact KL, Bernoulli monotonicity, then the global
  infimum theorem.

## Grounded non-quick fronts

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron--Frobenius asymptotics / martingale foundations.
- P-REF-03: arbitrary signal-space conditional expectation.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/03/04: source-locked distinct non-A results.
- P-BRG-01: includes extinction/concentration/maximizer-relative-mass clauses.

P-EVO-03 specifically requires the full K-PF-01 primitive-matrix asymptotic
package; pinned Mathlib has `Matrix.IsPrimitive` definitions but no directly
reusable complete Perron--Frobenius power-convergence theorem was found. Do not
count an assumed-convergence surrogate.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56, `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent audit/proof lane.
