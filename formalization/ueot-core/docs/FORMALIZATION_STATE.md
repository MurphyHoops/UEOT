# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`. GitHub Issue #56
> carries the live cross-chat construction log when available.

Last synchronized: **2026-09-14**

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
| integrated proved, staged by this checkpoint | **71** |
| active proof | **1** |
| blocked | **0** |
| pending/unclassified | **34** |
| total | **106** |

The authoritative full-green checkpoint before this recovery branch is
**70/106**. This branch stages **71 proved / 35 not yet counted** after P-API-01
completed all proof-side and post-main gates. It must itself pass PR CI, land on
`main`, and pass the resulting main CI before 71/106 is called full-green.

The active proof lane is P-ALG-01. It is **not counted**.

## Newly staged proof — P-API-01

Frozen §28.3 exact/approximate process-interface composition is implemented by:

- `UEOT.V3.ProcessInterface.p_api_01_exact`;
- `UEOT.V3.ProcessInterface.p_api_01_approx`.

The implementation contains exactly the frozen process-interface data: protocol
lift, measurable path readout and naturality of path-law pushforward for all
declared protocols. Exact interfaces compose exactly. Approximate TV defects
compose with `min 1 (εAB + εBC)` by pushforward contraction plus the TV triangle
inequality. Frozen §28.4 control actions, policy lifts, rewards and constraints
remain separate.

Evidence:
- feature `formal/papi01-process-interface-fresh@0f76d04a4dcc34b2d2aaa806d5803e4823561bbc`;
- feature CI `34769177051`: success;
- clean integration `formal/papi01-clean-int-70@697df634e502bbd5407fc7f832963ac0afe1203d`;
- PR #64 CI `34770423058`: success;
- proof main `f72e2a7448c88b8c90dbf5856522f71a588886ce`;
- post-main CI `34770728978`: success;
- source semantic audit complete;
- prohibited-proof audit clean.

## Previous full-green checkpoint — 70/106

P-KL-02 and all earlier counted theorems are fully green. The 70/106 ledger main
CI `34770086580` succeeded on
`main@8f29d29a0fe32bf9cccb7cbc12c84676768d9592`.

## Active proof — P-ALG-01

Frozen §28.5 is a genuine finite exact partition-refinement algorithm, not an
existence wrapper and not approximate clustering. Source audit is locked to:

- finite state set and common finite action set;
- transition matrix for every action;
- reward `r(x,a)` and output label `o(x)`;
- initial partition by output plus complete reward vector;
- exact refinement by current block plus all action/current-block transition
  masses;
- finite termination;
- terminal controlled stability/lumpability;
- coarsest stable refinement of the initial partition;
- preservation of output/reward/all-action one-step quotient laws;
- all corresponding finite-horizon output laws by recursion.

Current feature branch: `formal/palg01-refinement-core`.
Current head: `cfe4665da5a61cacdc74be2810af81665e4b19e0`.
Current CI: `34770820284`.

First layer already implemented:
- finite controlled `Model`;
- `initialSetoid`;
- exact `blockMass`;
- `refineSetoid`;
- `Refines` and one-round split-only theorem;
- `Stable` plus fixed-point equivalence;
- target-block representative independence;
- finite `relPairs` encoding for termination.

Pinned Mathlib verification found:
- `Quotient.fintype` exists at the project pin;
- `Finset.card_lt_card` and `ssubset_iff_subset_ne` are available;
- `Finpartition.ofSetoid` gives the finite equivalence-class partition;
- `part`, `biUnion_parts` and disjoint finite-sum infrastructure provide the
  exact bridge needed for the frozen coarsestness proof.

Do not add §28.4 constraint indicators to P-ALG-01. Do not replace exact equality
with floating tolerances.

## Grounded non-quick fronts

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron--Frobenius asymptotics / martingale foundations.
- P-REF-03: arbitrary signal-space conditional expectation.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/03/04: source-locked distinct non-A results.
- P-BRG-01: includes extinction/concentration/maximizer-relative-mass clauses.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron--Frobenius asymptotic package. Do not count an assumed-convergence
surrogate.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available,
   `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent audit/proof lane.
