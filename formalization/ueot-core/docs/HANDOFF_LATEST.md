# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot on `main` and is updated at
> meaningful lifecycle transitions.

## Current lifecycle snapshot

- authoritative full-green baseline before this checkpoint: **70/106**;
- this branch stages **71/106** after P-API-01 completed all proof-side and
  post-main gates;
- remaining not-yet-counted P-IDs after staging: **35**;
- full-green 70 baseline: `8f29d29a0fe32bf9cccb7cbc12c84676768d9592`;
- P-API-01 proof main: `f72e2a7448c88b8c90dbf5856522f71a588886ce`;
- newest staged promotion: **P-API-01**;
- P-API-01 feature CI `34769177051`: success;
- P-API-01 clean-integration PR #64 CI `34770423058`: success;
- P-API-01 post-main CI `34770728978`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean.

**Do not call 71/106 full-green until this ledger/recovery branch passes PR CI,
lands on `main`, and the resulting main CI succeeds.**

## P-API-01 — completed proof contract

Frozen §28.3 is implemented literally:

- process interface = protocol lift plus measurable path readout;
- exact naturality for all declared protocols;
- exact composition has the source order
  `J_AC = J_AB ∘ J_BC`, `C_AC = C_BC ∘ C_AB`;
- approximate TV defects compose with
  `min 1 (ε_AB + ε_BC)`;
- §28.4 control actions, policy lifts, rewards and constraints are not folded
  into this process-interface theorem.

Canonical theorems:
- `UEOT.V3.ProcessInterface.p_api_01_exact`;
- `UEOT.V3.ProcessInterface.p_api_01_approx`.

Evidence:
- feature `formal/papi01-process-interface-fresh@0f76d04a4dcc34b2d2aaa806d5803e4823561bbc`;
- feature CI `34769177051`: success;
- clean integration `formal/papi01-clean-int-70@697df634e502bbd5407fc7f832963ac0afe1203d`;
- clean PR #64 CI `34770423058`: success;
- proof main `f72e2a7448c88b8c90dbf5856522f71a588886ce`;
- proof post-main CI `34770728978`: success.

## Previous full-green checkpoint — 70/106

P-KL-02 and all earlier counted P-IDs are fully green. The 70/106 ledger main
CI `34770086580` succeeded at
`main@8f29d29a0fe32bf9cccb7cbc12c84676768d9592`. Do not reopen counted P-IDs
absent a source mismatch or CI regression.

## Active proof lane — P-ALG-01

Frozen §28.5 is source-locked exactly as follows:

- finite state set and common finite action set;
- known exact transition matrices, reward vector and output label;
- initial partition = equal output label + equal complete action-reward vector;
- each refinement retains the current block and splits by transition mass to
  every current block under every action;
- finite termination;
- terminal controlled stability/lumpability;
- terminal partition is the coarsest stable refinement of the initial one;
- quotient preserves output, reward and every action's one-step distribution;
- finite-horizon output laws follow by kernel recursion.

Current feature branch:
`formal/palg01-refinement-core`, based on the 70/106 full-green baseline.

Implemented first layer:
- `Model` finite controlled Markov data;
- `initialSetoid` matching output + complete reward vector;
- exact `blockMass`;
- `refineSetoid` with source-faithful signature semantics;
- refinement-only property;
- `Stable` and fixed-point equivalence;
- target-block representative invariance;
- finite `relPairs` measure for termination.

CI for current head `cfe4665da5a61cacdc74be2810af81665e4b19e0` is run
`34770820284` and must be collected before layering more code.

Planned next proof layers after that build is green:
1. strict refinement strictly decreases `relPairs.card`;
2. finite iteration reaches a stable fixed point;
3. use pinned `Finpartition.ofSetoid` and disjoint block unions to prove the
   frozen coarsestness induction step;
4. construct the terminal quotient transition law for every action;
5. prove output/reward and one-step preservation;
6. prove all corresponding finite-horizon output laws;
7. expose a source-facing `p_alg_01` bundle;
8. feature CI, prohibited-proof audit, clean integration only from the then
   latest full-green main.

Do not add constraint indicators to P-ALG-01: frozen §28.5 contains output,
complete reward vectors and transition masses; §28.4 constraint transport is a
separate control-interface contract. Do not replace exact equality with floating
tolerance grouping.

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
Perron--Frobenius asymptotic package; do not count an assumed-convergence
surrogate.

## Guards

- do not reopen counted P-IDs absent source mismatch/CI regression;
- feature green never increments coverage;
- no `sorry`, `admit`, `native_decide`, unsourced `axiom`;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-REF-03 requires arbitrary signal spaces;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-BRG-01 includes concentration/extinction/maximizer-ratio clauses;
- P-KL-04/05 must remain at their frozen CTMC/Girsanov level.

## Recovery order

1. `UEOT_CORE3_LEAN_OPERATIONS.md`;
2. Issue #56 when available;
3. `PID_STATUS.yaml`;
4. `FORMALIZATION_STATE.md`;
5. `V3_COVERAGE_STATUS.md`;
6. live main/branches/CI.
