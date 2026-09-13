# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state. This file is the
> fallback archival snapshot on `main` and is updated at meaningful lifecycle
> transitions.

## Current lifecycle snapshot

- coverage staged by this recovery checkpoint: **69/106**;
- not yet counted after this checkpoint: **37**;
- proof main: `17f7ca2070a439a7e4c99622d3c27095431a1571`;
- newest staged promotion: **P-EVO-02**;
- P-EVO-02 clean-integration CI `34765061853`: success;
- P-EVO-02 post-main CI `34765399086`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean;
- **69/106 becomes full-green only after this four-file recovery/ledger checkpoint is integrated to main and its resulting main CI succeeds.**

## P-EVO-02 — staged counted promotion

Frozen source §25.3 is preserved exactly for finite `T` independent of the
joint parent/offspring pair `(F,F')` and copied without error:

`I((F,T);(F',T)) = I(F;F') + H(T)`.

Implementation and evidence:
- canonical theorem `UEOT.V3.EvolutionSharedLabel.p_evo_02`;
- feature branch `formal/pevo02-shared-label`;
- feature head `bfe0c3f43728a9ae5a07f1729c143039d16d7cff`;
- feature CI `34763489145`: success;
- independence encoded structurally by `ρ.prod (copyJoint τ)`;
- exact copy encoded by the diagonal copy law;
- `sharedRepack` is only a measurable coordinate regrouping;
- clean integration head `0a3691ef1d97cae1a8017adae47bd8aa7ea49c47`;
- PR #59 clean-integration CI `34765061853`: success;
- main proof commit `17f7ca2070a439a7e4c99622d3c27095431a1571`;
- post-main CI `34765399086`: success;
- exact integration diff: theorem file + one top-level import.

## P-KL-03 — full-green counted baseline

Frozen §22.3 history-dependent finite-horizon KL chain rule is fully integrated.
Main proof commit `b3e1c152e42b4e2a2b7001776214ecaaa35aae18`, post-main CI
`34763070439`, and 68/106 ledger main CI `34763815124` all succeeded.

## Active proof lane — P-KL-02

Frozen §22.2 source contract:

- all probability laws `Q ≪ P0` satisfying `Q(A) ≥ p`;
- `q := P0(A)`, `0 < q < 1`;
- if `p ≤ q`, infimum `0`, attained by `P0`;
- if `p > q`, infimum exactly Bernoulli KL;
- explicit RN optimizer
  `(p/q) 1_A + ((1-p)/(1-q)) 1_{Aᶜ}`;
- prove probability, absolute continuity, exact event probability and exact KL;
- retain `p = 1` with `0 log 0 = 0` convention.

Current construction:
- branch `formal/pkl02-event-iprojection`;
- `eventTiltDensity` is the exact frozen two-region RN density;
- `eventIProjection := P0.withDensity eventTiltDensity`;
- construction / measurable / AC / RN derivative layer green at
  `333a3e9ffa0cadbaaa0b167ec0ccdc7d8685317a`, CI `34765080012`;
- mass/probability head `1378efc916e894057cd4cd38cedbfd9c5eac9f80` corrected the pinned Mathlib `withDensity_apply` namespace and is under CI `34765567421`;
- exact-KL plan: use `klDiv_eq_lintegral_klFun_of_ac`, replace RN derivative by the explicit density a.e., split the l-integral over `A/Aᶜ`, then compare with `InformationBernoulliKL.bernoulliLaw_klDiv_toReal`;
- sharp lower-bound plan: combine P-KL-01 with Bernoulli KL monotonicity on `r ≥ p > q`; prefer a binary Markov contraction/data-processing proof if the kernel helper is shorter than an analytic derivative formalization;
- feature green never increments coverage.

## Grounded non-quick audit — P-EVO-03

Frozen P-EVO-03 depends on the full Perron--Frobenius asymptotic package K-PF-01:
positive left/right Perron vectors for a primitive nonnegative matrix, spectral
gap, and normalized power convergence. Pinned Mathlib exposes
`Matrix.IsPrimitive` but no directly reusable full asymptotic theorem was found.
Do not replace this with an assumed convergence hypothesis and count it as the
source theorem.

## Exact next actions

1. integrate this 69/106 recovery/ledger checkpoint through PR CI;
2. require the resulting main CI before calling **69/106 full-green**;
3. collect P-KL-02 run `34765567421`; repair only exact Lean/API failures;
4. once optimizer probability/event-mass is green, add exact-KL as the next isolated layer;
5. then prove Bernoulli monotonicity and the global all-`Q` infimum theorem;
6. clean-integrate P-KL-02 only from the latest full-green main; feature green does not count.

## Guards

- do not reopen counted P-IDs absent source mismatch/CI regression;
- no `sorry`, `admit`, `native_decide`, unsourced `axiom`;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-REF-03 requires arbitrary signal spaces;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-BRG-01 includes concentration/extinction/maximizer-ratio clauses;
- P-KL-04/05 must remain at their frozen CTMC/Girsanov level.

## Recovery order

1. `UEOT_CORE3_LEAN_OPERATIONS.md`;
2. Issue #56;
3. `PID_STATUS.yaml`;
4. `FORMALIZATION_STATE.md`;
5. `V3_COVERAGE_STATUS.md`;
6. live main/branches/CI.
