# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state. This file is the
> fallback archival snapshot on `main` and is updated at meaningful lifecycle
> transitions.

## Current lifecycle snapshot

- authoritative counted coverage: **69/106 full-green**;
- remaining frozen P-IDs: **37**;
- current main: `eb7aacf4ba95dc2308c7434144dca40d001c0a39`;
- newest counted promotion: **P-EVO-02**;
- P-EVO-02 feature CI `34763489145`: success;
- P-EVO-02 clean-integration CI `34765061853`: success;
- P-EVO-02 proof main commit `17f7ca2070a439a7e4c99622d3c27095431a1571`;
- P-EVO-02 post-main CI `34765399086`: success;
- 69/106 recovery/ledger PR #60 CI `34765913122`: success;
- 69/106 ledger main CI `34766813335`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean.

P-EVO-02 is therefore fully counted. Do not reopen it absent a substantive
frozen-source mismatch or CI regression.

## P-KL-03 — previous full-green baseline

Frozen §22.3 history-dependent finite-horizon KL chain rule is fully integrated.
Main proof commit `b3e1c152e42b4e2a2b7001776214ecaaa35aae18`, post-main CI
`34763070439`, and 68/106 ledger main CI `34763815124` all succeeded.

## Active proof lane — P-KL-02

Frozen §22.2 source contract remains exact:

- optimize over all probability laws `Q ≪ P0` satisfying `Q(A) ≥ p`;
- `q := P0(A)`, `0 < q < 1`, `0 ≤ p ≤ 1`;
- if `p ≤ q`, infimum `0`, attained by `P0`;
- if `p > q`, infimum exactly Bernoulli KL;
- explicit RN optimizer `(p/q) 1_A + ((1-p)/(1-q)) 1_{Aᶜ}`;
- prove optimizer probability, absolute continuity, exact event mass and exact KL;
- retain the endpoint `p = 1` with `0 log 0 = 0`;
- P-KL-01 alone is not an acceptable weakening.

Primary feature branch: `formal/pkl02-event-iprojection`.

Implemented layers:
- `eventTiltDensity`: exact frozen two-region RN density;
- `eventIProjection := P0.withDensity eventTiltDensity`;
- measurable/AC/RN derivative layer;
- exact event/complement mass lemmas;
- probability-law lemma.

CI history relevant to the current checkpoint:
- construction/RN helper head `333a3e9ffa0cadbaaa0b167ec0ccdc7d8685317a`, CI `34765080012`: success;
- head `301fac6615d133340de071a08d5a11472dade41f`, CI `34766038056`: failed only because two redundant `simp only [Measure.restrict_univ]` commands made no progress;
- repair head `058a7d35c044f143a3b2622cb05b1dfb292c5ef1` removes only those no-op tactics;
- primary feature CI `34766950875` is the current validation run for that repair.

Parallel exact-KL scratch lane:
- branch `formal/pkl02-exact-kl-scratch` from `058a7d35...`;
- head `2052313aad3209b8e1458c6340fd36df0c170589`;
- prototypes `eventIProjection_klDiv_formula` directly in `ENNReal` using
  `InformationTheory.klDiv_eq_lintegral_klFun_of_ac`, the explicit RN derivative,
  and the `A/Aᶜ` l-integral split;
- scratch CI `34767150813` validates only the next proof layer and never increments coverage.

## Exact next actions

1. collect primary P-KL-02 CI `34766950875`;
2. if green, treat optimizer mass/probability as a stable feature checkpoint;
3. collect scratch exact-KL CI `34767150813`, repair only exact Lean/API errors, then transplant the green exact-KL theorem to the primary branch;
4. prove active-side Bernoulli KL monotonicity for `r ≥ p > q` and combine it with P-KL-01;
5. state and prove the global all-`Q` infimum theorem, including the `p ≤ q` baseline branch and the `p = 1` endpoint;
6. source-semantic/prohibited-proof audit;
7. feature green still does **not** increment coverage;
8. clean-integrate P-KL-02 only from the latest full-green main, then require post-main CI and ledger sync before any coverage increment.

## Grounded non-quick audit — P-EVO-03

Frozen P-EVO-03 depends on the full Perron--Frobenius asymptotic package K-PF-01:
positive left/right Perron vectors for a primitive nonnegative matrix, spectral
gap, and normalized power convergence. Pinned Mathlib exposes
`Matrix.IsPrimitive` but no directly reusable full asymptotic theorem was found.
Do not replace this with an assumed convergence hypothesis and count it as the
source theorem.

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
