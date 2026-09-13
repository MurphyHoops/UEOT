# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state. This file is the
> fallback archival snapshot on `main` and is updated only at meaningful
> lifecycle transitions.

## Current lifecycle snapshot

- counted coverage: **61/106**;
- not yet counted: **45**;
- active source-facing proof lanes: **2**;
- pending/audit queue: **43**;
- newest counted promotions: **P-COMP-03 and P-KL-01**;
- clean integration/main proof commit:
  `08ec1bfa1af3dd1d90ff0d046b8cf3472e16fdf9`;
- integration CI `34753554298`: success;
- post-main CI `34753815801`: success;
- source semantic audit: complete for both;
- prohibited-proof audit: clean.

P-COMP-03:
- feature `formal/pcomp03-composition-margin`;
- head `7e074e694c26e52901342336b5e57b666df4fa8c`;
- feature CI `34752374454`: success;
- theorem `UEOT.V3.CompositionMargin.p_comp_03`;
- exact source constant `(1+max_pi L_pi)` retained.

P-KL-01:
- feature `formal/pkl01-event-bernoulli`;
- head `c691145fc6ef8a1fa9332abebf09f3659a5cb2eb`;
- feature CI `34753031461`: success;
- theorem `UEOT.V3.PathEventKL.p_kl_01`;
- frozen `Q ≪ P0` assumption retained;
- existing event-indicator/KL data-processing foundation reused.

## Active lane — P-EVO-01

- branch `formal/pevo01-price-decomposition`;
- checkpoint head `dbf40a016377ad3689e4c88b0d5f67a2a675a9c5`;
- candidate `UEOT.V3.EvolutionPrice.p_evo_01`;
- frozen `M=D_bK`, deterministic `p'=pM/bar_b`, zero-growth-row semantics and
  deterministic/random-ratio distinction are preserved;
- last CI `34753626091`: failure only at double finite-sum commutation;
- next action: use a verified pinned-Mathlib product/Fintype sum rearrangement,
  not another guessed identifier.

## Active lane — P-COMP-05

- branch `formal/pcomp05-boolean-atoms`;
- head `7f3c73fc8d801a17b79b86aa9b8c7402344d0562`;
- candidate `UEOT.V3.CompositionBooleanAtoms.p_comp_05`;
- feature CI `34754028909`: running at snapshot time;
- implementation uses `BooleanSubalgebra.closure (Set.range V)` and proves the
  signature partition, region reconstruction, atom characterization and least
  generated Boolean algebra clauses.

## Audited next lane — P-KL-03

Reusable foundations already on main/pinned Mathlib:
- `UEOT.V3.InformationKernelKL.klDiv_compProd_right_eq_lintegral`;
- `klDiv_compProd_eq_add`;
- `UEOT.V3.DynamicsKernel`.

Remaining obligation: iterate the one-step chain rule over finite-horizon,
possibly history-dependent kernels. Do not weaken to a one-step or homogeneous
Markov statement.

## Exact next actions

1. require the CI of the ledger commit recording **61/106** to succeed; only
   then is 61/106 a full-green checkpoint;
2. inspect P-COMP-05 CI `34754028909`; decode/fix exact Lean errors if red;
3. repair only the P-EVO-01 double-sum commutation proof and rerun feature CI;
4. source/prohibited audit any green active lane, then clean-integrate from the
   latest full-green main;
5. continue P-KL-03 path-recursion audit while CI runs;
6. refresh Issue #56 at each meaningful lifecycle checkpoint.

## Guards

- feature green never increments coverage;
- do not reopen counted P-IDs absent source mismatch/CI regression;
- no `sorry`, `admit`, `native_decide`, unsourced `axiom`;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-REF-03 requires arbitrary signal spaces;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-BRG-01 includes concentration/extinction/maximizer-ratio clauses.

## Recovery order

1. `UEOT_CORE3_LEAN_OPERATIONS.md`;
2. Issue #56;
3. `PID_STATUS.yaml`;
4. `FORMALIZATION_STATE.md`;
5. `V3_COVERAGE_STATUS.md`;
6. live main/branches/CI.
