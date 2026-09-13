# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state. This file is the
> fallback archival snapshot on `main` and is updated at meaningful lifecycle
> transitions.

## Current lifecycle snapshot

- counted coverage: **63/106**;
- not yet counted: **43**;
- latest proof main before this docs commit:
  `bfd9d83073cb929ea12de4267005023749023df5`;
- newest counted promotions: **P-EVO-01 and P-COMP-05**;
- integration CI `34754713285`: success;
- post-main CI `34754974676`: success;
- source semantic audits: complete;
- prohibited-proof audits: clean;
- **63/106 becomes full-green only after this ledger commit's own main CI succeeds.**

P-EVO-01:
- feature `formal/pevo01-price-decomposition`;
- head `a3f9473c4dfb71c049fa177a5effce46837122bd`;
- feature CI `34754264183`: success;
- theorem `UEOT.V3.EvolutionPrice.p_evo_01`;
- source-valid zero-growth rows and deterministic/random-ratio distinction retained.

P-COMP-05:
- feature `formal/pcomp05-boolean-atoms`;
- head `dfb398a6c2f8edfa458ef5d2a242f02fd3d46971`;
- feature CI `34754344097`: success;
- theorem `UEOT.V3.CompositionBooleanAtoms.p_comp_05`;
- full atom/minimal-Boolean-algebra theorem retained.

## Active lane — P-COMP-06
- branch `formal/pcomp06-carrier-lift`;
- head `168e432b8479a6683d933d81bc1e362df2a4340c`;
- candidate `UEOT.V3.CompositionCarrierLift.p_comp_06`;
- feature CI `34754842269`: success;
- preserves both nested inclusion-min operations;
- next: final prohibited-proof audit and clean integration from latest full-green main.

## Active lane — P-COMP-07
- branch `formal/pcomp07-composition-window`;
- head `0826699b3fe135c3faec353153cc4d2fa533e13a`;
- candidate `UEOT.V3.CompositionWindow.p_comp_07`;
- feature CI `34755041666`: pending at snapshot time;
- compactness and continuity derive attained threshold boundaries.

## Active lane — P-ALI-02
- branch `formal/pali02-parent-value`;
- head `b0ef953829c83f0219ffe62e8b54243ae2270b51`;
- candidate `UEOT.V3.AlignmentParentValue.p_ali_02`;
- feature CI `34755240251`: pending at snapshot time;
- exact finite Hilbert decomposition + Cauchy--Schwarz lower bound.

## Audited next lane — P-KL-03
Reusable foundations already on main/pinned Mathlib:
- `UEOT.V3.InformationKernelKL.klDiv_compProd_right_eq_lintegral`;
- `InformationTheory.klDiv_compProd_eq_add`;
- `UEOT.V3.DynamicsKernel`;
- `MeasurableEquiv.IicProdIoc`.

Remaining obligation: iterate the one-step chain rule over a finite horizon for
possibly history-dependent kernels. Do not weaken to a one-step or
homogeneous-Markov theorem.

## Exact next actions
1. require the main CI of the 63/106 ledger commit to succeed;
2. collect P-COMP-07 CI `34755041666`, decode/fix exact error if red;
3. collect P-ALI-02 CI `34755240251`, decode/fix exact error if red;
4. after 63 is full-green, source/prohibited audit P-COMP-06 and any other green
   feature, then clean-integrate only minimal theorem/import diffs from that main;
5. continue P-KL-03 finite-history path recursion audit while CI runs;
6. refresh Issue #56 at every lifecycle transition.

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
