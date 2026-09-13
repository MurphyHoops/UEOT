# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state. This file is the
> fallback archival snapshot on `main` and is updated at meaningful lifecycle
> transitions.

## Current lifecycle snapshot

- counted coverage: **64/106**;
- not yet counted: **42**;
- latest proof main before this docs commit:
  `b26de5a7bf8a725e9446b883f9181d0732e86c7f`;
- newest counted promotion: **P-COMP-06**;
- feature CI `34754842269`: success;
- integration CI `34755655869`: success;
- post-main CI `34755873092`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean;
- **64/106 becomes full-green only after this ledger commit's own main CI succeeds.**

## P-COMP-06 — counted pending ledger CI

- branch `formal/pcomp06-carrier-lift`;
- feature head `168e432b8479a6683d933d81bc1e362df2a4340c`;
- theorem `UEOT.V3.CompositionCarrierLift.p_comp_06`;
- clean integration/main proof commit
  `b26de5a7bf8a725e9446b883f9181d0732e86c7f`;
- preserves both nested inclusion-min operations exactly.

## Active lane — P-COMP-07

- branch `formal/pcomp07-composition-window`;
- latest branch head `9337f0d58ebb283a1560ba947671ecf2688d0b59`;
- candidate `UEOT.V3.CompositionWindow.p_comp_07`;
- source semantic audit: complete;
- no boundary-witness weakening: compactness + continuity must derive attained
  `k_D`,`k_F`;
- CI `34755844111` on the real-order import fix still failed to synthesize
  `TopologicalSpace ℝ`;
- next action: locate the exact pinned Mathlib public module/instance rather than
  adding imports blindly.

## Active lane — P-ALI-02

- branch `formal/pali02-parent-value`;
- head `a6dd0fe8d06c31abd1c950608698452e2ced3c94`;
- candidate `UEOT.V3.AlignmentParentValue.p_ali_02`;
- source-facing version now uses a finite `PiLp 2` real Hilbert direct sum,
  actual parent/child `HasGradientAt` certificates, and actual `HasDerivAt`
  dynamics;
- the parent derivative is produced by Mathlib's chain rule, not assumed;
- feature CI `34756045489`: in progress at snapshot time.

## Audited next lane — P-KL-03

Reusable foundations already on main/pinned Mathlib:
- `UEOT.V3.InformationKernelKL.klDiv_compProd_right_eq_lintegral`;
- `InformationTheory.klDiv_compProd_eq_add`;
- `UEOT.V3.DynamicsKernel`;
- `MeasurableEquiv.IicProdIoc`.

Remaining obligation: iterate the one-step chain rule over a finite horizon for
possibly history-dependent kernels. Do not weaken to one-step or
homogeneous-Markov semantics.

## Newly discovered reuse front

Build output confirms existing modules for discrete conditional entropy,
conditional mutual information and deterministic statistics. Before writing new
foundations, audit these for P-COMP-04 and P-EVO-02.

## Exact next actions

1. require this 64/106 ledger commit's own main CI to succeed;
2. collect P-ALI-02 CI `34756045489`, decode/fix exact errors if red;
3. resolve P-COMP-07's pinned Mathlib real-topology instance/import exactly and rerun feature CI;
4. once a source-closed feature is green, clean-integrate only its theorem file plus top-level import from latest full-green main;
5. use CI time to audit existing conditional-entropy/MI modules for P-COMP-04 and P-EVO-02;
6. refresh Issue #56 at meaningful lifecycle transitions.

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
