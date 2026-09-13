# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`.

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
| integrated proved | **66** |
| integration-ready feature lanes | **1** |
| active source-facing proof lanes | **1** |
| source-audited next lanes | **1** |
| blocked | **0** |
| pending/unclassified | **37** |
| total | **106** |

The authoritative source-level ledger is **66 proved / 40 not yet counted**.
This ledger commit must itself pass main CI before 66/106 is called full-green.

## Newly counted — P-ALI-02 + P-COMP-07

### P-ALI-02

- theorem `UEOT.V3.AlignmentParentValue.p_ali_02`;
- frozen finite Hilbert direct sum is represented by a heterogeneous dependent
  family `H : I → Type*` with `PiLp 2 H`;
- actual parent/child `HasGradientAt` certificates and actual `HasDerivAt`
  trajectory;
- derivative produced by chain rule, not assumed;
- feature `formal/pali02-parent-value@3c882f0801b3e6b00ebd86dc13da0f5b5d7c38b8`;
- feature CI `34756782788`: success.

### P-COMP-07

- theorem `UEOT.V3.CompositionWindow.p_comp_07`;
- compact interval, continuous monotone/antitone diagnostics, nonempty threshold
  sets, attained boundaries derived from compactness/closedness, interval-or-empty
  joint feasible set;
- no extra boundary-witness assumption;
- feature `formal/pcomp07-composition-window@76401f58d3877e8326e8417b7e56c9b4bf79b12b`;
- feature CI `34756769679`: success.

Joint lifecycle:
- clean integration branch `formal/ali02-comp07-main-integration`;
- integration/main proof commit `5f9a36d25c5e35fafe5379a5a2ff47b14e77cce8`;
- integration CI `34757135510`: success;
- safe non-force main fast-forward;
- post-main CI `34757507969`: success;
- prohibited-proof audits clean.

## Integration-ready lane — P-COMP-04

Frozen source: with side information `(C_{1:m},U)`, exact sufficiency/minimality
gives a deterministic parent core `C_P = g(M_P,U)`, hence
`H(C_P | C_{1:m},U) ≤ H(M_P | C_{1:m},U)`.

- branch `formal/pcomp04-parent-info`;
- head `d7b3446dcac54f62f7d28a141dd8649793b2586c`;
- theorem `UEOT.V3.CompositionParentInformation.p_comp_04`;
- feature CI `34757571535`: success;
- source-facing map deliberately cannot depend on child-core tuple `S`;
- finite alphabets make the frozen finite-conditional-entropy condition automatic;
- next action: prohibited-proof final audit, then clean-port theorem file plus one
  top-level import onto the latest full-green main.

## Active proof lane — P-KL-03

Frozen source: same initial law; finite horizon; possibly history-dependent
discrete kernels; rowwise absolute continuity; exact path-space KL chain rule.

- branch `formal/pkl03-path-chain`;
- current head `e4a242c18a7448fd0352f8284b36a0d608094a8b`;
- candidate `UEOT.V3.PathKLChain.p_kl_03`;
- CI `34757721974`: in progress at synchronization;
- current implementation uses Ionescu--Tulcea finite prefixes,
  `klDiv_compProd_eq_add`, and the UEOT kernel-KL lintegral bridge;
- do not replace by one-step or homogeneous-Markov semantics.

## Source audit lane — P-EVO-02

Frozen target:
`I((F,T);(F',T)) = I(F;F') + H(T)` for finite `T` independent of `(F,F')`
and copied without error. Reuse existing deterministic-copy/product/KL chain
infrastructure before adding new foundations.

## Grounded non-quick fronts

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron--Frobenius asymptotics / martingale foundations.
- P-REF-03: arbitrary signal-space conditional expectation.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/03/04: source-locked distinct non-A results.
- P-BRG-01: includes extinction/concentration/maximizer-relative-mass clauses.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56, `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent audit/proof lane.
