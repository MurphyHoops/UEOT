# Parent Binding Mechanism — Interface Audit

Status: **LOCAL RESEARCH / NO REMOTE LIFECYCLE**

Baseline:

- canonical source base: `origin/main@5c62f2f1db479b9f0f8e725ced6588b59d0fe42d`;
- Track X #227 is already merged and green on that base;
- frozen counted core remains `{M-QD-01, M-TC-01, M-PE-01, M-OI-01}`;
- this local continuation intentionally performs no push, PR, Issue mutation,
  ledger mutation, or governance mutation.

## 1. Residual exposed by Track X

Track X proved that, once one has an explicit pairwise parent-kernel defect,
residual isolation converts that defect into long-run semantic stability:

`row kernel defect <= epsilon`

plus

`l1ResidualConorm >= kappa`

implies

`semantic defect <= epsilon / kappa`.

However, the same-child-fibre hypothesis in X3 is semantically important but
is not used numerically.  The missing bridge is therefore:

> why should richer parent completions compatible with the same lower-level
> evidence induce nearby parent dynamics?

This audit calls that missing bridge **parent binding regularity**.

## 2. Existing reusable surfaces

### Track X / Track S

Reused without modification:

- `suppliedInvariant_tracking`;
- `x3_parentSemanticTracking`;
- `x4_fiberSemanticDiameter`;
- `l1ResidualConorm` and the finite-state residual-isolation machinery.

### M-TC

Reused without modification:

- `TransportCertificate.weighted_chain_bound`;
- `development_pipeline_via_weighted_chain`.

The new dynamic parent-binding theorem is an adapter over this exact M-TC
surface; it introduces no new transport principle.

### P-COMP

The frozen P-COMP family was re-read before adding any parent-binding theorem.
Its source-facing roles remain heterogeneous:

- P-COMP-01: common conditional joint path law and partition integration;
- P-COMP-02: intervention/Jensen-Shannon separation;
- P-COMP-03: forward Lipschitz stability of a composition margin;
- P-COMP-04: conditional parent-core information inequality;
- P-COMP-05: Booleanization of overlapping regions;
- P-COMP-06: physical carrier -> minimal child coalition lift;
- P-COMP-07: feasible composition window.

None of those frozen theorem conclusions supplies either:

1. a metric diameter bound on the richer parent-completion fibre; or
2. a Lipschitz/inverse regularity theorem from parent assembly realization to
   the induced parent Markov kernel.

Therefore the missing Track-X `hrow` premise cannot honestly be deleted from
the frozen P-COMP source alone.

## 3. Chosen typed bridge

The local continuation introduces one uncounted domain bridge:

`ParentBindingLipschitz repr K hK`.

It contains only:

- a nonnegative sensitivity constant `L`;
- the rowwise inequality

  `crossRowTV (K p) (K q) <= L * dist (repr p) (repr q)`.

It does not contain:

- invariant laws;
- residual isolation;
- long-run semantic conclusions;
- child-fibre diameter;
- Objecthood, objective, selection, or fitness semantics.

Accordingly it is classified as a **domain regularity bridge**, not a G0
primitive.

## 4. Required no-go checks

Two separate no-go results are required before using the bridge.

### PB0 — P-COMP-06 validity is not dynamics identification

`pb0_pcompValidity_does_not_control_parent_semantics` constructs two parent
completions which:

- are both valid under one genuine P-COMP-06 assembly certificate;
- bind to the same child evidence;
- induce different parent kernels;
- have explicitly stationary invariant laws at TV distance exactly one.

Hence carrier validity alone cannot produce the Track-X dynamics defect.

### Diagnostic no-go — forward stability is not inverse identification

`p_comp_03_forward_stability_not_parent_identifiability` uses a legal
P-COMP-03 identity-cut example.  The P-COMP-03 forward Lipschitz theorem
applies, but the resulting composition margin is identically zero, so two
distinct richer parent states have exactly the same diagnostic value.

Hence forward diagnostic continuity alone cannot provide an inverse binding
metric or a parent-kernel realization law.

## 5. Positive static bridge

If one child-evidence fibre has assembly-space diameter at most `delta` and the
parent realization is row-TV Lipschitz with constant `L`, then

`parentRowDefect_of_binding`

generates the exact row-defect premise consumed by Track X:

`crossRowTV <= L * delta`.

With a uniform residual-isolation floor `kappaMin > 0`,

`parentSemanticDiameter_of_binding`

gives

`fiberSemanticDiameter <= (L * delta) / kappaMin`.

This is the intended static emergence-style theorem:

`assembly uncertainty × binding sensitivity / dynamical isolation`

controls higher-level long-run semantic uncertainty.

## 6. Dynamic bridge through M-TC

`assemblyDist_le_bindingTransportEnvelope` is a direct wrapper around
`development_pipeline_via_weighted_chain`.

`parentSemanticTracking_via_MTC` then composes:

1. M-TC assembly-error transport;
2. parent-binding Lipschitz realization;
3. Track-S residual isolation.

The resulting bound contains the exact M-TC weighted product/sum envelope.

`parentSemanticTracking_via_MTC_tendsto_zero` adds one explicit asymptotic
assumption: the generated M-TC envelope tends to zero.  Under a uniform
positive residual-isolation floor, long-run semantic TV distance then tends to
zero.

M-TC itself is **not** claimed to make the envelope vanish.

## 7. P-COMP specialization

`pcompSemanticDiameter_of_binding` strengthens Track-X X6 in one precise way:
the row-TV defect is no longer supplied directly.  It is generated from:

- a domain assembly-space diameter bound on P-COMP-valid richer parents; and
- `ParentBindingLipschitz`.

P-COMP still supplies only the admissible parent-completion family/binding
surface.  The metric diameter and realization regularity remain explicit
domain obligations.

## 8. Interface verdict

The local proof search does **not** justify an endogenous universal parent
formation theorem from frozen P-COMP alone.

It does justify a reusable typed chain:

`assembly defect`

-> `M-TC transport` (when dynamic)

-> `binding realization defect`

-> `parent-kernel defect`

-> `Track-S residual isolation`

-> `stable parent long-run semantics`.

The unresolved scientific quantity is therefore no longer the Track-X
`epsilon / kappa` step.  It is the **domain law that determines or bounds the
assembly metric and binding sensitivity `L` from concrete lower-level
physics/interaction evidence**.
