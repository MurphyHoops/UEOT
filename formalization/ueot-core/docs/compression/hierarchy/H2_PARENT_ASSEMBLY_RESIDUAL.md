# Track H — H2 Parent-Object Assembly Residual

Status: **H2 ACTIVE / RESEARCH / UNCOUNTED**

Authority:
- parent mission: Issue #146;
- Track H tracker: Issue #197;
- current H2 base: `main@996b5f2488526230f927e0a804884dc070a9b085`;
- H0/H1 evidence: canonical merged main only;
- counted-core impact: **NONE**.

## Question

Can genuine multi-input parent formation

`(O₁,...,Oₘ, interface/environment) -> O_parent`

be reconstructed from existing G0/G1/G2 architecture without assuming the
parent-specific certificates that frozen P-COMP already takes as inputs?

## Existing hierarchy-lift mechanism is not residual

M-QD already proves, for a surjective coarse representation `q`:

`FiberCompatible q g ↔ ∃! gbar, gbar ∘ q = g`.

Therefore a common-witness/refinement span needs no new primitive when the high
leg is constant on fibres of the low leg. Compatible hierarchy lifts are
already M-QD-derived.

The H2 residual begins where parent information is not determined by
child/coarse fibres or where extra assembly data are separately supplied.

## Frozen source signatures

### P-COMP-01 — path integration
Supplied input: one common joint probability law
`ρ : Measure (U × (∀ i, X i))`.

Proven output: nonnegative partition information, zero iff conditional
factorization, and positive finite integration margin iff no nontrivial
partition factorizes.

H2 reading: the common joint law is assumed, not reconstructed from child
marginals.

### P-COMP-02 — intervention / cut margin
Supplied input: observational law `P` and declared cut laws `Pcut`.

Proven output: positive finite JS cut margin iff every declared cut changes the
declared record law.

H2 reading: intervention/cut semantics are assumed.

### P-COMP-03 — composition-margin robustness
Supplied input: cut maps plus Lipschitz certificates.

Proven output: a Lipschitz bound for the already defined composition margin.

H2 reading: this transports supplied diagnostics; it is not a constructor.

### P-COMP-04 — parent predictive information
Supplied input: a parent representation `M`, a law on `((S×U)×M)`, and a
measurable parent-core map `g : M×U -> C`.

Proven output: the conditional parent-core entropy bound.

H2 reading: the parent representation/core map are inputs.

### P-COMP-05 — overlap geometry
Supplied input: declared overlapping regions.

Proven output: the unique least generated Boolean algebra and its atoms.

H2 reading: this canonicalizes overlap geometry, not predictive parent
formation.

### P-COMP-06 — carrier lift
Supplied input: child regions and a physical minimal-carrier family.

Proven output: exact equality between the child minimal family and the lifted
minimal-cover family.

H2 reading: physical carrier semantics are inputs.

### P-COMP-07 — composition window
Supplied input: integration/fidelity diagnostics, monotonicity/continuity,
compact coupling interval and feasibility assumptions.

Proven output: the exact joint feasibility window.

H2 reading: the diagnostics/window assumptions are inputs.

### Already existing architecture that is not residual
- P-OMG-01/02: retained causal-integrity machinery;
- P-CORE-01: G2 assembly of already certified operational ports;
- AgencyGodGoaAssembly: supplied history-derived state -> GOD/closed-loop/GOA.

None of these is a multi-child parent constructor.

## Machine-checked separation evidence

The module `Hierarchy.ParentAssemblyResidual` exposes exactly three public
theorems.

### 1. `commonWitness_not_hierarchyLift`

Finite witness:
- witness space: `Bool × Bool`;
- low state: `Prod.fst`;
- high state: `id`.

No `Bool -> Bool×Bool` lift reconstructs the high state from the low state.
The proof uses M-QD `fiberCompatible_of_comp_eq`.

Scientific meaning: a span is weaker than a hierarchy arrow unless fibre
compatibility holds.

### 2. `childConsistency_does_not_determine_unique_parent`

There exist two distinct parent completions with exactly the same child
projection.

Scientific meaning: child consistency constrains parent candidates but does
not canonically choose one.

### 3. `same_child_marginals_different_joint`

There exist two distinct finite joint PMFs with exactly the same two child
marginals.

Scientific meaning: child laws/marginals do not determine the common joint law
required by P-COMP-01.

## Synthesis

The three mechanisms expose one abstract pattern:

> Forgetful maps from richer parent/assembly data to child/coarse data need not
> be injective or invertible.

Existing child/coarse data therefore identify a fibre of possible lifts or
extensions. Additional assembly certificates select or justify a point in that
fibre.

H2 classification:

**RESIDUAL_OPEN relative to current G0/G1/G2:** non-canonical
lift/extension/binding data are required to justify a parent object when the
needed parent information is not already fibre-compatible or determined by
child data.

This is a residual obligation, not primitive promotion.

## Architecture classification

- theorem evidence: **G3** separation / boundary;
- H2 synthesis: **SYNTHESIS_ONLY**;
- lifecycle on branch: **RESEARCH**;
- lifecycle after accepted merge: **MERGED_UNCOUNTED**;
- track owner: **H**;
- theorem provenance on branch: **POST_FINAL_RESEARCH**;
- frozen source provenance: **FROZEN_CORE_V3**;
- counted-core impact: **NONE**.

## Explicit nonclaims

H2 does not claim:
- no conceivable parent constructor can exist;
- one universal parent operator exists;
- `CommonWitness`, `Assembly`, or `HierarchyLift` is a new primitive;
- P-OMG causal-integrity machinery is residual;
- P-CORE or Agency->GOD->GOA already solves parent formation;
- a fifth counted generator is justified;
- any frozen P-ID lifecycle changes;
- 4 -> 3, 4 -> 4, or 4 -> 5.

A future primitive-promotion case requires a separate lifecycle with
independent-family reuse, out-of-sample derivation power,
deletion/nonredundancy evidence, Lean proof, exact-head CI, independent
semantic review, ledger changes and re-finalization.
