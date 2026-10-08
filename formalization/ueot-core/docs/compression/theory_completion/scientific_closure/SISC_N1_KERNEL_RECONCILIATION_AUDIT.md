# N1.3 — reconciliation: P-ALG and reachable stochastic prediction quotient

`SISCModelKernelReconciliation.lean` provides an exact bridge between two
coexisting finite controlled stochastic models in the public UEOT library:

1. `UEOT.V3.FiniteStablePartition.Model` (P-ALG-01), with a quotient
   specified as a `Setoid` and transition `blockMass`;
2. `FiniteControlledStochasticKernel` and `StrongLumpability`, with an
   arbitrary observation representation `q : X → Q` and finite transition
   `massIntoClass` on its reachable image.

The bridge constructs a concrete `Model → FiniteControlledStochasticKernel`
conversion, specialized representation `x ↦ Quotient.mk S x`, and proves for
every source x, destination representative z and action a:

`massIntoClass (modelAsFiniteKernel M) q x a (toReachable q z)`
`= blockMass M S a x z`.

This establishes a true semantic identity of transition masses, not simply
a similarity between definitions, and proves

`StrongLumpability (modelAsFiniteKernel M) q ↔ Stable M S`.

The final theorem exposes both unique quotient kernels simultaneously, by
reusing the established P-ALG quotient and the generic input-fibre descent.

What it does not do: prove that the source process's **evidence-relative
response equivalence** is stable, identify physical ontology, or infer the
candidate partition. Those require separate observational identifiability
and causal calibration, pursued in N1.2.

No frozen Core theorems or previously released P-ALG source files are edited.
