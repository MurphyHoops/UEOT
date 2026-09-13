# UEOT Core 3 Lean — Pinned API Notes

> Small operational knowledge base for Lean 4.33.1 + Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Record only facts learned from real compilation/proof work. This file exists to prevent repeated CI waste.

## Environment

- Lean: `4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official build: `lake build UEOT`

## Conditional distributions / disintegration

### Reconstruct a measure from its disintegration

Working idiom used in the P-INFO-03 chain:

```lean
have hreconstruct : ρ.fst ⊗ₘ conditionalJointKernel ρ = ρ := by
  unfold conditionalJointKernel
  exact Measure.disintegrate ρ ρ.condKernel
```

### Conditional-kernel uniqueness

For product/joint laws in P-INT-01, prefer the already working disintegration / conditional-kernel uniqueness route from the UEOT codebase instead of guessing theorem names such as `Measure.condKernel_compProd` that are not available under the pinned Mathlib API.

Search existing UEOT code for the proved uniqueness lemma before adding new foundational infrastructure.

## Conditional independence

Useful pinned theorem in the P-INT-01 architecture:

`condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`

This is the main bridge between conditional independence and equality of conditional distributions on the product conditioning variable.

## Kernel.prodMkRight

Pinned elaboration was more reliable with explicit argument order, e.g.:

```lean
Kernel.prodMkRight H q0
```

rather than relying on ambiguous method-style inference such as:

```lean
q0.prodMkRight H
```

which produced anonymous measurable-space inference failures during P-INT-01 development.

## Standard Borel assumptions

For source-facing regular-conditional / Markov-kernel statements, check Standard-Borel instances explicitly. In P-INT-01 the structured `M` and `U` spaces needed the corresponding Standard-Borel assumptions.

Do not solve missing instances by silently weakening the source theorem to finite/countable spaces unless the frozen source actually has that scope.

## `rw` / simplification failures

Several P-INFO-03 / P-INT-01 CI failures were caused by a tactic continuing after an earlier `rw`/`congr` had already closed the goal. When Lean reports `No goals to be solved`, inspect whether the previous tactic completed the goal before adding more rewrites.

Conversely, after `map_map` or similar measure-map rewrites, a definitional `rfl` may be the correct final closure rather than another API lemma.

## Random encoder geometry

P-INFO-03 encodes genuinely randomized encoders as Markov kernels. Do not regress to deterministic statistics for source theorems that allow random encoders.

The source-marginal/conditional invariance stack already exists in main; reuse it instead of rebuilding conditional-information foundations.

## PredictionAE

Main already contains common-factorization/common-version prediction infrastructure (`PredictionAE`). P-INT-01 common-protocol formalization should reuse it rather than introducing a parallel intervention-family null-set framework.

## Development rule

Before spending a full GitHub CI cycle on an uncertain API name:

1. search the current repo;
2. search pinned Mathlib source/theorems;
3. run a module-level check where possible;
4. record the confirmed API here if it is likely to recur.
