import UEOT.V3.PredictableOLSScore
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Tactic

/-!
# P-INV-05 — predictable multiplier bridge

This module isolates the remaining source-facing probability bridge for the
predictable-design OLS theorem.

The first two reusable ingredients are:

1. monotonicity of the sub-Gaussian variance proxy;
2. freezing a measurable function under conditioning on the variable that
   determines it: the conditional law of `f X` given `X` is deterministic.

The next theorem in this module will specialize the second fact to
`condExpKernel` and use it to turn a predictable random multiplier into a
constant on each conditional fiber.
-/

namespace UEOT.V3.PredictableOLSMultiplier

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

/-- A sub-Gaussian MGF bound remains valid when its variance proxy is enlarged. -/
theorem hasSubgaussianMGF_mono_param
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {c c' : ℝ≥0}
    (h : Kernel.HasSubgaussianMGF X c κ ν) (hcc : c ≤ c') :
    Kernel.HasSubgaussianMGF X c' κ ν := by
  refine
    { integrable_exp_mul := h.integrable_exp_mul
      mgf_le := ?_ }
  filter_upwards [h.mgf_le] with ω hω
  intro t
  calc
    mgf X (κ ω) t ≤ exp ((c : ℝ) * t ^ 2 / 2) := hω t
    _ ≤ exp ((c' : ℝ) * t ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      have hc : (c : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hcc
      nlinarith [sq_nonneg t]

/-- If we condition on `X`, then applying any measurable function `f` to the
conditional copy of `X` gives the deterministic kernel concentrated at `f X`.

This is the abstract "freeze the predictable coefficient on the conditional
fiber" fact used by the P-INV-05 source proof. -/
theorem condDistrib_self_map
    {α β γ : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    {μ : Measure α} [IsFiniteMeasure μ]
    (X : α → β) (hX : AEMeasurable X μ)
    (f : β → γ) (hf : Measurable f) :
    (condDistrib X X μ).map f =ᵐ[μ.map X] Kernel.deterministic f hf := by
  have hcomp := condDistrib_comp (μ := μ) (Y := X) X hX hf
  have hself := condDistrib_comp_self (μ := μ) X hf
  exact hcomp.symm.trans hself

end UEOT.V3.PredictableOLSMultiplier
