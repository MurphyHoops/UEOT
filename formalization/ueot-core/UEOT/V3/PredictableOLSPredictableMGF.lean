import UEOT.V3.PredictableOLSMultiplier
import Mathlib.Tactic

/-!
# P-INV-05 — predictable multiplier MGF bridge

This module isolates the algebraic/probabilistic heart of the remaining source
bridge.  It assumes two ingredients proved independently:

* the predictable coefficient is frozen on almost every conditional fibre;
* the exponential of the product is globally integrable.

From these, a conditional sub-Gaussian bound for `X` with proxy `c` is
transported to `A * X` with proxy `B^2 c` whenever `|A| ≤ B`.
-/

namespace UEOT.V3.PredictableOLSPredictableMGF

open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal

universe uΩ

variable {Ω : Type uΩ} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Conditional sub-Gaussianity is preserved by a bounded predictable random
multiplier once the coefficient is frozen on conditional fibres. -/
theorem hasCondSubgaussianMGF_predictable_mul_of_freeze
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (A X : Ω → ℝ) (B : ℝ)
    (hB0 : 0 ≤ B)
    (hbound : ∀ ω, |A ω| ≤ B)
    {c : ℝ≥0}
    (hX : HasCondSubgaussianMGF m hm X c μ)
    (hfreeze : ∀ᵐ ω ∂(μ.trim hm),
      ∀ᵐ y ∂(condExpKernel (mΩ := mΩ) μ m ω), A y = A ω)
    (hint : ∀ t : ℝ, Integrable (fun ω => exp (t * (A ω * X ω))) μ) :
    HasCondSubgaussianMGF m hm (fun ω => A ω * X ω)
      (Real.toNNReal (B ^ 2) * c) μ := by
  unfold HasCondSubgaussianMGF
  refine
    { integrable_exp_mul := ?_
      mgf_le := ?_ }
  · intro t
    rw [condExpKernel_comp_trim (mΩ := mΩ) (μ := μ) hm]
    exact hint t
  · filter_upwards [hX.mgf_le, hfreeze] with ω hmgf hfreeze
    intro t
    have hprod :
        (fun y => A y * X y) =ᵐ[condExpKernel (mΩ := mΩ) μ m ω]
          (fun y => A ω * X y) := by
      filter_upwards [hfreeze] with y hy
      rw [hy]
    rw [mgf_congr hprod, mgf_const_mul]
    calc
      mgf X (condExpKernel (mΩ := mΩ) μ m ω) (A ω * t)
          ≤ exp ((c : ℝ) * (A ω * t) ^ 2 / 2) := hmgf _
      _ ≤ exp ((((Real.toNNReal (B ^ 2)) * c : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        have hsq : (A ω) ^ 2 ≤ B ^ 2 := by
          rw [sq_le_sq]
          simpa [abs_of_nonneg hB0] using hbound ω
        rw [NNReal.coe_mul, Real.coe_toNNReal (B ^ 2) (sq_nonneg B)]
        calc
          (c : ℝ) * (A ω * t) ^ 2 / 2
              = ((c : ℝ) * (A ω) ^ 2) * t ^ 2 / 2 := by ring
          _ ≤ ((c : ℝ) * B ^ 2) * t ^ 2 / 2 := by
            gcongr
          _ = (B ^ 2 * (c : ℝ)) * t ^ 2 / 2 := by ring

end UEOT.V3.PredictableOLSPredictableMGF
