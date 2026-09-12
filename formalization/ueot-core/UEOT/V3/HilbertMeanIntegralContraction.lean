import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# P-STAT-06 — averaging preserves bounded differences

The Doob/McDiarmid bridge repeatedly averages a bounded-difference statistic
over unrevealed independent coordinates.  Probability averaging must not
increase a one-coordinate oscillation.  This file isolates that deterministic
integral contraction step.
-/

namespace UEOT.V3.HilbertMeanIntegralContraction

open MeasureTheory Real

universe uα

variable {α : Type uα} [MeasurableSpace α]

/-- Under a probability measure, integration is 1-Lipschitz for an a.e.
uniform scalar difference bound. -/
theorem abs_integral_sub_integral_le_const
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f g : α → ℝ} {c : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ᵐ x ∂μ, |f x - g x| ≤ c) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ c := by
  have hbound : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ c := by
    filter_upwards [hfg] with x hx
    simpa [Real.norm_eq_abs] using hx
  have hmass : μ.real Set.univ = 1 := by
    simp [Measure.real]
  have hnorm : ‖∫ x, (f x - g x) ∂μ‖ ≤ c := by
    have hraw := norm_integral_le_of_norm_le_const (μ := μ) hbound
    simpa [hmass] using hraw
  rw [integral_sub hf hg] at hnorm
  simpa [Real.norm_eq_abs] using hnorm

/-- Pointwise bounded difference therefore survives averaging over any
probability-distributed nuisance/future coordinate. -/
theorem abs_integral_section_sub_integral_section_le
    {β : Type*} (μ : Measure α) [IsProbabilityMeasure μ]
    (F : β → α → ℝ) {x y : β} {c : ℝ}
    (hx : Integrable (F x) μ) (hy : Integrable (F y) μ)
    (hxy : ∀ᵐ z ∂μ, |F x z - F y z| ≤ c) :
    |(∫ z, F x z ∂μ) - ∫ z, F y z ∂μ| ≤ c := by
  exact abs_integral_sub_integral_le_const μ hx hy hxy

end UEOT.V3.HilbertMeanIntegralContraction
