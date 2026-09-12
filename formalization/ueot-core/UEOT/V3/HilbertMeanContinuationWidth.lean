import UEOT.V3.HilbertMeanIntegralContraction
import UEOT.V3.HilbertMeanRangeWidth

/-!
# P-STAT-06 — continuation values preserve bounded differences

A Doob continuation value is obtained by integrating the source statistic over
future/unrevealed coordinates.  Probability averaging is a contraction, so a
pointwise `c`-bounded oscillation in the currently revealed coordinate remains
`c`-bounded after all future coordinates are averaged out.  Combined with the
range-width bridge, centering by any common past-dependent value yields an
interval of the same width.
-/

namespace UEOT.V3.HilbertMeanContinuationWidth

open MeasureTheory

universe uα uβ

variable {α : Type uα} {β : Type uβ}
variable [MeasurableSpace α]

/-- Future averaging preserves the pairwise oscillation bound in the active
coordinate. -/
theorem continuation_pairwise_abs_sub_le
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : β → α → ℝ) {c : ℝ}
    (hint : ∀ x, Integrable (F x) μ)
    (hosc : ∀ x y, ∀ᵐ z ∂μ, |F x z - F y z| ≤ c) :
    ∀ x y,
      |(∫ z, F x z ∂μ) - ∫ z, F y z ∂μ| ≤ c := by
  intro x y
  exact HilbertMeanIntegralContraction.abs_integral_section_sub_integral_section_le
    μ F (hint x) (hint y) (hosc x y)

/-- The centered continuation value belongs to the interval determined by the
infimum and supremum of all active-coordinate continuation values. -/
theorem centered_continuation_mem_Icc
    [Nonempty β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : β → α → ℝ) {c m : ℝ}
    (hint : ∀ x, Integrable (F x) μ)
    (hosc : ∀ x y, ∀ᵐ z ∂μ, |F x z - F y z| ≤ c)
    (x : β) :
    (∫ z, F x z ∂μ) - m ∈ Set.Icc
      (sInf (Set.range (fun y : β => ∫ z, F y z ∂μ)) - m)
      (sSup (Set.range (fun y : β => ∫ z, F y z ∂μ)) - m) := by
  apply HilbertMeanRangeWidth.centered_mem_Icc_sInf_sSup
    (fun y : β => ∫ z, F y z ∂μ)
  exact continuation_pairwise_abs_sub_le μ F hint hosc

/-- The centered continuation interval has width at most the original
pointwise oscillation bound `c`. -/
theorem centered_continuation_interval_width_le
    [Nonempty β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : β → α → ℝ) {c m : ℝ}
    (hint : ∀ x, Integrable (F x) μ)
    (hosc : ∀ x y, ∀ᵐ z ∂μ, |F x z - F y z| ≤ c) :
    (sSup (Set.range (fun y : β => ∫ z, F y z ∂μ)) - m) -
      (sInf (Set.range (fun y : β => ∫ z, F y z ∂μ)) - m) ≤ c := by
  apply HilbertMeanRangeWidth.centered_interval_width_le
    (fun y : β => ∫ z, F y z ∂μ)
  exact continuation_pairwise_abs_sub_le μ F hint hosc

end UEOT.V3.HilbertMeanContinuationWidth
