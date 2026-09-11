import UEOT.V3.HilbertMeanSecondMoment
import Mathlib.Probability.Moments.Variance

/-!
# P-STAT-06 — first-moment bridge

This module isolates the Jensen/Cauchy–Schwarz step used by the frozen
P-STAT-06 proof. On a probability space, the first moment of a real random
variable is at most the square root of its second moment. We derive this from
nonnegativity of variance, so no constant is lost.
-/

namespace UEOT.V3.HilbertMeanFirstMoment

open MeasureTheory ProbabilityTheory

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω]

/-- Probability-space first/second-moment bridge with the exact constant one:
`E[X] ≤ sqrt(E[X²])`. This is the scalar form needed after applying the norm
to the centered Hilbert empirical mean. -/
theorem integral_le_sqrt_integral_sq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hX : AEStronglyMeasurable X μ)
    (hXsq : Integrable (fun ω => X ω ^ 2) μ) :
    (∫ ω, X ω ∂μ) ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂μ) := by
  have hmem : MemLp X 2 μ :=
    (memLp_two_iff_integrable_sq hX).2 hXsq
  have hvar : 0 ≤ variance X μ := variance_nonneg X μ
  rw [variance_eq_sub hmem] at hvar
  have hsq :
      (∫ ω, X ω ∂μ) ^ 2 ≤ ∫ ω, X ω ^ 2 ∂μ :=
    sub_nonneg.mp hvar
  exact Real.le_sqrt_of_sq_le hsq

end UEOT.V3.HilbertMeanFirstMoment
