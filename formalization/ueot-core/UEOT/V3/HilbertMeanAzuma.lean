import UEOT.V3.HilbertMeanFirstMoment
import Mathlib.Probability.Moments.SubGaussian

/-!
# P-STAT-06 — Azuma tail layer

This file intentionally isolates the exact Mathlib Azuma theorem before adding
any constant-parameter normalization.  The source-level specialization and the
bounded-difference/Doob bridge are added only after this imported core is green.
-/

namespace UEOT.V3.HilbertMeanAzuma

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Stable wrapper around Mathlib's conditional-sub-Gaussian Azuma bound. -/
theorem azuma_parameterized
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ}
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {cY : ℕ → ℝ≥0}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ)
    (n : ℕ)
    (h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by
  exact measure_sum_ge_le_of_hasCondSubgaussianMGF h_adapted h0 n h_subG hε

end UEOT.V3.HilbertMeanAzuma
