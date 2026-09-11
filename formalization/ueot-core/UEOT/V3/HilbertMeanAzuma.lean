import UEOT.V3.HilbertMeanFirstMoment
import Mathlib.Probability.Moments.SubGaussian

/-!
# P-STAT-06 — Azuma tail layer

This file isolates the exact pinned-Mathlib Azuma theorem and the constant
normalization required by the frozen P-STAT-06 proof.  The source
bounded-difference constant is `2/N`; Hoeffding therefore assigns each Doob
increment the sub-Gaussian variance proxy `(2/N)^2 / 4 = 1/N^2`.
-/

namespace UEOT.V3.HilbertMeanAzuma

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

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
    (h_subG : ∀ (i : ℕ), i < n - 1 →
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by
  exact measure_sum_ge_le_of_hasCondSubgaussianMGF h_adapted h0 n h_subG hε

/-- The per-coordinate variance proxy induced by a `2/N` bounded difference. -/
def invSqParam (N : ℕ) : ℝ≥0 :=
  ((N : ℝ≥0)⁻¹) ^ 2

/-- Exact constant normalization used by frozen P-STAT-06: summing `N` copies
of `1/N²` gives `1/N`. -/
theorem coe_sum_invSqParam_eq_one_div
    {N : ℕ} (hN : 0 < N) :
    (((∑ _i ∈ Finset.range N, invSqParam N : ℝ≥0) : ℝ)) =
      1 / (N : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  rw [NNReal.coe_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp [invSqParam, NNReal.coe_inv]
  field_simp [hN0]

end UEOT.V3.HilbertMeanAzuma
