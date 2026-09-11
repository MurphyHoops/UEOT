import UEOT.V3.HilbertMeanFirstMoment
import Mathlib.Probability.Moments.SubGaussian

/-!
# P-STAT-06 — Azuma tail layer

Mathlib supplies the conditional sub-Gaussian Azuma-Hoeffding inequality with
variance proxy `sum_i c_i`.  This module first exposes that theorem without
algebraic rewriting, then proves the P-STAT-06 specialization for `N` increments
with parameter `1/N^2` each.

The bounded-difference-to-Doob-increment bridge remains a separate obligation.
-/

namespace UEOT.V3.HilbertMeanAzuma

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Thin stable wrapper around Mathlib's conditional-sub-Gaussian Azuma bound. -/
theorem azuma_parameterized
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration ℕ _} {cY : ℕ → ℝ≥0}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ)
    (n : ℕ)
    (h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by
  exact measure_sum_ge_le_of_hasCondSubgaussianMGF h_adapted h0 n h_subG hε

/-- With exactly `N` increments and sub-Gaussian parameter `1/N^2` for each,
Azuma gives the frozen P-STAT-06 scalar tail `exp (-N*eps^2/2)`. -/
theorem azuma_one_div_N_sq
    {N : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration ℕ _}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : HasSubgaussianMGF (Y 0)
      ⟨1 / (N : ℝ) ^ 2, by positivity⟩ μ)
    (h_subG : ∀ i < N - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1))
        ⟨1 / (N : ℝ) ^ 2, by positivity⟩ μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range N, Y i ω}
      ≤ Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
  let cN : ℝ≥0 := ⟨1 / (N : ℝ) ^ 2, by positivity⟩
  have hNreal : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have h := azuma_parameterized
    (μ := μ) (cY := fun _ => cN) h_adapted
    (by simpa [cN] using h0) N (by simpa [cN] using h_subG) hε
  have hsum :
      (↑(∑ i ∈ Finset.range N, cN) : ℝ) = 1 / (N : ℝ) := by
    simp [cN, Finset.sum_const, nsmul_eq_mul] <;>
      field_simp [hNreal] <;> ring
  calc
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range N, Y i ω}
        ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range N, cN)) := h
    _ = Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
      rw [hsum]
      congr 1
      field_simp [hNreal] <;> ring

end UEOT.V3.HilbertMeanAzuma
