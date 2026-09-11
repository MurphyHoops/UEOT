import UEOT.V3.HilbertMeanFirstMoment
import Mathlib.Probability.Moments.SubGaussian

/-!
# P-STAT-06 — exact Azuma tail layer

This module isolates the final concentration algebra used by the frozen proof.
Once a coordinate-exposure Doob difference process has conditional sub-Gaussian
parameter `1/N^2` at each of its `N` increments, Mathlib's Azuma-Hoeffding
inequality gives exactly `exp (-N * eps^2 / 2)`.

The separate bounded-difference-to-Doob-increment bridge remains an explicit
obligation; this file does not assume McDiarmid as a black box.
-/

namespace UEOT.V3.HilbertMeanAzuma

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Constant-parameter specialization of Mathlib's conditional-sub-Gaussian
Azuma bound. -/
theorem azuma_constant_parameter
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration ℕ _}
    (h_adapted : StronglyAdapted ℱ Y)
    {c : ℝ≥0}
    (h0 : HasSubgaussianMGF (Y 0) c μ)
    (n : ℕ)
    (h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) c μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ Real.exp (-ε ^ 2 / (2 * n * c)) := by
  have h := measure_sum_ge_le_of_hasCondSubgaussianMGF
    (μ := μ) (cY := fun _ => c) h_adapted h0 n (by simpa using h_subG) hε
  simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc] using h

/-- If there are exactly `N` Doob increments and each has sub-Gaussian
parameter `1/N^2`, the exponent is the frozen P-STAT-06 constant
`-N*eps^2/2`. -/
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
  have h := azuma_constant_parameter
    (μ := μ) h_adapted h0 N (by simpa using h_subG) hε
  convert h using 1
  · rfl
  · congr 1
    field_simp
    ring

end UEOT.V3.HilbertMeanAzuma
