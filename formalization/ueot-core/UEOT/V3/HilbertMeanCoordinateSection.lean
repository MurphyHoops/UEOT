import UEOT.V3.HilbertMeanConcentration

/-!
# P-STAT-06 — active-coordinate RKHS sections

The frozen McDiarmid proof varies one sample coordinate while all other
coordinates, including any particular realization of the unrevealed future,
are held fixed. This file packages the source statistic as such a one-coordinate
section and proves the exact `2/N` pairwise oscillation bound uniformly in the
fixed background configuration.
-/

namespace UEOT.V3.HilbertMeanCoordinateSection

open UEOT.V3.HilbertMeanConcentration

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Replace the active sample coordinate and evaluate the RKHS empirical-mean
error against the fixed target mean. -/
noncomputable def coordinateErrorSection {N : ℕ}
    (base : Fin N → H) (i : Fin N) (μ : H) (v : H) : ℝ :=
  ‖empiricalMean (Function.update base i v) - μ‖

/-- Uniform source-facing bounded difference: for every fixed configuration of
all non-active coordinates, any two admissible values of the active feature
produce statistic values differing by at most exactly `2/N`. -/
theorem coordinateErrorSection_pairwise_le_two_div
    {N : ℕ} (hN : 0 < N)
    (base : Fin N → H) (i : Fin N) (μ : H)
    (a b : H)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |coordinateErrorSection base i μ a - coordinateErrorSection base i μ b| ≤
      2 / (N : ℝ) := by
  unfold coordinateErrorSection
  apply abs_norm_sub_mean_diff_le_two_div hN
      (Function.update base i a) (Function.update base i b) i
  · intro j hji
    simp [Function.update, hji]
  · simpa [Function.update_same] using ha
  · simpa [Function.update_same] using hb

/-- If the active-coordinate feature space is uniformly norm-bounded by one,
the entire active-coordinate section has pairwise oscillation `2/N`. -/
theorem coordinateErrorSection_pairwise_uniform
    {N : ℕ} (hN : 0 < N)
    (base : Fin N → H) (i : Fin N) (μ : H)
    (hunit : ∀ v : H, ‖v‖ ≤ 1) :
    ∀ a b : H,
      |coordinateErrorSection base i μ a - coordinateErrorSection base i μ b| ≤
        2 / (N : ℝ) := by
  intro a b
  exact coordinateErrorSection_pairwise_le_two_div hN base i μ a b (hunit a) (hunit b)

end UEOT.V3.HilbertMeanCoordinateSection
