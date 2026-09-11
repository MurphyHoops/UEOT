import UEOT.V3.PredictableOLS
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# P-INV-05 — coordinate sub-Gaussian tail layer

This module isolates the probability step after the predictable-design score
coordinates have been shown to be sub-Gaussian. It proves a two-sided tail for
one coordinate and a finite-dimensional union bound over all `d` coordinates.

The remaining source-specific bridge is to derive the coordinate
sub-Gaussian hypothesis from predictable multipliers and conditionally
sub-Gaussian noise with the exact parameter `N * (sigma * B)^2`.
-/

namespace UEOT.V3.PredictableOLSTail

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω]

/-- A centered sub-Gaussian scalar has the standard two-sided tail with the
same variance proxy. -/
theorem measure_abs_gt_le_of_hasSubgaussianMGF
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ)
    {R : ℝ} (hR : 0 ≤ R) :
    μ.real {ω | R < |X ω|} ≤
      2 * exp (-R ^ 2 / (2 * c)) := by
  let upper : Set Ω := {ω | R ≤ X ω}
  let lower : Set Ω := {ω | R ≤ -X ω}
  have hbad : {ω | R < |X ω|} ⊆ upper ∪ lower := by
    intro ω hω
    change R < |X ω| at hω
    change ω ∈ upper ∪ lower
    by_cases hx : 0 ≤ X ω
    · left
      change R ≤ X ω
      rw [abs_of_nonneg hx] at hω
      exact hω.le
    · right
      have hx' : X ω < 0 := lt_of_not_ge hx
      change R ≤ -X ω
      rw [abs_of_neg hx'] at hω
      exact hω.le
  have hupper : μ.real upper ≤ exp (-R ^ 2 / (2 * c)) := by
    simpa [upper] using hX.measure_ge_le hR
  have hlower : μ.real lower ≤ exp (-R ^ 2 / (2 * c)) := by
    simpa [lower] using hX.neg.measure_ge_le hR
  calc
    μ.real {ω | R < |X ω|}
        ≤ μ.real (upper ∪ lower) := measureReal_mono hbad
    _ ≤ μ.real upper + μ.real lower := measureReal_union_le upper lower
    _ ≤ exp (-R ^ 2 / (2 * c)) + exp (-R ^ 2 / (2 * c)) :=
      add_le_add hupper hlower
    _ = 2 * exp (-R ^ 2 / (2 * c)) := by ring

/-- Finite-dimensional union bound for a family of sub-Gaussian score
coordinates. No independence between coordinates is required. -/
theorem measure_exists_coord_abs_gt_le
    {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin d → Ω → ℝ) {c : ℝ≥0}
    (hZ : ∀ j, HasSubgaussianMGF (Z j) c μ)
    {R : ℝ} (hR : 0 ≤ R) :
    μ.real {ω | ∃ j : Fin d, R < |Z j ω|} ≤
      (d : ℝ) * (2 * exp (-R ^ 2 / (2 * c))) := by
  have hset :
      {ω | ∃ j : Fin d, R < |Z j ω|} =
        ⋃ j : Fin d, {ω | R < |Z j ω|} := by
    ext ω
    simp
  rw [hset]
  calc
    μ.real (⋃ j : Fin d, {ω | R < |Z j ω|})
        ≤ ∑ j : Fin d, μ.real {ω | R < |Z j ω|} :=
          measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin d, (2 * exp (-R ^ 2 / (2 * c))) := by
      exact Finset.sum_le_sum fun j _ =>
        measure_abs_gt_le_of_hasSubgaussianMGF μ (Z j) (hZ j) hR
    _ = (d : ℝ) * (2 * exp (-R ^ 2 / (2 * c))) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]

/-- A convenient failure-probability wrapper: any threshold whose union-bound
right-hand side is at most `alpha` gives simultaneous coordinate control except
on an event of probability at most `alpha`. -/
theorem measure_exists_coord_abs_gt_le_alpha
    {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin d → Ω → ℝ) {c : ℝ≥0}
    (hZ : ∀ j, HasSubgaussianMGF (Z j) c μ)
    {R alpha : ℝ} (hR : 0 ≤ R)
    (hbudget : (d : ℝ) * (2 * exp (-R ^ 2 / (2 * c))) ≤ alpha) :
    μ.real {ω | ∃ j : Fin d, R < |Z j ω|} ≤ alpha := by
  exact (measure_exists_coord_abs_gt_le μ Z hZ hR).trans hbudget

end UEOT.V3.PredictableOLSTail
