import UEOT.V3.PredictableOLSTail
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# P-INV-05 — exact score threshold inversion

This module closes the finite-dimensional tail arithmetic once every coordinate
of the predictable-design score vector is known to be sub-Gaussian with
variance proxy `N * (sigma * B)^2`.
-/

namespace UEOT.V3.PredictableOLSRadius

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.PredictableOLSTail
open scoped NNReal

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω]

/-- Variance proxy of one OLS score coordinate after summing `N` predictable
increments, each with proxy `(sigma * B)^2`. -/
noncomputable def scoreParam (N : ℕ) (sigma B : ℝ) : ℝ≥0 :=
  ⟨(N : ℝ) * (sigma * B) ^ 2,
    mul_nonneg (Nat.cast_nonneg N) (sq_nonneg (sigma * B))⟩

/-- Frozen P-INV-05 coordinate threshold. -/
noncomputable def scoreRadius (N d : ℕ) (sigma B alpha : ℝ) : ℝ :=
  sigma * B * sqrt (2 * (N : ℝ) * log ((2 * (d : ℝ)) / alpha))

/-- Exact inversion of the two-sided `d`-coordinate union tail. -/
theorem raw_score_union_tail_eq_alpha
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {sigma B alpha : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    (d : ℝ) *
        (2 * exp
          (-(scoreRadius N d sigma B alpha) ^ 2 /
            (2 * (scoreParam N sigma B : ℝ)))) = alpha := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdreal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdoneNat : 1 ≤ d := Nat.succ_le_iff.mpr hd
  have hdone : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdoneNat
  have hratio_pos : 0 < (2 * (d : ℝ)) / alpha := by positivity
  have hratio_one : 1 ≤ (2 * (d : ℝ)) / alpha := by
    rw [le_div_iff₀ halpha0]
    have htwo_d : (1 : ℝ) ≤ 2 * (d : ℝ) := by nlinarith
    exact halpha1.trans htwo_d
  have hlog : 0 ≤ log ((2 * (d : ℝ)) / alpha) := Real.log_nonneg hratio_one
  have hrad : 0 ≤ 2 * (N : ℝ) * log ((2 * (d : ℝ)) / alpha) := by positivity
  have hexponent :
      -(scoreRadius N d sigma B alpha) ^ 2 /
          (2 * (scoreParam N sigma B : ℝ)) =
        -log ((2 * (d : ℝ)) / alpha) := by
    unfold scoreRadius scoreParam
    simp only [NNReal.coe_mk]
    rw [mul_pow, Real.sq_sqrt hrad]
    have hsigma0 : sigma ≠ 0 := ne_of_gt hsigma
    have hB0 : B ≠ 0 := ne_of_gt hB
    have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNreal
    field_simp [hsigma0, hB0, hN0]
    ring
  rw [hexponent, Real.exp_neg, Real.exp_log hratio_pos]
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdreal
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha0
  field_simp [hd0, halpha_ne]

/-- At the frozen P-INV-05 score threshold, the probability that any score
coordinate exceeds the threshold is at most `alpha`. -/
theorem measure_exists_score_coord_gt_le_alpha
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin d → Ω → ℝ)
    {sigma B alpha : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hZ : ∀ j, HasSubgaussianMGF (Z j) (scoreParam N sigma B) μ) :
    μ.real {ω | ∃ j : Fin d,
      scoreRadius N d sigma B alpha < |Z j ω|} ≤ alpha := by
  have hR : 0 ≤ scoreRadius N d sigma B alpha := by
    unfold scoreRadius
    positivity
  have htail := measure_exists_coord_abs_gt_le
    μ Z hZ hR
  exact htail.trans_eq
    (raw_score_union_tail_eq_alpha hN hd hsigma hB halpha0 halpha1)

end UEOT.V3.PredictableOLSRadius
