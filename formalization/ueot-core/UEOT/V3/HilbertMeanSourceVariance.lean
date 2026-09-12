import UEOT.V3.HilbertMeanFirstMoment
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P-STAT-06 — source marginal variance bound

For a Hilbert-valued probability law supported in the unit ball, centering by
its Bochner mean does not cost the crude factor two.  The exact identity

`E ‖X - EX‖² = E ‖X‖² - ‖EX‖²`

therefore gives the sharp bound `E ‖X - EX‖² ≤ 1` required by the frozen
P-STAT-06 first-moment constant.
-/

namespace UEOT.V3.HilbertMeanSourceVariance

open MeasureTheory ProbabilityTheory

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]

/-- Unit-ball support makes the identity map integrable. -/
theorem integrable_id_of_ae_norm_le_one
    (ν : Measure H) [IsProbabilityMeasure ν]
    (hunit : ∀ᵐ x ∂ν, ‖x‖ ≤ 1) :
    Integrable (fun x : H => x) ν := by
  exact Integrable.of_bound aestronglyMeasurable_id 1 hunit

/-- Unit-ball support gives an integrable raw squared norm with expectation at
most one. -/
theorem integral_norm_sq_le_one_of_ae_norm_le_one
    (ν : Measure H) [IsProbabilityMeasure ν]
    (hunit : ∀ᵐ x ∂ν, ‖x‖ ≤ 1) :
    Integrable (fun x : H => ‖x‖ ^ 2) ν ∧
      (∫ x : H, ‖x‖ ^ 2 ∂ν) ≤ 1 := by
  have hmeas : AEStronglyMeasurable (fun x : H => ‖x‖ ^ 2) ν := by
    fun_prop
  have hint : Integrable (fun x : H => ‖x‖ ^ 2) ν := by
    refine Integrable.of_bound hmeas 1 ?_
    filter_upwards [hunit] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
    nlinarith [norm_nonneg x]
  have hmono :
      (∫ x : H, ‖x‖ ^ 2 ∂ν) ≤ ∫ _x : H, (1 : ℝ) ∂ν := by
    refine integral_mono_ae hint (integrable_const 1) ?_
    filter_upwards [hunit] with x hx
    nlinarith [norm_nonneg x]
  simpa using And.intro hint hmono

/-- Exact Hilbert variance identity around the Bochner mean. -/
theorem integral_norm_sub_mean_sq_eq
    (ν : Measure H) [IsProbabilityMeasure ν]
    (μH : H)
    (hmean : (∫ x : H, x ∂ν) = μH)
    (hunit : ∀ᵐ x ∂ν, ‖x‖ ≤ 1) :
    (∫ x : H, ‖x - μH‖ ^ 2 ∂ν) =
      (∫ x : H, ‖x‖ ^ 2 ∂ν) - ‖μH‖ ^ 2 := by
  have hxint := integrable_id_of_ae_norm_le_one ν hunit
  have hraw := (integral_norm_sq_le_one_of_ae_norm_le_one ν hunit).1
  have hinner : Integrable (fun x : H => inner ℝ x μH) ν :=
    hxint.inner_const μH
  have hinnerInt :
      (∫ x : H, inner ℝ x μH ∂ν) = ‖μH‖ ^ 2 := by
    calc
      (∫ x : H, inner ℝ x μH ∂ν)
          = ∫ x : H, inner ℝ μH x ∂ν := by
              apply integral_congr_ae
              exact ae_of_all ν (fun x => real_inner_comm x μH)
      _ = inner ℝ μH (∫ x : H, x ∂ν) := integral_inner hxint μH
      _ = inner ℝ μH μH := by rw [hmean]
      _ = ‖μH‖ ^ 2 := real_inner_self_eq_norm_sq
  have hconst : Integrable (fun _x : H => ‖μH‖ ^ 2) ν := integrable_const _
  calc
    (∫ x : H, ‖x - μH‖ ^ 2 ∂ν)
        = ∫ x : H, (‖x‖ ^ 2 - 2 * inner ℝ x μH + ‖μH‖ ^ 2) ∂ν := by
            apply integral_congr_ae
            exact ae_of_all ν (fun x => norm_sub_sq_real x μH)
    _ = (∫ x : H, ‖x‖ ^ 2 - 2 * inner ℝ x μH ∂ν) + ‖μH‖ ^ 2 := by
          rw [integral_add (hraw.sub (hinner.const_mul 2)) hconst]
          simp
    _ = (∫ x : H, ‖x‖ ^ 2 ∂ν) - 2 * (∫ x : H, inner ℝ x μH ∂ν) + ‖μH‖ ^ 2 := by
          rw [integral_sub hraw (hinner.const_mul 2), integral_const_mul]
    _ = (∫ x : H, ‖x‖ ^ 2 ∂ν) - ‖μH‖ ^ 2 := by
          rw [hinnerInt]
          ring

/-- Sharp centered second-moment bound under unit-ball support. -/
theorem integral_norm_sub_mean_sq_le_one
    (ν : Measure H) [IsProbabilityMeasure ν]
    (μH : H)
    (hmean : (∫ x : H, x ∂ν) = μH)
    (hunit : ∀ᵐ x ∂ν, ‖x‖ ≤ 1) :
    (∫ x : H, ‖x - μH‖ ^ 2 ∂ν) ≤ 1 := by
  rw [integral_norm_sub_mean_sq_eq ν μH hmean hunit]
  have hraw := (integral_norm_sq_le_one_of_ae_norm_le_one ν hunit).2
  have hsq : 0 ≤ ‖μH‖ ^ 2 := sq_nonneg _
  linarith

end UEOT.V3.HilbertMeanSourceVariance
