import UEOT.V3.HilbertMeanIntegralContraction
import UEOT.V3.HilbertMeanRangeWidth

/-!
# P-STAT-06 — centered one-coordinate fibers

After future coordinates have been averaged out, a Doob increment is the
active-coordinate continuation value minus its average under the active
coordinate law.  This file records the deterministic/probabilistic facts
needed by conditional Hoeffding: absolute envelope, zero mean, and a support
interval whose width is no larger than the original oscillation constant.
-/

namespace UEOT.V3.HilbertMeanCenteredFiber

open MeasureTheory Real
open scoped NNReal

universe uβ

variable {β : Type uβ} [MeasurableSpace β]

/-- A continuation value with pairwise oscillation at most `c` differs from its
probability average by at most `c`. -/
theorem abs_sub_integral_le
    (ν : Measure β) [IsProbabilityMeasure ν]
    (q : β → ℝ) {c : ℝ}
    (hq : Integrable q ν)
    (hosc : ∀ x y, |q x - q y| ≤ c)
    (x : β) :
    |q x - ∫ y, q y ∂ν| ≤ c := by
  have hconst : Integrable (fun _ : β => q x) ν := integrable_const _
  have h := HilbertMeanIntegralContraction.abs_integral_sub_integral_le_const
    ν hconst hq (by
      filter_upwards with y
      exact hosc x y)
  simpa using h

/-- The centered continuation value has mean exactly zero. -/
theorem integral_centered_eq_zero
    (ν : Measure β) [IsProbabilityMeasure ν]
    (q : β → ℝ)
    (hq : Integrable q ν) :
    (∫ x, (q x - ∫ y, q y ∂ν) ∂ν) = 0 := by
  rw [integral_sub hq (integrable_const _), integral_const]
  simp

/-- The centered continuation value lies in the symmetric absolute envelope
`[-c,c]`. -/
theorem centered_mem_Icc_neg_pos
    (ν : Measure β) [IsProbabilityMeasure ν]
    (q : β → ℝ) {c : ℝ}
    (hq : Integrable q ν)
    (hosc : ∀ x y, |q x - q y| ≤ c)
    (x : β) :
    q x - (∫ y, q y ∂ν) ∈ Set.Icc (-c) c := by
  exact (abs_le.mp (abs_sub_integral_le ν q hq hosc x))

/-- With a nonempty active-coordinate type, the centered continuation values
also lie in their exact infimum/supremum interval. -/
theorem centered_mem_exact_Icc
    [Nonempty β]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (q : β → ℝ) {c : ℝ}
    (hq : Integrable q ν)
    (hosc : ∀ x y, |q x - q y| ≤ c)
    (x : β) :
    q x - (∫ y, q y ∂ν) ∈ Set.Icc
      (sInf (Set.range q) - ∫ y, q y ∂ν)
      (sSup (Set.range q) - ∫ y, q y ∂ν) := by
  exact HilbertMeanRangeWidth.centered_mem_Icc_sInf_sSup q hosc x

/-- The exact centered support interval has the same real width bound `c`. -/
theorem centered_exact_interval_width_le
    [Nonempty β]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (q : β → ℝ) {c : ℝ}
    (hq : Integrable q ν)
    (hosc : ∀ x y, |q x - q y| ≤ c) :
    (sSup (Set.range q) - ∫ y, q y ∂ν) -
      (sInf (Set.range q) - ∫ y, q y ∂ν) ≤ c := by
  exact HilbertMeanRangeWidth.centered_interval_width_le q hosc

/-- `NNReal` form of the exact interval-width bound, matching the support-width
input expected by `HilbertMeanConditionalHoeffding`. -/
theorem centered_exact_interval_nnnorm_le
    [Nonempty β]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (q : β → ℝ) {c : ℝ≥0}
    (hq : Integrable q ν)
    (hosc : ∀ x y, |q x - q y| ≤ (c : ℝ)) :
    ‖(sSup (Set.range q) - ∫ y, q y ∂ν) -
      (sInf (Set.range q) - ∫ y, q y ∂ν)‖₊ ≤ c := by
  classical
  let x₀ : β := Classical.choice (inferInstance : Nonempty β)
  have hbelow := HilbertMeanRangeWidth.bddBelow_range_of_pairwise_abs_sub_le q hosc
  have habove := HilbertMeanRangeWidth.bddAbove_range_of_pairwise_abs_sub_le q hosc
  have hlow : sInf (Set.range q) ≤ q x₀ :=
    csInf_le hbelow (Set.mem_range_self x₀)
  have hupp : q x₀ ≤ sSup (Set.range q) :=
    le_csSup habove (Set.mem_range_self x₀)
  have hnon : 0 ≤
      (sSup (Set.range q) - ∫ y, q y ∂ν) -
        (sInf (Set.range q) - ∫ y, q y ∂ν) := by
    linarith
  have hreal :
      (sSup (Set.range q) - ∫ y, q y ∂ν) -
        (sInf (Set.range q) - ∫ y, q y ∂ν) ≤ (c : ℝ) :=
    centered_exact_interval_width_le ν q hq hosc
  apply NNReal.coe_le_coe.mp
  simpa [Real.norm_eq_abs, abs_of_nonneg hnon] using hreal

end UEOT.V3.HilbertMeanCenteredFiber
