import UEOT.V3.PredictableOLSMultiplier
import Mathlib.Tactic

/-!
# P-INV-05 — exponential integrability of predictable products

This module proves the integrability half of the predictable-multiplier bridge.
If `A` is past-measurable and uniformly bounded by `B`, while `X` is
conditionally sub-Gaussian, then `exp (t * (A * X))` is integrable for every
real `t`.

The proof deliberately does not use the conditional-fibre freezing theorem.
It dominates the random exponent by the two deterministic tilts
`exp (q X) + exp (-q X)`, where `q = |t| B`.
-/

namespace UEOT.V3.PredictableOLSProductIntegrability

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

universe uΩ

variable {Ω : Type uΩ} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- A bounded predictable multiplier preserves exponential integrability of a
conditionally sub-Gaussian noise variable. -/
theorem integrable_exp_predictable_mul
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (A X : Ω → ℝ) (B : ℝ)
    (hB0 : 0 ≤ B)
    (hA : @Measurable Ω ℝ m inferInstance A)
    (hbound : ∀ ω, |A ω| ≤ B)
    {c : ℝ≥0}
    (hX : HasCondSubgaussianMGF m hm X c μ)
    (t : ℝ) :
    Integrable (fun ω => exp (t * (A ω * X ω))) μ := by
  have hAΩ : @Measurable Ω ℝ mΩ inferInstance A := hA.mono hm le_rfl
  have hXsm := by
    have hi := hX.integrable_exp_mul 1
    exact (aemeasurable_of_aemeasurable_exp hi.1.aemeasurable).aestronglyMeasurable
  have hAX := hAΩ.aestronglyMeasurable.mul hXsm
  have htarget :=
    Real.continuous_exp.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.mul hAX)
  let q : ℝ := |t| * B
  have hq0 : 0 ≤ q := mul_nonneg (abs_nonneg t) hB0
  have hplus : Integrable (fun ω => exp (q * X ω)) μ := hX.integrable_exp_mul q
  have hminus : Integrable (fun ω => exp ((-q) * X ω)) μ := hX.integrable_exp_mul (-q)
  refine (hplus.add hminus).mono' htarget ?_
  filter_upwards with ω
  have hu : t * (A ω * X ω) ≤ q * |X ω| := by
    calc
      t * (A ω * X ω) ≤ |t * (A ω * X ω)| := le_abs_self _
      _ = |t| * |A ω| * |X ω| := by
        rw [abs_mul, abs_mul]
        ring
      _ ≤ q * |X ω| := by
        dsimp [q]
        gcongr
        exact hbound ω
  have hexp : exp (t * (A ω * X ω)) ≤ exp (q * |X ω|) :=
    Real.exp_le_exp.mpr hu
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hsum_pos : 0 < exp (q * X ω) + exp ((-q) * X ω) :=
    add_pos (Real.exp_pos _) (Real.exp_pos _)
  rw [abs_of_pos hsum_pos]
  calc
    exp (t * (A ω * X ω)) ≤ exp (q * |X ω|) := hexp
    _ ≤ exp (q * X ω) + exp ((-q) * X ω) := by
      by_cases hx : 0 ≤ X ω
      · rw [abs_of_nonneg hx]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · have hx' : X ω ≤ 0 := le_of_not_ge hx
        rw [abs_of_nonpos hx']
        have heq : q * (-X ω) = (-q) * X ω := by ring
        rw [heq]
        exact le_add_of_nonneg_left (Real.exp_pos _).le

end UEOT.V3.PredictableOLSProductIntegrability
