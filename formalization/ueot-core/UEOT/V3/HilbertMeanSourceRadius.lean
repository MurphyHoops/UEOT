import UEOT.V3.HilbertMeanSourceUncenteredTail
import UEOT.V3.HilbertMeanRadius
import Mathlib.Tactic

/-!
# P-STAT-06 — exact source radius

This module specializes the source uncentered tail at the frozen finite-family
deviation and normalizes the threshold to

`(1 + sqrt (2 * log (L / alpha))) / sqrt N`.

The resulting per-channel failure probability is exactly `alpha / L`.
-/

namespace UEOT.V3.HilbertMeanSourceRadius

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanRadius
open UEOT.V3.HilbertMeanSourceUncenteredTail

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- Frozen P-STAT-06 radius. -/
noncomputable def pStat06SourceRadius (N L : ℕ) (alpha : ℝ) : ℝ :=
  (1 + Real.sqrt (2 * Real.log ((L : ℝ) / alpha))) / Real.sqrt (N : ℝ)

/-- The generic deviation form equals the frozen source normalization. -/
theorem one_div_sqrt_add_deviation_eq_sourceRadius
    {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    1 / Real.sqrt (N : ℝ) + pStat06Deviation N L alpha =
      pStat06SourceRadius N L alpha := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLoneNat : 1 ≤ L := Nat.succ_le_iff.mpr hL
  have hLone : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLoneNat
  have hratio_one : 1 ≤ (L : ℝ) / alpha := by
    rw [le_div_iff₀ halpha0]
    simpa using halpha1.trans hLone
  have hlog : 0 ≤ Real.log ((L : ℝ) / alpha) := Real.log_nonneg hratio_one
  have hnum : 0 ≤ 2 * Real.log ((L : ℝ) / alpha) := mul_nonneg (by norm_num) hlog
  unfold pStat06Deviation pStat06SourceRadius
  rw [Real.sqrt_div hnum]
  ring

/-- Source-facing exact per-channel P-STAT-06 radius bound. -/
theorem source_meanError_tail_exact_radius
    [BorelSpace H] [StandardBorelSpace H] [CompleteSpace H]
    [MeasurableAdd₂ H] [MeasurableSub H] [Nonempty H]
    {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hInt : ∀ j, Integrable (fun x : H => x) (μ j))
    (hmean : ∀ j, (∫ x : H, x ∂μ j) = μH)
    (hunit : ∀ j, ∀ᵐ x ∂μ j, ‖x‖ ≤ 1) :
    (Measure.pi μ).real
      {ω | pStat06SourceRadius N L alpha ≤ ‖empiricalMean ω - μH‖}
      ≤ alpha / (L : ℝ) := by
  have htail := source_meanError_tail_from_first_moment
    hN μ μH hμH hInt hmean hunit
    (Real.sqrt_nonneg (2 * Real.log ((L : ℝ) / alpha) / (N : ℝ)))
  have hdev :
      Real.sqrt (2 * Real.log ((L : ℝ) / alpha) / (N : ℝ)) =
        pStat06Deviation N L alpha := rfl
  have hradius := one_div_sqrt_add_deviation_eq_sourceRadius
    hN hL halpha0 halpha1
  calc
    (Measure.pi μ).real
        {ω | pStat06SourceRadius N L alpha ≤ ‖empiricalMean ω - μH‖}
        ≤ Real.exp
          (-(N : ℝ) * (pStat06Deviation N L alpha) ^ 2 / 2) := by
            simpa [hdev, hradius] using htail
    _ = alpha / (L : ℝ) := scalar_tail_eq_alpha_div hN hL halpha0 halpha1

end UEOT.V3.HilbertMeanSourceRadius
