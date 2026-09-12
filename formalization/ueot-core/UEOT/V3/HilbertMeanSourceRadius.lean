import UEOT.V3.HilbertMeanSourceUncenteredTail
import UEOT.V3.HilbertMeanRadius

/-!
# P-STAT-06 — source tail at the exact simultaneous deviation

This module instantiates the source-facing uncentered tail at the frozen
finite-candidate deviation

`ε = sqrt (2 log (L / alpha) / N)`.

The resulting one-channel failure probability is exactly bounded by
`alpha / L`; the already-verified generic finite-union theorem can therefore
close the simultaneous layer without changing constants.
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

/-- Exact per-channel P-STAT-06 source radius bound. -/
theorem source_meanError_tail_at_pStat06Deviation
    [BorelSpace H] [StandardBorelSpace H] [CompleteSpace H]
    [MeasurableAdd₂ H] [MeasurableSub H] [Nonempty H]
    {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hInt : ∀ j, Integrable (fun x : H => x) (μ j))
    (hmean : ∀ j, (∫ x : H, x ∂μ j) = μH)
    (hunit : ∀ j, ∀ᵐ x ∂μ j, ‖x‖ ≤ 1)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    (Measure.pi μ).real
      {ω |
        1 / Real.sqrt (N : ℝ) + pStat06Deviation N L alpha ≤
          ‖empiricalMean ω - μH‖}
      ≤ alpha / (L : ℝ) := by
  have hdev : 0 ≤ pStat06Deviation N L alpha := Real.sqrt_nonneg _
  have htail := source_meanError_tail_from_first_moment
    hN μ μH hμH hInt hmean hunit hdev
  calc
    (Measure.pi μ).real
        {ω |
          1 / Real.sqrt (N : ℝ) + pStat06Deviation N L alpha ≤
            ‖empiricalMean ω - μH‖}
        ≤ Real.exp
          (-(N : ℝ) * (pStat06Deviation N L alpha) ^ 2 / 2) := htail
    _ = alpha / (L : ℝ) :=
      scalar_tail_eq_alpha_div hN hL halpha0 halpha1

end UEOT.V3.HilbertMeanSourceRadius
