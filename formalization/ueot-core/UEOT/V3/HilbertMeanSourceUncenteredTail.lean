import UEOT.V3.HilbertMeanSourceCenteredTail
import UEOT.V3.HilbertMeanSourceFirstMoment
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# P-STAT-06 — source tail shifted by the exact first moment

This module combines the source-facing centered Azuma tail with the sharp
Hilbert first-moment estimate.  No new concentration inequality is introduced:
the bad event at radius `1 / sqrt N + ε` is contained in the centered event at
level `ε` because `E F ≤ 1 / sqrt N`.
-/

namespace UEOT.V3.HilbertMeanSourceUncenteredTail

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanSourceCenteredTail
open UEOT.V3.HilbertMeanSourceFirstMoment

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- Exact source-facing uncentered Hilbert-mean tail. -/
theorem source_meanError_tail_from_first_moment
    [BorelSpace H] [StandardBorelSpace H] [CompleteSpace H]
    [MeasurableAdd₂ H] [MeasurableSub H] [Nonempty H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hmean : ∀ j, (∫ x : H, x ∂μ j) = μH)
    (hunit : ∀ j, ∀ᵐ x ∂μ j, ‖x‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi μ).real
      {ω | 1 / Real.sqrt (N : ℝ) + ε ≤ ‖empiricalMean ω - μH‖}
      ≤ Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
  have hfirst := source_meanError_first_moment_le_one_div_sqrt
    hN μ μH hmean hunit
  have hsubset :
      {ω : Fin N → H |
        1 / Real.sqrt (N : ℝ) + ε ≤ ‖empiricalMean ω - μH‖} ⊆
      {ω : Fin N → H |
        ε ≤ ‖empiricalMean ω - μH‖ -
          ∫ x, ‖empiricalMean x - μH‖ ∂Measure.pi μ} := by
    intro ω hω
    dsimp only [Set.mem_setOf_eq] at hω ⊢
    linarith
  calc
    (Measure.pi μ).real
        {ω | 1 / Real.sqrt (N : ℝ) + ε ≤ ‖empiricalMean ω - μH‖}
        ≤ (Measure.pi μ).real
          {ω | ε ≤ ‖empiricalMean ω - μH‖ -
            ∫ x, ‖empiricalMean x - μH‖ ∂Measure.pi μ} :=
          measureReal_mono hsubset
    _ ≤ Real.exp (-(N : ℝ) * ε ^ 2 / 2) :=
      source_meanError_centered_tail hN μ μH hμH hunit hε

end UEOT.V3.HilbertMeanSourceUncenteredTail
