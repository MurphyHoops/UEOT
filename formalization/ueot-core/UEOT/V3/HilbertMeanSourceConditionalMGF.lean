import UEOT.V3.HilbertMeanSourceRationalMGF
import UEOT.V3.HilbertMeanConditionalSubGaussianLift
import Mathlib.Tactic

/-!
# P-STAT-06 — source conditional sub-Gaussian increment

The rational conditional-MGF inequality is promoted to the trimmed past law and
then to all real MGF parameters through `Kernel.HasSubgaussianMGF.of_rat`.
This closes the conditional probability-theory layer for the clipped source
increment with the exact proxy `1/N²`.
-/

namespace UEOT.V3.HilbertMeanSourceConditionalMGF

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.HilbertMeanAzuma
open UEOT.V3.HilbertMeanConditionalSubGaussianLift
open UEOT.V3.HilbertMeanSourceClippedIncrement
open UEOT.V3.HilbertMeanSourceRationalMGF

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- Under the canonical product law, the filtration-native clipped source
increment is conditionally sub-Gaussian with the exact McDiarmid proxy `1/N²`
relative to the strict-past sigma-algebra. -/
theorem hasCondSubgaussianMGF_sourceClippedIncrement_invSqParam
    [BorelSpace H] [StandardBorelSpace H] [Nonempty H]
    [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    HasCondSubgaussianMGF
      (sourcePastSigma (H := H) i)
      (sourcePastSigma_le (H := H) i)
      (sourceClippedIncrement μ i μH)
      (invSqParam N)
      (Measure.pi μ) := by
  letI : IsProbabilityMeasure (Measure.pi μ) := by infer_instance
  apply hasCondSubgaussianMGF_of_rat_condExp_le
    (μ := Measure.pi μ)
    (X := sourceClippedIncrement μ i μH)
    (c := invSqParam N)
    (sourcePastSigma_le (H := H) i)
  · intro t
    exact integrable_exp_mul_sourceClippedIncrement
      hN μ i μH hμH hunit t
  · intro q
    apply ae_trim_condExp_le_of_ae_condExp_le
      (μ := Measure.pi μ)
      (m := sourcePastSigma (H := H) i)
      (sourcePastSigma_le (H := H) i)
    exact ae_condExp_exp_sourceClippedIncrement_le
      hN μ i μH hμH hunit q

end UEOT.V3.HilbertMeanSourceConditionalMGF
