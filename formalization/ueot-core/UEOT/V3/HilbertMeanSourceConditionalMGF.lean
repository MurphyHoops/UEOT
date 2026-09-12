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
  let P : Measure (Fin N → H) := Measure.pi μ
  let m : MeasurableSpace (Fin N → H) := sourcePastSigma (H := H) i
  let X : (Fin N → H) → ℝ := sourceClippedIncrement μ i μH
  let c : ℝ≥0 := invSqParam N
  have hm : m ≤ (inferInstance : MeasurableSpace (Fin N → H)) := by
    simpa [m] using sourcePastSigma_le (H := H) i
  have h_int : ∀ t : ℝ, Integrable (fun ω => exp (t * X ω)) P := by
    intro t
    simpa [P, X] using
      integrable_exp_mul_sourceClippedIncrement
        hN μ i μH hμH hunit t
  have h_rat : ∀ q : ℚ, ∀ᵐ ω ∂(P.trim hm),
      P[fun y => exp ((q : ℝ) * X y) | m] ω ≤
        exp ((c : ℝ) * (q : ℝ) ^ 2 / 2) := by
    intro q
    apply ae_trim_condExp_le_of_ae_condExp_le
      (μ := P) (m := m) hm
    simpa [P, m, X, c] using
      ae_condExp_exp_sourceClippedIncrement_le
        hN μ i μH hμH hunit q
  change HasCondSubgaussianMGF m hm X c P
  apply Kernel.HasSubgaussianMGF.of_rat
  · intro t
    rw [condExpKernel_comp_trim (μ := P) hm]
    exact h_int t
  · intro q
    have heq := condExp_ae_eq_trim_integral_condExpKernel hm (h_int (q : ℝ))
    filter_upwards [h_rat q, heq] with ω hbound hEq
    rw [hEq] at hbound
    simpa [mgf] using hbound

end UEOT.V3.HilbertMeanSourceConditionalMGF
