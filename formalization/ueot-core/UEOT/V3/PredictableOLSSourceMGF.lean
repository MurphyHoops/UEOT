import UEOT.V3.PredictableOLSKernelFreeze
import UEOT.V3.PredictableOLSProductIntegrability
import UEOT.V3.PredictableOLSPredictableMGF
import UEOT.V3.PredictableOLSScore
import Mathlib.Tactic

/-!
# P-INV-05 — source-facing predictable multiplier MGF

This module eliminates the technical `freeze` and exponential-integrability
interfaces from the predictable-multiplier theorem.  Its assumptions are the
mathematical source assumptions themselves: a past-measurable bounded
coefficient and conditionally sub-Gaussian noise.
-/

namespace UEOT.V3.PredictableOLSSourceMGF

open MeasureTheory ProbabilityTheory
open UEOT.V3.PredictableOLSScore
open UEOT.V3.PredictableOLSKernelFreeze
open UEOT.V3.PredictableOLSProductIntegrability
open UEOT.V3.PredictableOLSPredictableMGF
open scoped NNReal

universe uΩ

variable {Ω : Type uΩ} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The source noise proxy `sigma^2`, represented as a nonnegative real. -/
def noiseParam (sigma : ℝ) : ℝ≥0 :=
  ⟨sigma ^ 2, sq_nonneg sigma⟩

@[simp] theorem coe_noiseParam (sigma : ℝ) :
    (noiseParam sigma : ℝ) = sigma ^ 2 := rfl

/-- The generic predictable-multiplier proxy `B^2 sigma^2` is exactly the
score-layer proxy `(sigma B)^2`. -/
theorem predictable_mul_param_eq_incrementParam (sigma B : ℝ) :
    Real.toNNReal (B ^ 2) * noiseParam sigma = incrementParam sigma B := by
  apply NNReal.eq
  rw [NNReal.coe_mul, Real.coe_toNNReal (B ^ 2) (sq_nonneg B),
    coe_noiseParam, coe_incrementParam]
  ring

/-- A bounded past-measurable coefficient times conditionally sub-Gaussian
noise is conditionally sub-Gaussian with the exact source proxy `(sigma B)^2`.

This is the one-step probability bridge required by P-INV-05. -/
theorem hasCondSubgaussianMGF_predictable_mul
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (A X : Ω → ℝ) (sigma B : ℝ)
    (hB0 : 0 ≤ B)
    (hA : @Measurable Ω ℝ m inferInstance A)
    (hbound : ∀ ω, |A ω| ≤ B)
    (hX : HasCondSubgaussianMGF m hm X (noiseParam sigma) μ) :
    HasCondSubgaussianMGF m hm (fun ω => A ω * X ω)
      (incrementParam sigma B) μ := by
  have hfreeze := predictable_ae_eq_const (μ := μ) hm A hA
  have hint : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * (A ω * X ω))) μ :=
    fun t => integrable_exp_predictable_mul hm A X B hB0 hA hbound hX t
  have hmul := hasCondSubgaussianMGF_predictable_mul_of_freeze
    hm A X B hB0 hbound hX hfreeze hint
  rw [predictable_mul_param_eq_incrementParam sigma B] at hmul
  exact hmul

end UEOT.V3.PredictableOLSSourceMGF
