import UEOT.V3.InformationConditionalBinary
import UEOT.V3.InformationBinaryMutualFinite
import Mathlib.Tactic.NormNum

/-!
# Conditional binary fiber mutual information

This module exposes the already machine-checked unconditional binary mutual-
information identity on each true conditional fiber `P(M,B|U=u)`.  It is a
pure composition layer: no new information-theoretic assumption is introduced.
-/

namespace UEOT.V3.InformationConditionalBinaryFiberMI

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationCore
open UEOT.V3.InformationConditionalBinary
open UEOT.V3.InformationBinaryConditionalMean
open UEOT.V3.InformationBinaryMutualEntropy
open UEOT.V3.InformationBinaryMutualFinite

universe uU uM

variable {U : Type uU} {M : Type uM}
variable [MeasurableSpace U] [MeasurableSpace M]
variable [StandardBorelSpace U] [StandardBorelSpace M]
variable [Nonempty M]

/-- Every conditional fiber has finite binary-output mutual information. -/
theorem fiberMutualInfo_ne_top
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) :
    mutualInfo (conditionalBinaryKernel ρ u) ≠ ⊤ := by
  exact mutualInfo_ne_top_binary (conditionalBinaryKernel ρ u)

/-- On each fixed `U=u` fiber, ordinary mutual information is exactly the
binary marginal entropy minus the posterior entropy. -/
theorem fiberMutualInfo_toReal_eq_entropy_drop
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) :
    (mutualInfo (conditionalBinaryKernel ρ u)).toReal =
      conditionalBinaryEntropyFiber ρ u -
        ∫ m, Real.binEntropy
          (posteriorBitOneProb (conditionalBinaryKernel ρ u) m)
          ∂(conditionalBinaryKernel ρ).fst u := by
  simpa [conditionalBinaryEntropyFiber, conditionalBitOneProb,
    binaryMarginalOneProb, Kernel.snd_apply, Measure.snd, Kernel.fst_apply,
    Measure.fst] using
    (mutualInfo_toReal_eq_binaryEntropy_sub_posteriorEntropy
      (conditionalBinaryKernel ρ u))

/-- The real entropy drop on every binary conditional fiber is nonnegative. -/
theorem fiber_entropy_drop_nonneg
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) :
    0 ≤ conditionalBinaryEntropyFiber ρ u -
      ∫ m, Real.binEntropy
        (posteriorBitOneProb (conditionalBinaryKernel ρ u) m)
        ∂(conditionalBinaryKernel ρ).fst u := by
  rw [← fiberMutualInfo_toReal_eq_entropy_drop ρ u]
  exact ENNReal.toReal_nonneg

/-- The marginal binary-entropy fiber is integrable over the true `U` law. -/
theorem integrable_conditionalBinaryEntropyFiber
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    Integrable (conditionalBinaryEntropyFiber ρ) ρ.fst := by
  refine Integrable.mono' (integrable_const (Real.log 2))
    (measurable_conditionalBinaryEntropyFiber ρ).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  have hnonneg := conditionalBinaryEntropyFiber_nonneg ρ u
  have hle := conditionalBinaryEntropyFiber_le_log_two ρ u
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hlog] using hle

end UEOT.V3.InformationConditionalBinaryFiberMI
