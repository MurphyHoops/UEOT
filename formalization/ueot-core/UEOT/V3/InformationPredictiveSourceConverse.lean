import UEOT.V3.InformationRandomEncoderSourceEntropy
import UEOT.V3.InformationPredictiveZeroTVRecovery

/-!
# P-INFO-03 — source-fixed zero-distortion converse

The lower-bound theorem from zero predictive TV is naturally stated using the
entropy of the deterministic core inside the encoder-induced law.  Random
encoding, however, leaves the source conditional law `P(H|U)` unchanged.  This
module combines those two machine-checked bridges and obtains the source-facing
converse required by the v1.1 rate-distortion theorem.
-/

namespace UEOT.V3.InformationPredictiveSourceConverse

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.TotalVariation
open UEOT.V3.InformationRandomEncoder
open UEOT.V3.InformationRandomEncoderSourceEntropy
open UEOT.V3.InformationPredictiveZeroTVRecovery

universe uU uH uM uC uY

variable {U : Type uU} {H : Type uH} {M : Type uM}
variable {C : Type uC} {Y : Type uY}
variable [MeasurableSpace U] [MeasurableSpace H] [MeasurableSpace M]
variable [MeasurableSpace C] [MeasurableSpace Y]
variable [StandardBorelSpace U] [StandardBorelSpace H] [StandardBorelSpace M]
variable [StandardBorelSpace C] [StandardBorelSpace Y]
variable [Nonempty H] [Nonempty M] [Nonempty C] [Nonempty Y]
variable [Countable C] [MeasurableSingletonClass C]

/-- **Source-fixed P-INFO-03 converse.**  Every genuinely randomized Markov
encoder and decoder with zero expected predictive TV distortion has conditional
information cost at least the source conditional entropy of the canonical core.
-/
theorem sourceConditionalCoreEntropy_le_randomEncoderConditionalMutualInfo_of_zeroDistortion
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (η : Kernel (U × H) M) [IsMarkovKernel η]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC]
    (hinj : Function.Injective (fun x => κC x))
    (q : Kernel (U × M) Y) [IsMarkovKernel q]
    (hzero :
      (∫⁻ z,
        ENNReal.ofReal
          (tvDist
            (canonicalPredictiveKernel (M := M) κC c hc z)
            (decodedPredictiveKernel (H := H) q z))
        ∂randomEncoderJoint μ η) = 0) :
    sourceConditionalCoreEntropy μ c hc ≤
      randomEncoderConditionalMutualInfo μ η := by
  rw [← conditionalStatisticEntropy_randomEncoder_eq_source μ η c hc]
  simpa [randomEncoderConditionalMutualInfo] using
    (conditionalStatisticEntropy_le_conditionalMutualInfo_of_zeroDistortion
      (randomEncoderJoint μ η) c hc κC hinj q hzero)

end

end UEOT.V3.InformationPredictiveSourceConverse
