import UEOT.V3.InformationPredictiveSourceConverse
import UEOT.V3.InformationCanonicalObjective
import UEOT.V3.InformationPredictiveAchievability

/-!
# P-INFO-03 — predictive object rate at zero distortion

This module closes the source-facing v1.1 theorem.  The optimization is not
restricted to one preselected code alphabet: a feasible scheme carries its own
Standard-Borel code space, a genuinely randomized Markov encoder
`P(M|U,H)`, a Markov decoder `Q(.|U,M)`, and an exact zero expected predictive
TV certificate.  `predictiveObjectRateZero` is the infimum of `I(H;M|U)` over
all such bundled schemes in the ambient code universe.

The converse is the randomized zero-TV recovery theorem.  Achievability uses
the canonical code `M=C`, deterministic encoder `C=c(U,H)`, and canonical
future-law decoder.  Hence `R_obj(0)=H(C|U)` exactly.
-/

namespace UEOT.V3.InformationPredictiveRateZero

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.TotalVariation
open UEOT.V3.InformationConditionalStatistic
open UEOT.V3.InformationRandomEncoder
open UEOT.V3.InformationRandomEncoderSourceEntropy
open UEOT.V3.InformationPredictiveZeroTVRecovery
open UEOT.V3.InformationPredictiveSourceConverse
open UEOT.V3.InformationPredictiveAchievability
open UEOT.V3.InformationCanonicalObjective

universe uU uH uC uY

/-- A code alphabet admissible in the predictive rate-distortion optimization.
The theorem is universe-polymorphic; within each theorem instance the infimum
ranges over all bundled Standard-Borel code spaces in that ambient universe. -/
structure PredictiveCodeSpace where
  Code : Type uC
  measurableSpace : MeasurableSpace Code
  standardBorelSpace : @StandardBorelSpace Code measurableSpace
  nonempty : Nonempty Code

namespace PredictiveCodeSpace

instance (S : PredictiveCodeSpace.{uC}) : MeasurableSpace S.Code :=
  S.measurableSpace

instance (S : PredictiveCodeSpace.{uC}) : StandardBorelSpace S.Code :=
  S.standardBorelSpace

instance (S : PredictiveCodeSpace.{uC}) : Nonempty S.Code :=
  S.nonempty

end PredictiveCodeSpace

variable {U : Type uU} {H : Type uH} {C : Type uC} {Y : Type uY}
variable [MeasurableSpace U] [MeasurableSpace H] [MeasurableSpace C]
variable [MeasurableSpace Y]
variable [StandardBorelSpace U] [StandardBorelSpace H]
variable [StandardBorelSpace C] [StandardBorelSpace Y]
variable [Nonempty H] [Nonempty C] [Nonempty Y]
variable [Countable C] [MeasurableSingletonClass C]

/-- A zero-distortion randomized encoder/decoder candidate. -/
structure ZeroDistortionScheme
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC] where
  space : PredictiveCodeSpace.{uC}
  encoder : Kernel (U × H) space.Code
  encoderMarkov : IsMarkovKernel encoder
  decoder : Kernel (U × space.Code) Y
  decoderMarkov : IsMarkovKernel decoder
  zeroDistortion :
    letI : IsMarkovKernel encoder := encoderMarkov
    letI : IsMarkovKernel decoder := decoderMarkov
    (∫⁻ z,
      ENNReal.ofReal
        (tvDist
          (canonicalPredictiveKernel (M := space.Code) κC c hc z)
          (decodedPredictiveKernel (H := H) decoder z))
      ∂randomEncoderJoint μ encoder) = 0

namespace ZeroDistortionScheme

/-- Conditional information cost of a feasible randomized scheme. -/
noncomputable def objective
    {μ : Measure (U × H)} [IsProbabilityMeasure μ]
    {c : U × H → C} {hc : Measurable c}
    {κC : Kernel C Y} [IsMarkovKernel κC]
    (S : ZeroDistortionScheme μ c hc κC) : ENNReal := by
  letI : IsMarkovKernel S.encoder := S.encoderMarkov
  exact randomEncoderConditionalMutualInfo μ S.encoder

end ZeroDistortionScheme

/-- Set of all zero-distortion conditional-information costs, allowing each
candidate to choose its own Standard-Borel code alphabet. -/
noncomputable def zeroDistortionObjectiveSet
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC] : Set ENNReal :=
  { r | ∃ S : ZeroDistortionScheme μ c hc κC,
      r = S.objective }

/-- `R_obj(0)`: infimum of `I(H;M|U)` over all zero-predictive-TV randomized
encoder/decoder schemes. -/
noncomputable def predictiveObjectRateZero
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC] : ENNReal :=
  sInf (zeroDistortionObjectiveSet μ c hc κC)

/-- Every feasible zero-distortion scheme pays at least the source conditional
entropy of the canonical predictive core. -/
theorem sourceEntropy_le_schemeObjective
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC]
    (hinj : Function.Injective (fun x => κC x))
    (S : ZeroDistortionScheme μ c hc κC) :
    sourceConditionalCoreEntropy μ c hc ≤ S.objective := by
  letI : IsMarkovKernel S.encoder := S.encoderMarkov
  letI : IsMarkovKernel S.decoder := S.decoderMarkov
  exact sourceConditionalCoreEntropy_le_randomEncoderConditionalMutualInfo_of_zeroDistortion
    μ S.encoder c hc κC hinj S.decoder S.zeroDistortion

/-- Converse after taking the infimum over all admissible code spaces and
randomized encoder/decoder pairs. -/
theorem sourceEntropy_le_predictiveObjectRateZero
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC]
    (hinj : Function.Injective (fun x => κC x)) :
    sourceConditionalCoreEntropy μ c hc ≤
      predictiveObjectRateZero μ c hc κC := by
  unfold predictiveObjectRateZero
  apply le_sInf
  intro r hr
  rcases hr with ⟨S, rfl⟩
  exact sourceEntropy_le_schemeObjective μ c hc κC hinj S

/-- The canonical predictive core itself is an admissible code space. -/
noncomputable def canonicalPredictiveCodeSpace : PredictiveCodeSpace.{uC} where
  Code := C
  measurableSpace := inferInstance
  standardBorelSpace := inferInstance
  nonempty := inferInstance

/-- Canonical zero-distortion achiever: `M=C` deterministically and decode by
the canonical future-law kernel. -/
noncomputable def canonicalZeroDistortionScheme
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC] :
    ZeroDistortionScheme μ c hc κC where
  space := canonicalPredictiveCodeSpace (C := C)
  encoder := canonicalCoreEncoder c hc
  encoderMarkov := by
    change IsMarkovKernel (canonicalCoreEncoder c hc)
    exact canonicalCoreEncoder_isMarkov c hc
  decoder := canonicalCoreDecoder (U := U) κC
  decoderMarkov := by
    change IsMarkovKernel (canonicalCoreDecoder (U := U) κC)
    exact canonicalCoreDecoder_isMarkov κC
  zeroDistortion := by
    change
      (∫⁻ z : U × (H × C),
        ENNReal.ofReal
          (tvDist
            (canonicalPredictiveKernel (M := C) κC c hc z)
            (decodedPredictiveKernel (H := H)
              (canonicalCoreDecoder (U := U) κC) z))
        ∂randomEncoderJoint μ (canonicalCoreEncoder c hc)) = 0
    exact canonicalCoreEncoder_zeroDistortion μ c hc κC

/-- The canonical achiever has objective exactly `H_μ(C|U)`. -/
theorem canonicalScheme_objective_eq_sourceEntropy
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC] :
    (canonicalZeroDistortionScheme μ c hc κC).objective =
      sourceConditionalCoreEntropy μ c hc := by
  change
    randomEncoderConditionalMutualInfo μ (canonicalCoreEncoder c hc) =
      sourceConditionalCoreEntropy μ c hc
  unfold randomEncoderConditionalMutualInfo sourceConditionalCoreEntropy
  exact canonicalEncoder_conditionalMutualInfo_eq_sourceEntropy μ c hc

/-- Achievability after taking the infimum: the canonical code gives an element
of the feasible objective set equal to the source conditional entropy. -/
theorem predictiveObjectRateZero_le_sourceEntropy
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC] :
    predictiveObjectRateZero μ c hc κC ≤
      sourceConditionalCoreEntropy μ c hc := by
  unfold predictiveObjectRateZero
  apply sInf_le
  refine ⟨canonicalZeroDistortionScheme μ c hc κC, ?_⟩
  exact (canonicalScheme_objective_eq_sourceEntropy μ c hc κC).symm

/-- **P-INFO-03 / Predictive Object Rate-Distortion at zero distortion.**
For a countable canonical predictive core whose labels injectively represent
future laws, the optimal randomized zero-TV representation rate is exactly the
source conditional entropy of that core:

`R_obj(0) = H(C|U)`.
-/
theorem predictiveObjectRateZero_eq_sourceEntropy
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC]
    (hinj : Function.Injective (fun x => κC x)) :
    predictiveObjectRateZero μ c hc κC =
      sourceConditionalCoreEntropy μ c hc := by
  apply le_antisymm
  · exact predictiveObjectRateZero_le_sourceEntropy μ c hc κC
  · exact sourceEntropy_le_predictiveObjectRateZero μ c hc κC hinj

end

end UEOT.V3.InformationPredictiveRateZero
