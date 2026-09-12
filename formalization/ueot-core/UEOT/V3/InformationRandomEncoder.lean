import UEOT.V3.InformationConditionalMutual
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# P-INFO-03 — random encoder joint-law geometry

The frozen rate-distortion source explicitly allows a randomized encoder
`P(M|H,U)` using independent encoder randomness.  This module therefore builds
the induced joint law from a Markov kernel; it does not replace the encoder by
a deterministic statistic `M=f(H,U)`.
-/

namespace UEOT.V3.InformationRandomEncoder

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationConditionalMutual

universe uU uH uM

variable {U : Type uU} {H : Type uH} {M : Type uM}
variable [MeasurableSpace U] [MeasurableSpace H] [MeasurableSpace M]
variable [StandardBorelSpace U] [StandardBorelSpace H] [StandardBorelSpace M]
variable [Nonempty H] [Nonempty M]

/-- Reassociate a raw composition-product sample `((u,h),m)` as
`(u,(h,m))`, the geometry used by the canonical conditional-MI interface. -/
def encoderReassoc : ((U × H) × M) → U × (H × M) :=
  fun z => (z.1.1, (z.1.2, z.2))

/-- Inverse reassociation. -/
def encoderUnreassoc : U × (H × M) → ((U × H) × M) :=
  fun z => ((z.1, z.2.1), z.2.2)

lemma measurable_encoderReassoc :
    Measurable (encoderReassoc (U := U) (H := H) (M := M)) := by
  unfold encoderReassoc
  exact (measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

lemma measurable_encoderUnreassoc :
    Measurable (encoderUnreassoc (U := U) (H := H) (M := M)) := by
  unfold encoderUnreassoc
  exact (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
    (measurable_snd.comp measurable_snd)

lemma encoderUnreassoc_leftInverse :
    Function.LeftInverse
      (encoderUnreassoc (U := U) (H := H) (M := M))
      encoderReassoc := by
  intro z
  rfl

lemma encoderReassoc_leftInverse :
    Function.LeftInverse
      (encoderReassoc (U := U) (H := H) (M := M))
      encoderUnreassoc := by
  intro z
  rfl

/-- Joint law on `U × (H × M)` induced by a source law `P(U,H)` and a genuinely
randomized encoder kernel `P(M|U,H)`. -/
noncomputable def randomEncoderJoint
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (η : Kernel (U × H) M) [IsMarkovKernel η] :
    Measure (U × (H × M)) :=
  (μ ⊗ₘ η).map encoderReassoc

instance randomEncoderJoint_isProbability
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (η : Kernel (U × H) M) [IsMarkovKernel η] :
    IsProbabilityMeasure (randomEncoderJoint μ η) := by
  unfold randomEncoderJoint
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_encoderReassoc (U := U) (H := H) (M := M)).aemeasurable).2 inferInstance

/-- The source objective `I(H;M|U)` for a randomized encoder, evaluated on the
actual encoder-induced joint law. -/
noncomputable def randomEncoderConditionalMutualInfo
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (η : Kernel (U × H) M) [IsMarkovKernel η] : ENNReal :=
  conditionalMutualInfo (randomEncoderJoint μ η)

lemma randomEncoderConditionalMutualInfo_nonneg
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (η : Kernel (U × H) M) [IsMarkovKernel η] :
    0 ≤ randomEncoderConditionalMutualInfo μ η := by
  exact bot_le

end

end UEOT.V3.InformationRandomEncoder
