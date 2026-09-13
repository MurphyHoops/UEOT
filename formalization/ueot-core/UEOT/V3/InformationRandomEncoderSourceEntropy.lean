import UEOT.V3.InformationRandomEncoderSourceConditional
import UEOT.V3.InformationConditionalStatistic

/-!
# P-INFO-03 — source-fixed conditional predictive-core entropy

The zero-distortion converse is expressed on the encoder-induced law
`ρ_η(U,H,M)`, but the source theorem requires a fixed quantity `H_μ(C|U)` that
cannot depend on the randomized encoder.  This module proves that the
conditional entropy of the deterministic predictive core computed from
`ρ_η` is exactly the same source entropy computed from `μ(U,H)`.
-/

namespace UEOT.V3.InformationRandomEncoderSourceEntropy

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationDiscreteEntropy
open UEOT.V3.InformationStatistic
open UEOT.V3.InformationConditionalMutual
open UEOT.V3.InformationConditionalStatistic
open UEOT.V3.InformationRandomEncoder
open UEOT.V3.InformationRandomEncoderSourceConditional

universe uU uH uM uC

variable {U : Type uU} {H : Type uH} {M : Type uM} {C : Type uC}
variable [MeasurableSpace U] [MeasurableSpace H] [MeasurableSpace M]
variable [MeasurableSpace C]
variable [StandardBorelSpace U] [StandardBorelSpace H] [StandardBorelSpace M]
variable [StandardBorelSpace C]
variable [Nonempty H] [Nonempty M] [Nonempty C]
variable [Countable C] [MeasurableSingletonClass C]

/-- Source-only conditional entropy of a deterministic core `C=c(U,H)`.
Unlike `conditionalStatisticEntropy` on an augmented law, this definition
mentions only the source law `μ(U,H)`. -/
noncomputable def sourceConditionalCoreEntropy
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c) : ENNReal :=
  ∫⁻ u,
    discreteShannonEntropy
      ((μ.condKernel u).map (coreAt c u)) ∂μ.fst

/-- **Random-encoder source invariance of core entropy.**  For every Markov
encoder `P(M|U,H)`, the deterministic core entropy computed from the induced
law on `U × (H × M)` equals the source-only `H_μ(C|U)`. -/
theorem conditionalStatisticEntropy_randomEncoder_eq_source
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (η : Kernel (U × H) M) [IsMarkovKernel η]
    (c : U × H → C) (hc : Measurable c) :
    conditionalStatisticEntropy (randomEncoderJoint μ η) c hc =
      sourceConditionalCoreEntropy μ c hc := by
  unfold conditionalStatisticEntropy sourceConditionalCoreEntropy
  rw [randomEncoderJoint_fst μ η]
  apply lintegral_congr_ae
  have hcond := randomEncoder_condKernel_fst_ae_eq_source μ η
  filter_upwards [hcond] with u hu
  unfold conditionalStatisticJoint
  rw [statisticJoint_fst]
  have hfiber :
      (conditionalJointKernel (randomEncoderJoint μ η) u).fst =
        μ.condKernel u := by
    unfold conditionalJointKernel Measure.fst
    have hu' := hu
    rw [Kernel.map_apply
      (randomEncoderJoint μ η).condKernel measurable_fst u] at hu'
    exact hu'
  rw [hfiber]

end

end UEOT.V3.InformationRandomEncoderSourceEntropy
