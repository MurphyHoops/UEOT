import UEOT.V3.InformationConditionalStatistic
import UEOT.V3.InformationDiscreteLawCode

/-!
# P-INFO-03 — predictive-law equality implies core recoverability

This module isolates the source-critical bridge between zero predictive
distortion and the information-theoretic lower bound.

Once a countable canonical predictive core `C` is represented injectively by
future laws, equality of the decoder's predicted future law with the canonical
law implies exact recovery of the core label through a measurable law decoder.
The recovery statement is lifted to the true conditional `U=u` fibers in the
law-level form required by `InformationConditionalStatistic`.
-/

namespace UEOT.V3.InformationPredictiveCoreRecovery

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationStatistic
open UEOT.V3.InformationEntropyBound
open UEOT.V3.InformationRecoverableDiscrete
open UEOT.V3.InformationConditionalMutual
open UEOT.V3.InformationConditionalStatistic
open UEOT.V3.InformationDiscreteLawCode

universe uU uH uM uC uY

/-- If a decoder recovers the first coordinate of a joint `(C,M)` law almost
everywhere, then the decoded-copy pushforward is exactly the diagonal copy law
of the `C` marginal. -/
theorem statisticJoint_recoverable_of_ae_decoder_recovers
    {H : Type uH} {M : Type uM} {C : Type uC}
    [MeasurableSpace H] [MeasurableSpace M] [MeasurableSpace C]
    [Countable C] [MeasurableSingletonClass C]
    [StandardBorelSpace M] [Nonempty M]
    (μ : Measure (H × M)) [IsProbabilityMeasure μ]
    (f : H → C) (hf : Measurable f)
    (d : M → C) (hd : Measurable d)
    (hrec : ∀ᵐ z ∂μ, d z.2 = f z.1) :
    (statisticJoint μ f hf).map (decodedCopyMap d) =
      copyJoint (statisticJoint μ f hf).fst := by
  rw [statisticJoint_fst μ f hf]
  unfold statisticJoint copyJoint
  let hstat : Measurable (fun z : H × M => (f z.1, z.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  let hdiag : Measurable (fun c : C => (c, c)) :=
    measurable_id.prodMk measurable_id
  have hleft :
      Measure.map (decodedCopyMap d)
          (Measure.map (fun z : H × M => (f z.1, z.2)) μ) =
        Measure.map (fun z : H × M => (f z.1, d z.2)) μ := by
    simpa [decodedCopyMap, Function.comp_def] using
      (Measure.map_map (μ := μ) (measurable_decodedCopyMap d hd) hstat)
  have hfst :
      Measure.map f μ.fst =
        Measure.map (fun z : H × M => f z.1) μ := by
    unfold Measure.fst
    simpa [Function.comp_def] using
      (Measure.map_map (μ := μ) hf measurable_fst)
  rw [hleft, hfst]
  have hright :
      Measure.map (fun c : C => (c, c))
          (Measure.map (fun z : H × M => f z.1) μ) =
        Measure.map (fun z : H × M => (f z.1, f z.1)) μ := by
    have hfp : Measurable (fun z : H × M => f z.1) := hf.comp measurable_fst
    simpa [Function.comp_def] using
      (Measure.map_map (μ := μ) hdiag hfp)
  rw [hright]
  apply Measure.map_congr
  filter_upwards [hrec] with z hz
  simp [hz]

section Conditional

variable {U : Type uU} {H : Type uH} {M : Type uM} {C : Type uC}
variable [MeasurableSpace U] [MeasurableSpace H] [MeasurableSpace M]
variable [MeasurableSpace C]
variable [StandardBorelSpace U] [StandardBorelSpace H] [StandardBorelSpace M]
variable [Nonempty H] [Nonempty M]
variable [Countable C] [MeasurableSingletonClass C]

/-- Fiberwise a.e. recovery of `C=c(U,H)` by one measurable decoder `d(U,M)`
is sufficient for the law-level `StatisticFiberRecoverable` condition used in
the conditional information lower bound. -/
theorem statisticFiberRecoverable_of_ae_decoder_recovers
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c)
    (d : U × M → C) (hd : Measurable d)
    (hrec : ∀ᵐ u ∂ρ.fst,
      ∀ᵐ z ∂conditionalJointKernel ρ u,
        d (u, z.2) = c (u, z.1)) :
    StatisticFiberRecoverable ρ c hc d := by
  filter_upwards [hrec] with u hu
  apply statisticJoint_recoverable_of_ae_decoder_recovers
    (conditionalJointKernel ρ u)
    (coreAt c u)
    (measurable_coreAt c hc u)
    (fun m => d (u, m))
    (measurable_decoderAt d hd u)
  filter_upwards [hu] with z hz
  simpa [coreAt] using hz

section LawCode

variable {Y : Type uY} [MeasurableSpace Y]
variable [Nonempty C]

/-- Decode a discrete predictive-core label from a measure-valued prediction. -/
def predictiveCoreDecoder
    (code : DiscreteLawCode (C := C) (Y := Y))
    (q : U × M → Measure Y) : U × M → C :=
  fun um => code.decode (q um)

lemma measurable_predictiveCoreDecoder
    (code : DiscreteLawCode (C := C) (Y := Y))
    (q : U × M → Measure Y) (hq : Measurable q) :
    Measurable (predictiveCoreDecoder code q) := by
  unfold predictiveCoreDecoder
  exact code.measurable_decode_comp hq

/-- Equality of the measure-valued prediction with the canonical law code in
almost every true conditional fiber implies recoverability of the discrete
canonical predictive core from `(U,M)`. -/
theorem statisticFiberRecoverable_of_predictiveLaw_eq
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c)
    (code : DiscreteLawCode (C := C) (Y := Y))
    (q : U × M → Measure Y) (hq : Measurable q)
    (heq : ∀ᵐ u ∂ρ.fst,
      ∀ᵐ z ∂conditionalJointKernel ρ u,
        q (u, z.2) = code.law (c (u, z.1))) :
    StatisticFiberRecoverable ρ c hc (predictiveCoreDecoder code q) := by
  apply statisticFiberRecoverable_of_ae_decoder_recovers
    ρ c hc (predictiveCoreDecoder code q)
    (measurable_predictiveCoreDecoder code q hq)
  filter_upwards [heq] with u hu
  filter_upwards [hu] with z hz
  unfold predictiveCoreDecoder
  exact code.decode_eq_of_law_eq hz

end LawCode
end Conditional

end

end UEOT.V3.InformationPredictiveCoreRecovery
