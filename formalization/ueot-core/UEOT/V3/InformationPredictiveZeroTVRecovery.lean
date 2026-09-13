import UEOT.V3.InformationPredictiveCoreRecovery
import UEOT.V3.InformationZeroTV
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# P-INFO-03 — zero predictive TV implies canonical-core recovery

This module closes the measure-theoretic source step

`E TV(P(Y|H,U), Q(.|M,U)) = 0`

implies that the discrete canonical predictive core is recoverable from
`(M,U)`.  The proof uses the true law `ρ` on `U × (H × M)`, converts zero
average TV into global almost-everywhere equality of the two future kernels,
and then uses the canonical disintegration

`ρ.fst ⊗ₘ ρ.condKernel = ρ`

to obtain the required fiberwise equality under `P(H,M|U=u)`.
-/

namespace UEOT.V3.InformationPredictiveZeroTVRecovery

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.TotalVariation
open UEOT.V3.InformationConditionalMutual
open UEOT.V3.InformationZeroTV
open UEOT.V3.InformationDiscreteLawCode
open UEOT.V3.InformationConditionalStatistic
open UEOT.V3.InformationPredictiveCoreRecovery

universe uU uH uM uC uY

variable {U : Type uU} {H : Type uH} {M : Type uM}
variable {C : Type uC} {Y : Type uY}
variable [MeasurableSpace U] [MeasurableSpace H] [MeasurableSpace M]
variable [MeasurableSpace C] [MeasurableSpace Y]
variable [StandardBorelSpace U] [StandardBorelSpace H] [StandardBorelSpace M]
variable [StandardBorelSpace Y]
variable [Nonempty H] [Nonempty M] [Nonempty C] [Nonempty Y]
variable [Countable C] [MeasurableSingletonClass C]

/-- The source canonical future kernel `P(Y|H,U)`, represented through the
countable core code `c(U,H)` and its law kernel `κC`. -/
noncomputable def canonicalPredictiveKernel
    (κC : Kernel C Y)
    (c : U × H → C) (hc : Measurable c) :
    Kernel (U × (H × M)) Y :=
  κC.comap
    (fun z => c (z.1, z.2.1))
    (hc.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))

/-- The source decoder future kernel `Q(.|M,U)` pulled back to the full
`(U,H,M)` sample space. -/
noncomputable def decodedPredictiveKernel
    (q : Kernel (U × M) Y) : Kernel (U × (H × M)) Y :=
  q.comap
    (fun z => (z.1, z.2.2))
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

instance canonicalPredictiveKernel_isMarkov
    (κC : Kernel C Y) [IsMarkovKernel κC]
    (c : U × H → C) (hc : Measurable c) :
    IsMarkovKernel (canonicalPredictiveKernel (M := M) κC c hc) := by
  unfold canonicalPredictiveKernel
  infer_instance

instance decodedPredictiveKernel_isMarkov
    (q : Kernel (U × M) Y) [IsMarkovKernel q] :
    IsMarkovKernel (decodedPredictiveKernel (H := H) q) := by
  unfold decodedPredictiveKernel
  infer_instance

/-- Zero source distortion gives equality of the canonical and decoded future
laws in almost every true `U=u` conditional fiber. -/
theorem nested_predictiveLaw_eq_of_zeroDistortion
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC]
    (q : Kernel (U × M) Y) [IsMarkovKernel q]
    (hzero :
      (∫⁻ z,
        ENNReal.ofReal
          (tvDist
            (canonicalPredictiveKernel (M := M) κC c hc z)
            (decodedPredictiveKernel (H := H) q z)) ∂ρ) = 0) :
    ∀ᵐ u ∂ρ.fst,
      ∀ᵐ hm ∂conditionalJointKernel ρ u,
        q (u, hm.2) = κC (c (u, hm.1)) := by
  have hglobal :
      canonicalPredictiveKernel (M := M) κC c hc =ᵐ[ρ]
        decodedPredictiveKernel (H := H) q :=
    ae_kernel_eq_of_lintegral_tvDist_eq_zero
      ρ
      (canonicalPredictiveKernel (M := M) κC c hc)
      (decodedPredictiveKernel (H := H) q)
      hzero
  have hcomp :
      canonicalPredictiveKernel (M := M) κC c hc =ᵐ[
        ρ.fst ⊗ₘ conditionalJointKernel ρ]
        decodedPredictiveKernel (H := H) q := by
    have hreconstruct : ρ.fst ⊗ₘ conditionalJointKernel ρ = ρ := by
      unfold conditionalJointKernel
      exact Measure.disintegrate ρ ρ.condKernel
    rw [hreconstruct]
    exact hglobal
  have hnested := Measure.ae_ae_of_ae_compProd hcomp
  filter_upwards [hnested] with u hu
  filter_upwards [hu] with hm hhm
  simpa [canonicalPredictiveKernel, decodedPredictiveKernel,
    Kernel.comap_apply] using hhm.symm

/-- **Zero-TV recoverability bridge.**  If the canonical core labels distinct
future laws and the decoder achieves zero average source TV distortion, then
that discrete core is recoverable from `(U,M)` in the exact law-level sense
used by the conditional data-processing lower bound. -/
theorem statisticFiberRecoverable_of_zeroDistortion
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC]
    (hinj : Function.Injective (fun c => κC c))
    (q : Kernel (U × M) Y) [IsMarkovKernel q]
    (hzero :
      (∫⁻ z,
        ENNReal.ofReal
          (tvDist
            (canonicalPredictiveKernel (M := M) κC c hc z)
            (decodedPredictiveKernel (H := H) q z)) ∂ρ) = 0) :
    StatisticFiberRecoverable ρ c hc
      (predictiveCoreDecoder
        ({ law := fun c => κC c, injective_law := hinj } :
          DiscreteLawCode (C := C) (Y := Y))
        (fun um => q um)) := by
  let code : DiscreteLawCode (C := C) (Y := Y) :=
    { law := fun c => κC c
      injective_law := hinj }
  apply statisticFiberRecoverable_of_predictiveLaw_eq
    ρ c hc code (fun um => q um) q.measurable
  have heq := nested_predictiveLaw_eq_of_zeroDistortion
    ρ c hc κC q hzero
  filter_upwards [heq] with u hu
  filter_upwards [hu] with hm hhm
  simpa [code] using hhm

/-- **Zero-TV information lower-bound bridge.**  This is the exact inequality
needed before taking the source rate-distortion infimum: a decoder with zero
average predictive TV forces the deterministic canonical core entropy carried
by the true randomized-encoder law below `I(H;M|U)`. -/
theorem conditionalStatisticEntropy_le_conditionalMutualInfo_of_zeroDistortion
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c)
    (κC : Kernel C Y) [IsMarkovKernel κC]
    (hinj : Function.Injective (fun c => κC c))
    (q : Kernel (U × M) Y) [IsMarkovKernel q]
    (hzero :
      (∫⁻ z,
        ENNReal.ofReal
          (tvDist
            (canonicalPredictiveKernel (M := M) κC c hc z)
            (decodedPredictiveKernel (H := H) q z)) ∂ρ) = 0) :
    conditionalStatisticEntropy ρ c hc ≤ conditionalMutualInfo ρ := by
  let code : DiscreteLawCode (C := C) (Y := Y) :=
    { law := fun c => κC c
      injective_law := hinj }
  have hrec : StatisticFiberRecoverable ρ c hc
      (predictiveCoreDecoder code (fun um => q um)) := by
    simpa [code] using
      (statisticFiberRecoverable_of_zeroDistortion
        ρ c hc κC hinj q hzero)
  exact conditionalStatisticEntropy_le_conditionalMutualInfo_of_recoverable
    ρ c hc
    (predictiveCoreDecoder code (fun um => q um))
    (measurable_predictiveCoreDecoder code (fun um => q um) q.measurable)
    hrec

end

end UEOT.V3.InformationPredictiveZeroTVRecovery
