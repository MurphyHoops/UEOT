import UEOT.V3.InformationConditionalMutualKLDecomposition
import UEOT.V3.InformationRecoverableDiscrete
import UEOT.V3.InformationStatistic

/-!
# P-INFO-03 — conditional deterministic-core data processing

The frozen source allows a genuinely randomized encoder `P(M|H,U)` but its
canonical predictive core `C` is a deterministic measurable function of
`(H,U)`. The data-processing statement is proved fiberwise: for each true
conditional law `P(H,M|U=u)`, apply ordinary mutual-information data processing
to the statistic `H ↦ C(u,H)`, then integrate over `U`.
-/

namespace UEOT.V3.InformationConditionalStatistic

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationCore
open UEOT.V3.InformationConditionalMutual
open UEOT.V3.InformationConditionalMutualKLDecomposition
open UEOT.V3.InformationStatistic
open UEOT.V3.InformationRecoverableDiscrete
open UEOT.V3.InformationDiscreteEntropy
open UEOT.V3.InformationEntropyBound

universe uU uH uM uC

variable {U : Type uU} {H : Type uH} {M : Type uM} {C : Type uC}
variable [MeasurableSpace U] [MeasurableSpace H] [MeasurableSpace M]
variable [MeasurableSpace C]
variable [StandardBorelSpace U] [StandardBorelSpace H] [StandardBorelSpace M]
variable [Nonempty H] [Nonempty M]

/-- Freeze the side-information coordinate in a deterministic core map. -/
def coreAt (c : U × H → C) (u : U) : H → C :=
  fun h => c (u, h)

lemma measurable_coreAt
    (c : U × H → C) (hc : Measurable c) (u : U) :
    Measurable (coreAt c u) := by
  unfold coreAt
  exact hc.comp (measurable_const.prodMk measurable_id)

/-- In the true fiber `P(H,M|U=u)`, push only the `H` coordinate through the
canonical deterministic core map. -/
noncomputable def conditionalStatisticJoint
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c) (u : U) : Measure (C × M) :=
  statisticJoint (conditionalJointKernel ρ u) (coreAt c u) (measurable_coreAt c hc u)

instance conditionalStatisticJoint_isProbability
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c) (u : U) :
    IsProbabilityMeasure (conditionalStatisticJoint ρ c hc u) := by
  unfold conditionalStatisticJoint statisticJoint
  exact (Measure.isProbabilityMeasure_map_iff
    (((measurable_coreAt c hc u).comp measurable_fst).prodMk measurable_snd).aemeasurable).2
      inferInstance

/-- Fiberwise representation of `I(C;M|U)` when `C=c(U,H)` is carried by the
original randomized-encoder joint law. -/
noncomputable def conditionalStatisticMutualInfo
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c) : ENNReal :=
  ∫⁻ u, mutualInfo (conditionalStatisticJoint ρ c hc u) ∂ρ.fst

/-- Conditional data processing for a deterministic predictive core. The
encoder generating `M` may be randomized; only `C=c(U,H)` is deterministic. -/
theorem conditionalStatisticMutualInfo_le_conditionalMutualInfo
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c) :
    conditionalStatisticMutualInfo ρ c hc ≤ conditionalMutualInfo ρ := by
  by_cases htop : conditionalMutualInfo ρ = ⊤
  · rw [htop]
    exact le_top
  · rw [conditionalMutualInfo_eq_lintegral_fiberMutualInfo_of_ne_top ρ htop]
    unfold conditionalStatisticMutualInfo
    exact lintegral_mono fun u =>
      mutualInfo_statistic_le
        (conditionalJointKernel ρ u)
        (coreAt c u)
        (measurable_coreAt c hc u)

section CountableCore

variable [Countable C] [MeasurableSingletonClass C]

/-- Conditional Shannon entropy of the deterministic countable core, computed
in each true `U` fiber of the randomized-encoder law. -/
noncomputable def conditionalStatisticEntropy
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c) : ENNReal :=
  ∫⁻ u,
    discreteShannonEntropy (conditionalStatisticJoint ρ c hc u).fst ∂ρ.fst

/-- A decoder `d(U,M)` recovers the deterministic core in almost every true
`U` fiber. -/
def StatisticFiberRecoverable
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c)
    (d : U × M → C) : Prop :=
  ∀ᵐ u ∂ρ.fst,
    (conditionalStatisticJoint ρ c hc u).map
        (decodedCopyMap (fun m => d (u, m))) =
      copyJoint (conditionalStatisticJoint ρ c hc u).fst

lemma measurable_decoderAt
    (d : U × M → C) (hd : Measurable d) (u : U) :
    Measurable (fun m => d (u, m)) := by
  exact hd.comp (measurable_const.prodMk measurable_id)

/-- Recoverability identifies conditional statistic information with the true
conditional Shannon entropy of the core. -/
theorem conditionalStatisticMutualInfo_eq_entropy_of_recoverable
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c)
    (d : U × M → C) (hd : Measurable d)
    (hrec : StatisticFiberRecoverable ρ c hc d) :
    conditionalStatisticMutualInfo ρ c hc =
      conditionalStatisticEntropy ρ c hc := by
  unfold conditionalStatisticMutualInfo conditionalStatisticEntropy
  apply lintegral_congr_ae
  filter_upwards [hrec] with u hu
  exact mutualInfo_eq_discreteShannonEntropy_of_recoverable
    (conditionalStatisticJoint ρ c hc u)
    (fun m => d (u, m))
    (measurable_decoderAt d hd u)
    hu

/-- P-INFO-03 lower-bound engine. For any possibly randomized encoder law, if
the deterministic countable core `C=c(U,H)` is recoverable from `(U,M)`, then
`H(C|U) ≤ I(H;M|U)`. -/
theorem conditionalStatisticEntropy_le_conditionalMutualInfo_of_recoverable
    (ρ : Measure (U × (H × M))) [IsProbabilityMeasure ρ]
    (c : U × H → C) (hc : Measurable c)
    (d : U × M → C) (hd : Measurable d)
    (hrec : StatisticFiberRecoverable ρ c hc d) :
    conditionalStatisticEntropy ρ c hc ≤ conditionalMutualInfo ρ := by
  calc
    conditionalStatisticEntropy ρ c hc =
        conditionalStatisticMutualInfo ρ c hc :=
      (conditionalStatisticMutualInfo_eq_entropy_of_recoverable
        ρ c hc d hd hrec).symm
    _ ≤ conditionalMutualInfo ρ :=
      conditionalStatisticMutualInfo_le_conditionalMutualInfo ρ c hc

end CountableCore

end

end UEOT.V3.InformationConditionalStatistic
