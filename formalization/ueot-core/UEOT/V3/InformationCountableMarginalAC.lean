import UEOT.V3.InformationDiscreteEntropy
import UEOT.V3.InformationEntropyBound
import UEOT.V3.InformationMutualInfoSymmetry
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.MeasureComp

namespace UEOT.V3.InformationCountableMarginalAC

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationEntropyBound
open UEOT.V3.InformationDiscreteEntropy
open UEOT.V3.InformationMutualInfoSymmetry

universe uC uM uX

variable {C : Type uC} {M : Type uM} {X : Type uX}
variable [MeasurableSpace C] [MeasurableSpace M]
variable [Countable C] [MeasurableSingletonClass C]
variable [StandardBorelSpace M] [Nonempty M]

theorem joint_absolutelyContinuous_prod_of_countable_fst
    (ρ : Measure (C × M)) [IsProbabilityMeasure ρ] :
    ρ ≪ ρ.fst.prod ρ.snd := by
  have hcopy : copyJoint ρ.fst ≪ ρ.fst.prod ρ.fst :=
    copyJoint_absolutelyContinuous_prod ρ.fst
  have hchan := hcopy.comp_right (retainFirstSendSecond ρ.condKernel)
  have hdis : ρ.fst ⊗ₘ ρ.condKernel = ρ :=
    Measure.disintegrate ρ ρ.condKernel
  have hsnd : ρ.condKernel ∘ₘ ρ.fst = ρ.snd := by
    have hs := congrArg Measure.snd hdis
    simpa using hs
  simpa [retainFirstSendSecond_comp_copyJoint,
    retainFirstSendSecond_comp_prod, hdis, hsnd] using hchan

theorem joint_absolutelyContinuous_prod_of_countable_snd
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (ρ : Measure (X × C)) [IsProbabilityMeasure ρ] :
    ρ ≪ ρ.fst.prod ρ.snd := by
  letI : IsProbabilityMeasure (ρ.map Prod.swap) :=
    (Measure.isProbabilityMeasure_map_iff measurable_swap.aemeasurable).2 inferInstance
  have h :=
    joint_absolutelyContinuous_prod_of_countable_fst (ρ.map Prod.swap)
  have hm := h.map measurable_swap
  have hleft : (ρ.map Prod.swap).map Prod.swap = ρ := by
    rw [Measure.map_map measurable_swap measurable_swap]
    calc
      ρ.map (Prod.swap ∘ Prod.swap) = ρ.map id := by
        apply Measure.map_congr
        filter_upwards with z
        cases z
        rfl
      _ = ρ := Measure.map_id
  have hright :
      ((ρ.map Prod.swap).fst.prod (ρ.map Prod.swap).snd).map Prod.swap =
        ρ.fst.prod ρ.snd := by
    rw [map_swap_fst ρ, map_swap_snd ρ]
    exact Measure.prod_swap
  rw [hleft, hright] at hm
  exact hm

end

end UEOT.V3.InformationCountableMarginalAC
