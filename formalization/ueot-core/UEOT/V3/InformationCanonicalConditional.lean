import UEOT.V3.InformationPredictiveAchievability
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# P-INFO-03 — conditional fibers of the canonical encoder

For the deterministic achieving encoder `M=C=c(U,H)`, the true conditional
law of `(H,C)` given `U=u` is the deterministic graph law obtained by drawing
`H ~ P(H|U=u)` and then setting `C=c(u,H)`.  This module proves that statement
by exhibiting an explicit disintegration and invoking uniqueness.
-/

namespace UEOT.V3.InformationCanonicalConditional

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationConditionalMutual
open UEOT.V3.InformationRandomEncoder
open UEOT.V3.InformationPredictiveAchievability

universe uU uH uC

variable {U : Type uU} {H : Type uH} {C : Type uC}
variable [MeasurableSpace U] [MeasurableSpace H] [MeasurableSpace C]
variable [StandardBorelSpace U] [StandardBorelSpace H] [StandardBorelSpace C]
variable [Nonempty H] [Nonempty C]

noncomputable def canonicalConditionalKernel
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c) : Kernel U (H × C) :=
  μ.condKernel ⊗ₖ Kernel.deterministic c hc

instance canonicalConditionalKernel_isMarkov
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c) :
    IsMarkovKernel (canonicalConditionalKernel μ c hc) := by
  unfold canonicalConditionalKernel
  infer_instance

theorem sourceFst_compProd_canonicalConditionalKernel
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c) :
    μ.fst ⊗ₘ canonicalConditionalKernel μ c hc =
      μ.map (canonicalCoreGraph c) := by
  unfold canonicalConditionalKernel
  have hdis : μ.fst ⊗ₘ μ.condKernel = μ :=
    Measure.disintegrate μ μ.condKernel
  have hpair : Measurable (fun uh : U × H => (uh, c uh)) :=
    measurable_id.prodMk hc
  calc
    μ.fst ⊗ₘ (μ.condKernel ⊗ₖ Kernel.deterministic c hc) =
        ((μ.fst ⊗ₘ μ.condKernel) ⊗ₘ Kernel.deterministic c hc).map
          MeasurableEquiv.prodAssoc := by
      symm
      exact Measure.compProd_assoc'
    _ = (μ ⊗ₘ Kernel.deterministic c hc).map
          MeasurableEquiv.prodAssoc := by rw [hdis]
    _ = (μ.map (fun uh : U × H => (uh, c uh))).map
          MeasurableEquiv.prodAssoc := by
      rw [Measure.compProd_deterministic hc]
    _ = μ.map (MeasurableEquiv.prodAssoc ∘
          fun uh : U × H => (uh, c uh)) := by
      exact Measure.map_map
        (MeasurableEquiv.measurable MeasurableEquiv.prodAssoc) hpair
    _ = μ.map (canonicalCoreGraph c) := by
      apply Measure.map_congr
      filter_upwards with uh
      rfl

theorem canonicalEncoderJoint_fst
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c) :
    (randomEncoderJoint μ (canonicalCoreEncoder c hc)).fst = μ.fst := by
  rw [randomEncoderJoint_canonicalCoreEncoder μ c hc]
  unfold Measure.fst
  rw [Measure.map_map measurable_fst (measurable_canonicalCoreGraph c hc)]
  change μ.map Prod.fst = μ.fst
  rfl

theorem canonicalConditionalKernel_ae_eq_condKernel
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c) :
    canonicalConditionalKernel μ c hc =ᵐ[μ.fst]
      (randomEncoderJoint μ (canonicalCoreEncoder c hc)).condKernel := by
  let ρ : Measure (U × (H × C)) :=
    randomEncoderJoint μ (canonicalCoreEncoder c hc)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  have hfst : ρ.fst = μ.fst := by
    dsimp [ρ]
    exact canonicalEncoderJoint_fst μ c hc
  have hreconstruct : ρ = ρ.fst ⊗ₘ canonicalConditionalKernel μ c hc := by
    rw [hfst]
    rw [sourceFst_compProd_canonicalConditionalKernel μ c hc]
    exact randomEncoderJoint_canonicalCoreEncoder μ c hc
  have huniq := ProbabilityTheory.eq_condKernel_of_measure_eq_compProd
    (ρ := ρ) (canonicalConditionalKernel μ c hc) hreconstruct
  change ∀ᵐ u ∂μ.fst,
    canonicalConditionalKernel μ c hc u =
      (randomEncoderJoint μ (canonicalCoreEncoder c hc)).condKernel u
  simpa [ρ, hfst] using huniq

section DiscreteCore

variable [Countable C] [MeasurableSingletonClass C]

theorem canonicalConditionalKernel_apply_eq_graph
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c) (u : U) :
    canonicalConditionalKernel μ c hc u =
      (μ.condKernel u).map (fun h => (h, c (u, h))) := by
  have hgraph : Measurable (fun h : H => (h, c (u, h))) :=
    measurable_id.prodMk
      (hc.comp (measurable_const.prodMk measurable_id))
  ext s hs
  unfold canonicalConditionalKernel
  rw [Kernel.compProd_deterministic_apply hc hs]
  rw [Measure.map_apply hgraph hs]
  rfl

end DiscreteCore

end

end UEOT.V3.InformationCanonicalConditional
