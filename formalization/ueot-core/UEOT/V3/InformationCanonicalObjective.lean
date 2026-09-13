import UEOT.V3.InformationCanonicalConditional
import UEOT.V3.InformationCountableMarginalAC
import UEOT.V3.InformationDeterministicGraph
import UEOT.V3.InformationConditionalStatistic
import UEOT.V3.InformationKernelKL

/-!
# P-INFO-03 — canonical encoder objective value

For the deterministic achieving encoder `M=C=c(U,H)`, this module computes the
conditional mutual-information objective exactly.  The proof does not assume
that the global CMI is finite.  Instead it rewrites both the true law and its
conditional-independence reference over the fixed source base `P(U)`, applies
the shared-base kernel KL integral theorem, and evaluates each conditional
fiber using the deterministic-graph identity `I(H;c(H)) = H(c(H))`.
-/

namespace UEOT.V3.InformationCanonicalObjective

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationCore
open UEOT.V3.InformationDiscreteEntropy
open UEOT.V3.InformationConditionalMutual
open UEOT.V3.InformationConditionalStatistic
open UEOT.V3.InformationRandomEncoder
open UEOT.V3.InformationPredictiveAchievability
open UEOT.V3.InformationCanonicalConditional
open UEOT.V3.InformationCountableMarginalAC
open UEOT.V3.InformationDeterministicGraph
open UEOT.V3.InformationKernelKL

universe uU uH uC

variable {U : Type uU} {H : Type uH} {C : Type uC}
variable [MeasurableSpace U] [MeasurableSpace H] [MeasurableSpace C]
variable [StandardBorelSpace U] [StandardBorelSpace H] [StandardBorelSpace C]
variable [Nonempty H] [Nonempty C]
variable [Countable C] [MeasurableSingletonClass C]

/-- The fiberwise conditional-independence reference associated with the
explicit canonical conditional kernel. -/
noncomputable def canonicalIndependenceKernel
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c) : Kernel U (H × C) :=
  (canonicalConditionalKernel μ c hc).fst ×ₖ
    (canonicalConditionalKernel μ c hc).snd

instance canonicalIndependenceKernel_isMarkov
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c) :
    IsMarkovKernel (canonicalIndependenceKernel μ c hc) := by
  unfold canonicalIndependenceKernel
  infer_instance

lemma canonicalIndependenceKernel_apply
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c) (u : U) :
    canonicalIndependenceKernel μ c hc u =
      (canonicalConditionalKernel μ c hc u).fst.prod
        (canonicalConditionalKernel μ c hc u).snd := by
  unfold canonicalIndependenceKernel
  rw [Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply]
  simp only [Measure.fst, Measure.snd]

/-- Every canonical conditional fiber is absolutely continuous with respect to
its product-of-marginals reference because its second coordinate is countable. -/
theorem canonicalConditionalKernel_ac_independence
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c) (u : U) :
    canonicalConditionalKernel μ c hc u ≪
      canonicalIndependenceKernel μ c hc u := by
  have h := joint_absolutelyContinuous_prod_of_countable_snd
    (canonicalConditionalKernel μ c hc u)
  simpa [canonicalIndependenceKernel_apply] using h

/-- **Exact objective value of the canonical encoder.**

`I(H;C|U)` under `C=c(U,H)` is the source conditional entropy of `C`, written
as the integral of the Shannon entropy of the conditional image law. -/
theorem canonicalEncoder_conditionalMutualInfo_eq_sourceEntropy
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (c : U × H → C) (hc : Measurable c) :
    conditionalMutualInfo
        (randomEncoderJoint μ (canonicalCoreEncoder c hc)) =
      ∫⁻ u,
        discreteShannonEntropy
          ((μ.condKernel u).map (coreAt c u)) ∂μ.fst := by
  let ρ : Measure (U × (H × C)) :=
    randomEncoderJoint μ (canonicalCoreEncoder c hc)
  let κ : Kernel U (H × C) := canonicalConditionalKernel μ c hc
  let η : Kernel U (H × C) := canonicalIndependenceKernel μ c hc
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  letI : IsMarkovKernel κ := by
    dsimp [κ]
    infer_instance
  letI : IsMarkovKernel η := by
    dsimp [η]
    infer_instance
  have hfst : ρ.fst = μ.fst := by
    dsimp [ρ]
    exact canonicalEncoderJoint_fst μ c hc
  have htrue : μ.fst ⊗ₘ κ = ρ := by
    dsimp [κ, ρ]
    calc
      μ.fst ⊗ₘ canonicalConditionalKernel μ c hc =
          μ.map (canonicalCoreGraph c) :=
        sourceFst_compProd_canonicalConditionalKernel μ c hc
      _ = randomEncoderJoint μ (canonicalCoreEncoder c hc) :=
        (randomEncoderJoint_canonicalCoreEncoder μ c hc).symm
  have hcond :
      κ =ᵐ[μ.fst] conditionalJointKernel ρ := by
    dsimp [κ, ρ]
    simpa [conditionalJointKernel] using
      (canonicalConditionalKernel_ae_eq_condKernel μ c hc)
  have hrefKernel :
      conditionalIndependenceKernel ρ =ᵐ[μ.fst] η := by
    filter_upwards [hcond] with u hu
    unfold conditionalIndependenceKernel
    dsimp [η, canonicalIndependenceKernel]
    rw [Kernel.prod_apply, Kernel.prod_apply,
      Kernel.fst_apply, Kernel.snd_apply,
      Kernel.fst_apply, Kernel.snd_apply]
    rw [← hu]
  have href :
      ρ.fst ⊗ₘ conditionalIndependenceKernel ρ =
        μ.fst ⊗ₘ η := by
    rw [hfst]
    exact Measure.compProd_congr hrefKernel
  have hac : ∀ᵐ u ∂μ.fst, κ u ≪ η u :=
    Filter.Eventually.of_forall fun u => by
      dsimp [κ, η]
      exact canonicalConditionalKernel_ac_independence μ c hc u
  unfold conditionalMutualInfo
  change InformationTheory.klDiv ρ
      (ρ.fst ⊗ₘ conditionalIndependenceKernel ρ) = _
  rw [href, ← htrue]
  rw [klDiv_compProd_right_eq_lintegral hac]
  apply lintegral_congr
  intro u
  have hκgraph := canonicalConditionalKernel_apply_eq_graph μ c hc u
  have hcore : Measurable (coreAt c u) := measurable_coreAt c hc u
  have hgraphInfo :=
    mutualInfo_deterministicGraph_eq_entropy_map
      (μ.condKernel u) (coreAt c u) hcore
  calc
    InformationTheory.klDiv (κ u) (η u) = mutualInfo (κ u) := by
      unfold mutualInfo
      dsimp [η]
      rw [canonicalIndependenceKernel_apply]
    _ = mutualInfo
        ((μ.condKernel u).map (deterministicGraph (coreAt c u))) := by
      rw [hκgraph]
      rfl
    _ = discreteShannonEntropy ((μ.condKernel u).map (coreAt c u)) :=
      hgraphInfo

end

end UEOT.V3.InformationCanonicalObjective
