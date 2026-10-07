import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Disintegration.Unique
import UEOT.V3.GeneralBayesPosterior

/-!
# Scientific Closure C1 — parameterized measurable belief recursion

This module closes the jointly-measurable posterior subproblem under the precise
regularity needed by Mathlib's parameterized disintegration theorem.  The latent
state `Z` is Standard Borel and nonempty; the observation measurable space `Y` is
countably generated.  The action space remains an arbitrary measurable space.

The construction is genuinely parameterized in the current probability belief and
action.  It builds one Markov joint law on `(belief, action)`, disintegrates that
joint law once, packages the resulting posterior as a jointly measurable
`ProbabilityMeasure Z`, and induces a Markov transition kernel on the whole belief
space.  For each fixed `(belief, action)` the selected posterior version agrees
almost everywhere, under the predictive observation law, with the existing
`GeneralBayesPosterior.posteriorKernel`; the underlying one-step joint law is
exactly the existing P-REF-02 joint law up to coordinate swap.

This is deliberately **not** a theorem for an arbitrary measurable observation
space.  The fully arbitrary-measurable-`Y` parameterized disintegration port stays
open unless an alternative common-version theorem supplies the missing regularity.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe uZ uA uY
variable {Z : Type uZ} {A : Type uA} {Y : Type uY}
variable [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace Y]

noncomputable def c1ProbDirac (a : A) : ProbabilityMeasure A :=
  ⟨Measure.dirac a, Measure.dirac.isProbabilityMeasure⟩

@[fun_prop] theorem measurable_c1ProbDirac : Measurable (c1ProbDirac : A → ProbabilityMeasure A) := by
  apply Measurable.subtype_mk
  exact Measure.measurable_dirac

noncomputable def c1BeliefActionMeasure (p : ProbabilityMeasure Z × A) : Measure (Z × A) :=
  p.1.toMeasure.prod (c1ProbDirac p.2).toMeasure

@[fun_prop] theorem measurable_c1BeliefActionMeasure :
    Measurable (c1BeliefActionMeasure : ProbabilityMeasure Z × A → Measure (Z × A)) := by
  exact ProbabilityMeasure.measurable_fun_prod.comp
    (measurable_fst.prodMk (measurable_c1ProbDirac.comp measurable_snd))

noncomputable def c1LiftedKernel
    (K : Kernel (Z × A) Y) [IsMarkovKernel K] :
    Kernel (ProbabilityMeasure Z × A) Y where
  toFun p := (c1BeliefActionMeasure p).bind K
  measurable' := (Measure.measurable_bind' K.measurable).comp measurable_c1BeliefActionMeasure

instance c1LiftedKernel_isMarkov (K : Kernel (Z × A) Y) [IsMarkovKernel K] :
    IsMarkovKernel (c1LiftedKernel K) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure ((c1BeliefActionMeasure p).bind K)
    unfold c1BeliefActionMeasure
    infer_instance

noncomputable def c1KeepActionTransition
    (P : Kernel (Z × A) Z) [IsMarkovKernel P] : Kernel (Z × A) (Z × A) :=
  P ⊗ₖ Kernel.deterministic (fun q : (Z × A) × Z => q.1.2) (by fun_prop)

instance c1KeepActionTransition_isMarkov
    (P : Kernel (Z × A) Z) [IsMarkovKernel P] :
    IsMarkovKernel (c1KeepActionTransition P) := by
  unfold c1KeepActionTransition
  infer_instance



theorem c1KeepActionTransition_comp_c1BeliefActionMeasure
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (b : ProbabilityMeasure Z) (a : A) :
    c1KeepActionTransition P ∘ₘ c1BeliefActionMeasure (b, a) =
      ((P.comap (fun z : Z => (z, a)) (by fun_prop)) ∘ₘ b.toMeasure).prod (Measure.dirac a) := by
  haveI : IsProbabilityMeasure (c1BeliefActionMeasure (b, a)) := by
    unfold c1BeliefActionMeasure
    infer_instance
  haveI : IsProbabilityMeasure (c1KeepActionTransition P ∘ₘ c1BeliefActionMeasure (b, a)) := by
    infer_instance
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.bind_apply (hs.prod ht) (c1KeepActionTransition P).aemeasurable]
  rw [Measure.prod_prod]
  unfold c1BeliefActionMeasure
  rw [MeasureTheory.lintegral_prod]
  · simp_rw [c1KeepActionTransition, Kernel.compProd_apply_prod hs ht]
    simp only [Kernel.deterministic_apply, Measure.dirac_apply' _ ht]
    simp_rw [MeasureTheory.setLIntegral_const]
    rw [show (c1ProbDirac a : Measure A) = Measure.dirac a by rfl]
    have hinner (x : Z) :
        Measurable (fun y : A => t.indicator 1 y * P (x, y) s) := by
      exact (measurable_const.indicator ht).mul
        ((Kernel.measurable_coe P hs).comp measurable_prodMk_left)
    simp_rw [MeasureTheory.lintegral_dirac' a (hinner _)]
    rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
    simp_rw [Kernel.comap_apply]
    by_cases ha : a ∈ t <;> simp [ha]
  · exact (Kernel.measurable_coe _ (hs.prod ht)).aemeasurable

noncomputable def c1ObservationLatent
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] : Kernel (Z × A) (Y × Z) :=
  O ⊗ₖ Kernel.deterministic (fun q : (Z × A) × Y => q.1.1) (by fun_prop)



theorem c1ObservationLatent_comp_predicted_prod_dirac
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (b : ProbabilityMeasure Z) (a : A) :
    c1ObservationLatent O ∘ₘ
        ((UEOT.V3.GeneralBayesPosterior.predictedLaw b.toMeasure P a).prod (Measure.dirac a)) =
      (UEOT.V3.GeneralBayesPosterior.jointLaw b.toMeasure P O a).map Prod.swap := by
  let μ : Measure Z := UEOT.V3.GeneralBayesPosterior.predictedLaw b.toMeasure P a
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact UEOT.V3.GeneralBayesPosterior.predictedLaw_isProbability b.toMeasure P a
  haveI : IsProbabilityMeasure (μ.prod (Measure.dirac a)) := by
    infer_instance
  haveI : IsMarkovKernel (c1ObservationLatent O) := by
    unfold c1ObservationLatent
    infer_instance
  haveI : IsProbabilityMeasure (c1ObservationLatent O ∘ₘ μ.prod (Measure.dirac a)) := by
    infer_instance
  apply Measure.ext_prod
  intro u s hu hs
  change
    (c1ObservationLatent O ∘ₘ μ.prod (Measure.dirac a)) (u ×ˢ s) =
      (UEOT.V3.GeneralBayesPosterior.jointLaw b.toMeasure P O a).map Prod.swap (u ×ˢ s)
  rw [Measure.bind_apply (hu.prod hs) (c1ObservationLatent O).aemeasurable]
  rw [Measure.map_apply measurable_swap (hu.prod hs)]
  have hswap : Prod.swap ⁻¹' (u ×ˢ s) = s ×ˢ u := by
    ext p
    simp
  rw [hswap]
  unfold UEOT.V3.GeneralBayesPosterior.jointLaw
  rw [Measure.compProd_apply_prod hs hu]
  rw [MeasureTheory.lintegral_prod]
  · simp_rw [c1ObservationLatent, Kernel.compProd_apply_prod hu hs]
    simp only [Kernel.deterministic_apply, Measure.dirac_apply' _ hs]
    simp_rw [MeasureTheory.setLIntegral_const]
    have hinner (z : Z) :
        Measurable (fun a' : A => s.indicator 1 z * O (z, a') u) := by
      exact measurable_const.mul ((Kernel.measurable_coe O hu).comp measurable_prodMk_left)
    simp_rw [MeasureTheory.lintegral_dirac' a (hinner _)]
    change (∫⁻ z, s.indicator 1 z * O (z, a) u ∂μ) =
      ∫⁻ z in s, (UEOT.V3.GeneralBayesPosterior.fixedActionKernel O a) z u ∂μ
    rw [← MeasureTheory.lintegral_indicator hs]
    apply MeasureTheory.lintegral_congr
    intro z
    by_cases hz : z ∈ s <;>
      simp [hz, UEOT.V3.GeneralBayesPosterior.fixedActionKernel, Kernel.comap_apply]
  · exact (Kernel.measurable_coe _ (hu.prod hs)).aemeasurable

instance c1ObservationLatent_isMarkov
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    IsMarkovKernel (c1ObservationLatent O) := by
  unfold c1ObservationLatent
  infer_instance

noncomputable def c1OneStepJoint
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] : Kernel (Z × A) (Y × Z) :=
  c1ObservationLatent O ∘ₖ c1KeepActionTransition P

instance c1OneStepJoint_isMarkov
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    IsMarkovKernel (c1OneStepJoint P O) := by
  unfold c1OneStepJoint
  infer_instance

noncomputable def c1BeliefActionJoint
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    Kernel (ProbabilityMeasure Z × A) (Y × Z) :=
  c1LiftedKernel (c1OneStepJoint P O)

instance c1BeliefActionJoint_isMarkov
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    IsMarkovKernel (c1BeliefActionJoint P O) := by
  unfold c1BeliefActionJoint
  infer_instance



theorem c1BeliefActionJoint_apply_eq_existing
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (b : ProbabilityMeasure Z) (a : A) :
    c1BeliefActionJoint P O (b, a) =
      (UEOT.V3.GeneralBayesPosterior.jointLaw b.toMeasure P O a).map Prod.swap := by
  change c1OneStepJoint P O ∘ₘ c1BeliefActionMeasure (b, a) = _
  rw [c1OneStepJoint, ← Measure.comp_assoc,
    c1KeepActionTransition_comp_c1BeliefActionMeasure P b a]
  change c1ObservationLatent O ∘ₘ
      (UEOT.V3.GeneralBayesPosterior.predictedLaw b.toMeasure P a).prod (Measure.dirac a) = _
  exact c1ObservationLatent_comp_predicted_prod_dirac P O b a



theorem c1BeliefActionJoint_fst_eq_observationLaw
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (b : ProbabilityMeasure Z) (a : A) :
    Kernel.fst (c1BeliefActionJoint P O) (b, a) =
      UEOT.V3.GeneralBayesPosterior.observationLaw b.toMeasure P O a := by
  rw [Kernel.fst_apply, c1BeliefActionJoint_apply_eq_existing P O b a]
  change (Measure.map Prod.swap
      (UEOT.V3.GeneralBayesPosterior.jointLaw b.toMeasure P O a)).fst = _
  rw [Measure.fst_map_swap]
  unfold UEOT.V3.GeneralBayesPosterior.jointLaw
  rw [Measure.snd_compProd]
  rfl

section Posterior

variable [StandardBorelSpace Z] [Nonempty Z]
variable [MeasurableSpace.CountablyGenerated Y]

noncomputable def c1ParametricPosteriorKernel
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    Kernel ((ProbabilityMeasure Z × A) × Y) Z :=
  Kernel.condKernel (c1BeliefActionJoint P O)

instance c1ParametricPosteriorKernel_isMarkov
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    IsMarkovKernel (c1ParametricPosteriorKernel P O) := by
  unfold c1ParametricPosteriorKernel
  infer_instance

noncomputable def c1ParametricPosteriorBelief
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (x : (ProbabilityMeasure Z × A) × Y) : ProbabilityMeasure Z :=
  ⟨c1ParametricPosteriorKernel P O x, by infer_instance⟩

@[fun_prop] theorem measurable_c1ParametricPosteriorBelief
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    Measurable (c1ParametricPosteriorBelief P O) := by
  apply Measurable.subtype_mk
  exact (c1ParametricPosteriorKernel P O).measurable



noncomputable def c1PosteriorSection
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (b : ProbabilityMeasure Z) (a : A) : Kernel Y Z :=
  (c1ParametricPosteriorKernel P O).comap (fun y => ((b, a), y)) (by fun_prop)

instance c1PosteriorSection_isMarkov
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (b : ProbabilityMeasure Z) (a : A) :
    IsMarkovKernel (c1PosteriorSection P O b a) := by
  unfold c1PosteriorSection
  infer_instance

theorem c1PosteriorSection_factorization
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (b : ProbabilityMeasure Z) (a : A) :
    UEOT.V3.GeneralBayesPosterior.observationLaw b.toMeasure P O a ⊗ₘ
        c1PosteriorSection P O b a =
      (UEOT.V3.GeneralBayesPosterior.jointLaw b.toMeasure P O a).map Prod.swap := by
  let rho : Measure (Y × Z) := c1BeliefActionJoint P O (b, a)
  have hsec :
      (c1PosteriorSection P O b a : Y → Measure Z) =ᵐ[
          Kernel.fst (c1BeliefActionJoint P O) (b, a)]
        (rho.condKernel : Y → Measure Z) := by
    have h := Kernel.condKernel_apply_eq_condKernel (c1BeliefActionJoint P O) (b, a)
    simpa [c1PosteriorSection, c1ParametricPosteriorKernel, rho, Kernel.comap_apply,
      Function.comp_def] using h
  calc
    UEOT.V3.GeneralBayesPosterior.observationLaw b.toMeasure P O a ⊗ₘ
        c1PosteriorSection P O b a
        = Kernel.fst (c1BeliefActionJoint P O) (b, a) ⊗ₘ c1PosteriorSection P O b a := by
            rw [c1BeliefActionJoint_fst_eq_observationLaw P O b a]
    _ = Kernel.fst (c1BeliefActionJoint P O) (b, a) ⊗ₘ rho.condKernel :=
      Measure.compProd_congr hsec
    _ = rho := by
      change rho.fst ⊗ₘ rho.condKernel = rho
      exact Measure.disintegrate rho rho.condKernel
    _ = (UEOT.V3.GeneralBayesPosterior.jointLaw b.toMeasure P O a).map Prod.swap :=
      c1BeliefActionJoint_apply_eq_existing P O b a

theorem c1ParametricPosteriorKernel_ae_eq_existing
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (b : ProbabilityMeasure Z) (a : A) :
    (fun y => c1ParametricPosteriorKernel P O ((b, a), y)) =ᵐ[
        UEOT.V3.GeneralBayesPosterior.observationLaw b.toMeasure P O a]
      UEOT.V3.GeneralBayesPosterior.posteriorKernel b.toMeasure P O a := by
  have hfac := c1PosteriorSection_factorization P O b a
  have hae := ProbabilityTheory.ae_eq_posterior_of_compProd_eq
    (κ := UEOT.V3.GeneralBayesPosterior.fixedActionKernel O a)
    (μ := UEOT.V3.GeneralBayesPosterior.predictedLaw b.toMeasure P a)
    (η := c1PosteriorSection P O b a) (by
      simpa [UEOT.V3.GeneralBayesPosterior.observationLaw,
        UEOT.V3.GeneralBayesPosterior.jointLaw] using hfac)
  simpa [c1PosteriorSection, Kernel.comap_apply, Function.comp_def,
    UEOT.V3.GeneralBayesPosterior.observationLaw,
    UEOT.V3.GeneralBayesPosterior.posteriorKernel] using hae



noncomputable def c1BeliefObservationKernel
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    Kernel (ProbabilityMeasure Z × A) Y :=
  Kernel.fst (c1BeliefActionJoint P O)

instance c1BeliefObservationKernel_isMarkov
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    IsMarkovKernel (c1BeliefObservationKernel P O) := by
  unfold c1BeliefObservationKernel
  infer_instance

noncomputable def c1BeliefStepJoint
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    Kernel (ProbabilityMeasure Z × A) (Y × ProbabilityMeasure Z) :=
  c1BeliefObservationKernel P O ⊗ₖ
    Kernel.deterministic
      (fun q : (ProbabilityMeasure Z × A) × Y => c1ParametricPosteriorBelief P O q)
      (measurable_c1ParametricPosteriorBelief P O)

instance c1BeliefStepJoint_isMarkov
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    IsMarkovKernel (c1BeliefStepJoint P O) := by
  unfold c1BeliefStepJoint
  infer_instance

noncomputable def c1BeliefTransitionKernel
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    Kernel (ProbabilityMeasure Z × A) (ProbabilityMeasure Z) :=
  Kernel.snd (c1BeliefStepJoint P O)

instance c1BeliefTransitionKernel_isMarkov
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    IsMarkovKernel (c1BeliefTransitionKernel P O) := by
  unfold c1BeliefTransitionKernel
  infer_instance



theorem c1BeliefTransitionKernel_apply_eq_map
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (b : ProbabilityMeasure Z) (a : A) :
    c1BeliefTransitionKernel P O (b, a) =
      (UEOT.V3.GeneralBayesPosterior.observationLaw b.toMeasure P O a).map
        (fun y => c1ParametricPosteriorBelief P O ((b, a), y)) := by
  apply Measure.ext
  intro s hs
  unfold c1BeliefTransitionKernel
  rw [Kernel.snd_apply']
  · unfold c1BeliefStepJoint
    rw [Kernel.compProd_apply (measurable_snd hs)]
    have hpre (y : Y) : Prod.mk y ⁻¹' Prod.snd ⁻¹' s = s := by
      ext x
      rfl
    simp_rw [hpre]
    simp_rw [Kernel.deterministic_apply' (measurable_c1ParametricPosteriorBelief P O) _ hs]
    rw [Measure.map_apply]
    · rw [show c1BeliefObservationKernel P O (b, a) =
          UEOT.V3.GeneralBayesPosterior.observationLaw b.toMeasure P O a by
          exact c1BeliefActionJoint_fst_eq_observationLaw P O b a]
      have hpost : Measurable (fun y => c1ParametricPosteriorBelief P O ((b, a), y)) :=
        (measurable_c1ParametricPosteriorBelief P O).comp (measurable_const.prodMk measurable_id)
      rw [← MeasureTheory.lintegral_indicator_one (hs.preimage hpost)]
      apply MeasureTheory.lintegral_congr
      intro y
      by_cases hy : c1ParametricPosteriorBelief P O ((b, a), y) ∈ s <;> simp [hy]
    · exact (measurable_c1ParametricPosteriorBelief P O).comp
        (measurable_const.prodMk measurable_id)
    · exact hs
  · exact hs

/-- **C1 countably-generated terminal theorem.**  Under Standard-Borel latent state
and countably-generated observations, Bayesian recursion admits one jointly measurable
posterior-belief version and therefore a Markov kernel on the whole probability-belief
space.  Its fixed-`(belief, action)` sections agree almost everywhere with the existing
P-REF-02 posterior, and its transition law is exactly the push-forward of the predictive
observation law through that posterior version. -/
theorem c1_countablyGenerated_belief_recursion
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O] :
    Measurable (c1ParametricPosteriorBelief P O) ∧
      IsMarkovKernel (c1BeliefTransitionKernel P O) ∧
      (∀ (b : ProbabilityMeasure Z) (a : A),
        (fun y => c1ParametricPosteriorKernel P O ((b, a), y)) =ᵐ[
            UEOT.V3.GeneralBayesPosterior.observationLaw b.toMeasure P O a]
          UEOT.V3.GeneralBayesPosterior.posteriorKernel b.toMeasure P O a) ∧
      (∀ (b : ProbabilityMeasure Z) (a : A),
        c1BeliefTransitionKernel P O (b, a) =
          (UEOT.V3.GeneralBayesPosterior.observationLaw b.toMeasure P O a).map
            (fun y => c1ParametricPosteriorBelief P O ((b, a), y))) := by
  exact ⟨measurable_c1ParametricPosteriorBelief P O, inferInstance,
    c1ParametricPosteriorKernel_ae_eq_existing P O,
    c1BeliefTransitionKernel_apply_eq_map P O⟩

end Posterior

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure
