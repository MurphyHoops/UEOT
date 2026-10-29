import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveLatentPath
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSourceWitness

/-!
Original commitment: the canonical finite-protocol predictive state has a source-derived recursion.
Existing result: actual P/O joint execution, a common measurable posterior and its disintegration.
Reduced premise: compute all word laws and derive continuation factorization; no Bayes-numerator field.
Model: nonempty Standard Borel latent, countable actions; countably generated observations for a.e. recursion, Standard Borel for ambient update.
Consumer: equality of complete response coordinates implies the SAME posterior responses agree a.e.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveResponseRecursion
open MeasureTheory ProbabilityTheory
open UEOT.V3.GeneralBayesPosterior
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open MeasurablePredictiveLatentPath
open scoped ENNReal
noncomputable section
variable {Z A W : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace W]

/-- Ordered observation tuple for the specified open-loop action word.
Repeated actions remain separate positions; the empty tuple is PUnit. -/
abbrev ObservationWord (W : Type*) (u : List A) := List.TProd (fun _ : A => W) u

instance observationWord_standardBorel [StandardBorelSpace W] (u : List A) :
    StandardBorelSpace (ObservationWord W u) := by
  induction u with
  | nil => exact inferInstanceAs (StandardBorelSpace PUnit)
  | cons a u ih =>
      change StandardBorelSpace (W × ObservationWord W u)
      infer_instance

instance observationWord_countablyGenerated [MeasurableSpace.CountablyGenerated W] (u : List A) :
    MeasurableSpace.CountablyGenerated (ObservationWord W u) := by
  induction u with
  | nil => exact inferInstanceAs (MeasurableSpace.CountablyGenerated PUnit)
  | cons a u ih =>
      change MeasurableSpace.CountablyGenerated (W × ObservationWord W u)
      infer_instance

/-- Actual finite observation law from a latent state. Each step samples P,
then O at the same next latent/action, and retains the entire ordered observation tuple. -/
def wordKernel (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O] :
    (u : List A) → Kernel Z (ObservationWord W u)
  | [] => Kernel.const Z (Measure.dirac PUnit.unit)
  | a :: u => (Kernel.id ∥ₖ wordKernel P O u) ∘ₖ fixedActionKernel (c1OneStepJoint P O) a

instance wordKernel_isMarkov (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O] (u : List A) :
    IsMarkovKernel (wordKernel P O u) := by
  induction u with
  | nil => change IsMarkovKernel (Kernel.const Z (Measure.dirac PUnit.unit)); infer_instance
  | cons a u ih =>
      change IsMarkovKernel ((Kernel.id ∥ₖ wordKernel P O u) ∘ₖ
        fixedActionKernel (c1OneStepJoint P O) a)
      infer_instance

/-- Response coordinates use actual probability laws, including every finite
measurable observation cylinder, not a finite selection of scalar tests. -/
abbrev ResponseState (A W : Type*) [MeasurableSpace W] :=
  (u : List A) → ProbabilityMeasure (ObservationWord W u)

def responseLaw (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (b : ProbabilityMeasure Z) (u : List A) : Measure (ObservationWord W u) :=
  wordKernel P O u ∘ₘ b.toMeasure

instance responseLaw_isProbability (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (b : ProbabilityMeasure Z) (u : List A) : IsProbabilityMeasure (responseLaw P O b u) := by
  unfold responseLaw
  infer_instance

def response (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (b : ProbabilityMeasure Z) : ResponseState A W :=
  fun u => ⟨responseLaw P O b u, by infer_instance⟩

@[fun_prop] theorem measurable_response (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O] : Measurable (response P O) := by
  apply measurable_pi_iff.mpr
  intro u
  apply Measurable.subtype_mk
  exact (Measure.measurable_bind' (wordKernel P O u).measurable).comp measurable_subtype_coe

variable [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W]
variable (P : Kernel (Z × A) Z) [IsMarkovKernel P]
variable (O : Kernel (Z × A) W) [IsMarkovKernel O]

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
/-- Actual primitive P/O execution averaged under b is the existing common C1 joint law. -/
theorem primitive_joint_mixture (b : ProbabilityMeasure Z) (a : A) :
    fixedActionKernel (c1OneStepJoint P O) a ∘ₘ b.toMeasure = c1BeliefActionJoint P O (b,a) := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro F hF
  rw [Measure.lintegral_bind (fixedActionKernel (c1OneStepJoint P O) a).aemeasurable hF.aemeasurable]
  exact (lintegral_belief_joint P O b a F hF).symm

/-- Continuation execution follows the SAME actually updated posterior. -/
def continuationPosterior (b : ProbabilityMeasure Z) (a : A) (u : List A) :
    Kernel W (ObservationWord W u) :=
  wordKernel P O u ∘ₖ c1PosteriorSection P O b a

instance continuationPosterior_isMarkov (b : ProbabilityMeasure Z) (a : A) (u : List A) :
    IsMarkovKernel (continuationPosterior P O b a u) := by unfold continuationPosterior; infer_instance

/-- The required observation/continuation numerator is derived from the
literal longer source word, not supplied as a factorization premise. -/
theorem actual_word_factorization (b : ProbabilityMeasure Z) (a : A) (u : List A) :
    observationLaw b.toMeasure P O a ⊗ₘ continuationPosterior P O b a u =
      responseLaw P O b (a :: u) := by
  have : IsProbabilityMeasure (observationLaw b.toMeasure P O a) := by
    unfold observationLaw
    infer_instance
  change observationLaw b.toMeasure P O a ⊗ₘ continuationPosterior P O b a u =
    ((Kernel.id ∥ₖ wordKernel P O u) ∘ₖ fixedActionKernel (c1OneStepJoint P O) a) ∘ₘ b.toMeasure
  rw [← Measure.comp_assoc, primitive_joint_mixture,
    c1BeliefActionJoint_apply_eq_existing, ← c1PosteriorSection_factorization,
    Measure.parallelComp_comp_compProd]
  rfl

/-- A current response coordinate also contains the actual first-observation law. -/
theorem response_first_marginal (b : ProbabilityMeasure Z) (a : A) (u : List A) :
    (responseLaw P O b (a :: u)).fst = observationLaw b.toMeasure P O a := by
  have : IsProbabilityMeasure (observationLaw b.toMeasure P O a) := by
    unfold observationLaw
    infer_instance
  rw [← actual_word_factorization, Measure.fst_compProd]

/-- Equal complete current responses imply equal actual observation laws. -/
theorem same_response_observationLaw (b c : ProbabilityMeasure Z)
    (h : response P O b = response P O c) (a : A) :
    observationLaw b.toMeasure P O a = observationLaw c.toMeasure P O a := by
  have hs := congrArg (fun s : ResponseState A W => (s [a]).toMeasure.fst) h
  exact (response_first_marginal P O b a []).symm.trans
    (hs.trans (response_first_marginal P O c a []))

/-- Each whole continuation-word law agrees under its actual observation law. -/
theorem same_response_posterior_word_ae (b c : ProbabilityMeasure Z)
    (h : response P O b = response P O c) (a : A) (u : List A) :
    ∀ᵐ w ∂observationLaw b.toMeasure P O a,
      response P O (c1ParametricPosteriorBelief P O ((b,a),w)) u =
        response P O (c1ParametricPosteriorBelief P O ((c,a),w)) u := by
  have : IsProbabilityMeasure (observationLaw b.toMeasure P O a) := by
    unfold observationLaw
    infer_instance
  have hfac : observationLaw b.toMeasure P O a ⊗ₘ continuationPosterior P O b a u =
      observationLaw b.toMeasure P O a ⊗ₘ continuationPosterior P O c a u := by
    rw [actual_word_factorization, same_response_observationLaw P O b c h a,
      actual_word_factorization]
    exact congrArg (fun s : ResponseState A W => (s (a::u)).toMeasure) h
  have hae := Kernel.ae_eq_of_compProd_eq hfac
  filter_upwards [hae] with w hw
  apply Subtype.ext
  change (wordKernel P O u ∘ₘ c1ParametricPosteriorKernel P O ((b,a),w)) =
    wordKernel P O u ∘ₘ c1ParametricPosteriorKernel P O ((c,a),w)
  simpa only [continuationPosterior, Kernel.comp_apply, c1PosteriorSection, Kernel.comap_apply] using hw

/-- Countability of ALL action words gives ONE common full-measure set on which
all complete posterior response coordinates agree, for this same first action. -/
theorem same_response_posterior_response_ae [Countable A] (b c : ProbabilityMeasure Z)
    (h : response P O b = response P O c) (a : A) :
    ∀ᵐ w ∂observationLaw b.toMeasure P O a,
      response P O (c1ParametricPosteriorBelief P O ((b,a),w)) =
        response P O (c1ParametricPosteriorBelief P O ((c,a),w)) := by
  have hall : ∀ᵐ w ∂observationLaw b.toMeasure P O a, ∀ u : List A,
      response P O (c1ParametricPosteriorBelief P O ((b,a),w)) u =
        response P O (c1ParametricPosteriorBelief P O ((c,a),w)) u :=
    ae_all_iff.mpr (same_response_posterior_word_ae P O b c h a)
  filter_upwards [hall] with w hw
  exact funext hw

-- Universal ambient disintegration needs Standard Borel continuation outputs.
-- The source-derived common-a.e. statement above only needs countable generation.
variable [StandardBorelSpace W]

/-- Universal disintegration of one supplied response coordinate. The actual
source proves the continuation observation type is nonempty, solely to select
a total Markov version on null observations; no latent-state section is used. -/
def coordinatePosterior (u : List A) :
    Kernel (ProbabilityMeasure (W × ObservationWord W u) × W) (ObservationWord W u) := by
  letI : Nonempty (ObservationWord W u) :=
    nonempty_of_isProbabilityMeasure (wordKernel P O u Classical.ofNonempty)
  exact Kernel.condKernel (beliefKernel (Z := W × ObservationWord W u))

instance coordinatePosterior_isMarkov (u : List A) :
    IsMarkovKernel (coordinatePosterior P O u) := by
  unfold coordinatePosterior
  infer_instance

/-- A common measurable probability-valued conditional version. -/
def coordinateUpdate (u : List A)
    (q : ProbabilityMeasure (W × ObservationWord W u) × W) :
    ProbabilityMeasure (ObservationWord W u) :=
  ⟨coordinatePosterior P O u q, by infer_instance⟩

omit [StandardBorelSpace Z] in
@[fun_prop] theorem measurable_coordinateUpdate (u : List A) :
    Measurable (coordinateUpdate P O u) := by
  apply Measurable.subtype_mk
  exact (coordinatePosterior P O u).measurable

omit [StandardBorelSpace Z] in
/-- Every supplied joint response law is reconstructed by this common version. -/
theorem coordinateUpdate_factorization (u : List A)
    (q : ProbabilityMeasure (W × ObservationWord W u)) :
    q.toMeasure.fst ⊗ₘ (coordinatePosterior P O u).comap (fun w => (q,w)) (by fun_prop) =
      q.toMeasure := by
  let : Nonempty (ObservationWord W u) :=
    nonempty_of_isProbabilityMeasure (wordKernel P O u Classical.ofNonempty)
  have h := congrArg (fun K : Kernel (ProbabilityMeasure (W × ObservationWord W u))
      (W × ObservationWord W u) => K q)
    (Kernel.disintegrate (beliefKernel (Z := W × ObservationWord W u))
      (Kernel.condKernel (beliefKernel (Z := W × ObservationWord W u))))
  rw [Kernel.compProd_apply_eq_compProd_sectR] at h
  exact h

/-- The ambient coordinate update reads the ACTUAL longer action-word law.
Off the source image it is a measurable extension, not an assertion that every
arbitrary array is realizable by a latent belief. -/
def ambientUpdate (c : ResponseState A W) (a : A) (w : W) : ResponseState A W :=
  fun u => coordinateUpdate P O u (c (a::u),w)

omit [StandardBorelSpace Z] in
/-- No quotient-image Standard Borel or measurable section assumption is required. -/
theorem measurable_ambientUpdate_fixed (a : A) :
    Measurable (fun q : ResponseState A W × W => ambientUpdate P O q.1 a q.2) := by
  apply measurable_pi_iff.mpr
  intro u
  exact (measurable_coordinateUpdate P O u).comp
    (((measurable_pi_apply (a::u)).comp measurable_fst).prodMk measurable_snd)

omit [StandardBorelSpace Z] in
/-- Discrete countable protocol labels give joint state/action/observation
measurability on the entire ambient response array, not only the source image. -/
theorem measurable_ambientUpdate_joint [Countable A] [MeasurableSingletonClass A] :
    Measurable (fun q : ResponseState A W × (A × W) => ambientUpdate P O q.1 q.2.1 q.2.2) := by
  have hm : Measurable (fun q : A × (ResponseState A W × W) =>
      ambientUpdate P O q.2.1 q.1 q.2.2) :=
    measurable_from_prod_countable_right (measurable_ambientUpdate_fixed P O)
  exact hm.comp (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))

/-- The universal coordinate conditional is the ACTUAL posterior continuation
response, under the actual first-observation law. -/
theorem ambientUpdate_word_actual_ae (b : ProbabilityMeasure Z) (a : A) (u : List A) :
    ∀ᵐ w ∂observationLaw b.toMeasure P O a,
      ambientUpdate P O (response P O b) a w u =
        response P O (c1ParametricPosteriorBelief P O ((b,a),w)) u := by
  have : IsProbabilityMeasure (observationLaw b.toMeasure P O a) := by
    unfold observationLaw
    infer_instance
  have hc := coordinateUpdate_factorization P O u (response P O b (a::u))
  change (responseLaw P O b (a::u)).fst ⊗ₘ
    (coordinatePosterior P O u).comap (fun w => (response P O b (a::u),w)) (by fun_prop) =
      responseLaw P O b (a::u) at hc
  rw [response_first_marginal] at hc
  have heq := Kernel.ae_eq_of_compProd_eq ((actual_word_factorization P O b a u).trans hc.symm)
  filter_upwards [heq] with w hw
  apply Subtype.ext
  change coordinatePosterior P O u (response P O b (a::u),w) =
    wordKernel P O u ∘ₘ c1ParametricPosteriorKernel P O ((b,a),w)
  simpa only [continuationPosterior, Kernel.comp_apply, c1PosteriorSection, Kernel.comap_apply] using hw.symm

/-- ONE common full-measure set carries the source-derived recursion of every
finite-protocol response coordinate. This is an actual ambient measurable update. -/
theorem ambientUpdate_actual_response_ae [Countable A] (b : ProbabilityMeasure Z) (a : A) :
    ∀ᵐ w ∂observationLaw b.toMeasure P O a,
      ambientUpdate P O (response P O b) a w =
        response P O (c1ParametricPosteriorBelief P O ((b,a),w)) := by
  have hall : ∀ᵐ w ∂observationLaw b.toMeasure P O a, ∀ u : List A,
      ambientUpdate P O (response P O b) a w u =
        response P O (c1ParametricPosteriorBelief P O ((b,a),w)) u :=
    ae_all_iff.mpr (ambientUpdate_word_actual_ae P O b a)
  filter_upwards [hall] with w hw
  exact funext hw

section AmbientTransition
variable [Countable A] [MeasurableSingletonClass A]

/-- Select a longer protocol coordinate measurably, using the declared discrete
countable action labels. The array itself need not be source-realizable. -/
def selectedWordKernel (u : List A) : Kernel (ResponseState A W × A) (W × ObservationWord W u) where
  toFun q := (q.1 (q.2::u)).toMeasure
  measurable' := by
    apply measurable_from_prod_countable_left
    intro a
    change Measurable (fun c : ResponseState A W => (c (a::u)).toMeasure)
    exact measurable_subtype_coe.comp (measurable_pi_apply (a::u))

instance selectedWordKernel_isMarkov (u : List A) : IsMarkovKernel (selectedWordKernel (W:=W) u) where
  isProbabilityMeasure q := by change IsProbabilityMeasure (q.1 (q.2::u)).toMeasure; infer_instance

/-- First-observation law is read from the actual one-action response coordinate. -/
def ambientObservation : Kernel (ResponseState A W × A) W :=
  Kernel.fst (selectedWordKernel (W:=W) [])

instance ambientObservation_isMarkov : IsMarkovKernel (ambientObservation (A:=A) (W:=W)) := by
  unfold ambientObservation
  infer_instance

/-- Ambient predictive-state transition computed solely from response arrays,
the allowed action and the sampled observation. No section to latent beliefs. -/
def ambientResponseKernel : Kernel (ResponseState A W × A) (ResponseState A W) :=
  Kernel.snd (ambientObservation ⊗ₖ Kernel.deterministic
    (fun q : (ResponseState A W × A) × W => ambientUpdate P O q.1.1 q.1.2 q.2)
    (by
      have hm := measurable_ambientUpdate_joint P O
      exact hm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))))

instance ambientResponseKernel_isMarkov : IsMarkovKernel (ambientResponseKernel P O) := by
  unfold ambientResponseKernel
  infer_instance

omit [StandardBorelSpace Z] in
/-- Literal row semantics of the computed ambient response transition. -/
theorem ambientResponseKernel_apply (c : ResponseState A W) (a : A) :
    ambientResponseKernel P O (c,a) = (ambientObservation (c,a)).map (ambientUpdate P O c a) := by
  have hu : Measurable (ambientUpdate P O c a) :=
    (measurable_ambientUpdate_fixed P O a).comp (measurable_const.prodMk measurable_id)
  apply (Measure.ext_iff_lintegral _).mpr
  intro F hF
  rw [ambientResponseKernel, Kernel.lintegral_snd _ _ hF, Kernel.lintegral_compProd]
  simp_rw [Kernel.lintegral_deterministic' _ hF]
  rw [lintegral_map hF hu]
  all_goals fun_prop

omit [StandardBorelSpace W] in
/-- On an actual source response, the computed marginal equals its actual observation law. -/
theorem ambientObservation_actual (b : ProbabilityMeasure Z) (a : A) :
    ambientObservation (response P O b,a) = observationLaw b.toMeasure P O a := by
  exact response_first_marginal P O b a []

/-- Actual general-source C1 consumer: one jointly measurable ambient kernel
factors the SAME source's posterior response transition at EVERY initial belief.
The source image need not be asserted Borel or supplied with a measurable section. -/
theorem actual_C1_response_kernel_factor (b : ProbabilityMeasure Z) (a : A) :
    (c1BeliefTransitionKernel P O (b,a)).map (response P O) =
      ambientResponseKernel P O (response P O b,a) := by
  have hp : Measurable (fun w => c1ParametricPosteriorBelief P O ((b,a),w)) :=
    (measurable_c1ParametricPosteriorBelief P O).comp (measurable_const.prodMk measurable_id)
  rw [c1BeliefTransitionKernel_apply_eq_map, Measure.map_map (measurable_response P O) hp,
    ambientResponseKernel_apply, ambientObservation_actual]
  apply Measure.map_congr
  filter_upwards [ambientUpdate_actual_response_ae P O b a] with w hw
  exact hw.symm

/-- Equal canonical responses therefore give the same actual next-response law. -/
theorem same_response_next_law (b c : ProbabilityMeasure Z)
    (h : response P O b = response P O c) (a : A) :
    (c1BeliefTransitionKernel P O (b,a)).map (response P O) =
      (c1BeliefTransitionKernel P O (c,a)).map (response P O) := by
  rw [actual_C1_response_kernel_factor, actual_C1_response_kernel_factor, h]

end AmbientTransition

namespace GaussianConsumer
open MeasurablePredictiveSourceWitness

private instance witnessSource_isMarkov : IsMarkovKernel actualSource := by
  unfold actualSource
  have : IsProbabilityMeasure noise := by unfold noise; infer_instance
  infer_instance

/-- A countable, genuinely controlled restriction of the existing continuous
shared-Gaussian source: the allowed drift is any integer. -/
def allowedSource : Kernel ((ℝ × ℝ) × ℤ) (ℝ × ℝ) :=
  actualSource.comap (fun xa => (xa.1,(xa.2 : ℝ))) (by fun_prop)

instance allowedSource_isMarkov : IsMarkovKernel allowedSource := by
  unfold allowedSource
  infer_instance

def allowedObservation : Kernel ((ℝ × ℝ) × ℤ) ℝ := MeasurablePredictiveSource.observation

instance allowedObservation_isMarkov : IsMarkovKernel allowedObservation := by
  unfold allowedObservation
  infer_instance

/-- Non-atomic common realization of the new COMPLETE response-state C1 consumer. -/
theorem actual_gaussian_response_factor (b : ProbabilityMeasure (ℝ × ℝ)) (a : ℤ) :
    (c1BeliefTransitionKernel allowedSource allowedObservation (b,a)).map
      (response allowedSource allowedObservation) =
      ambientResponseKernel allowedSource allowedObservation
        (response allowedSource allowedObservation b,a) :=
  actual_C1_response_kernel_factor allowedSource allowedObservation b a

/-- The first coordinate really is a nonzero Gaussian source law, rather than
an isolated positive-mass-observation Bayes calculation. -/
theorem origin_first_response :
    (responseLaw allowedSource allowedObservation (c1ProbDirac (0,0)) [(0 : ℤ)]).fst =
      gaussianReal 0 1 := by
  have hP : fixedActionKernel allowedSource (0 : ℤ) = fixedActionKernel actualSource (0 : ℝ) := by
    ext x s hs
    simp only [fixedActionKernel, allowedSource, Kernel.comap_apply, Int.cast_zero]
  have hO : fixedActionKernel allowedObservation (0 : ℤ) =
      fixedActionKernel (MeasurablePredictiveSource.observation (A:=ℝ)) (0 : ℝ) := by
    ext x s hs
    rfl
  rw [response_first_marginal, observationLaw, predictedLaw, hP, hO]
  exact origin_observation_law

end GaussianConsumer

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveResponseRecursion
