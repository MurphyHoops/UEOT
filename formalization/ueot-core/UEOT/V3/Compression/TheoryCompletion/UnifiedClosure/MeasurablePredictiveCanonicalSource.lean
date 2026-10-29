import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveResponseRecursion
import UEOT.V3.PredictionDependent
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
Original commitment: the canonical predictive state is sufficient and relatively minimal for actual futures.
Existing result: the SAME P/O run disintegrates its full observed prefix and retained terminal latent through its computed filter.
Premise reduced: derive the actual past/future conditional kernels before invoking original P-PRED-01 minimality.
Model: Standard Borel nonempty latent, countably generated observations; countable actions for all-word minimality.
Consumers: original PredictionDependent sufficiency/a.e./sigma endpoints and actual response(last computed belief).

A finite word is a declared open-loop intervention AFTER the same generated past.
It need not agree with that past policy's future decisions. No latent resampling,
new action, source alteration or success selection is performed. Competing
sufficient statistics admit measurable Markov predictors of all these word
futures; this is the definition of sufficiency, not a source-implementation
certificate. The arbitrary adaptive-protocol scope remains separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveCanonicalSource
open MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel
open MeasurablePredictiveJointPath MeasurablePredictiveLatentPath
open MeasurablePredictiveResponseRecursion
open scoped ENNReal ProbabilityTheory
noncomputable section

variable {Z A W : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace W]

abbrev ObservedPrefix (Z A W : Type*) [MeasurableSpace Z] (n : ℕ) :=
  (i : Finset.Iic n) → RecordState Z A W

abbrev RawResponse (A W : Type*) [MeasurableSpace W] :=
  (u : List A) → Measure (ObservationWord W u)

/-- Forget only the proof that each coordinate has probability mass one. -/
def rawResponse (c : ResponseState A W) : RawResponse A W := fun u => (c u).toMeasure

omit [MeasurableSpace A] in
@[fun_prop] theorem measurable_rawResponse : Measurable (rawResponse (A:=A) (W:=W)) := by
  apply measurable_pi_lambda
  intro u
  exact measurable_subtype_coe.comp (measurable_pi_apply u)

omit [MeasurableSpace A] in
/-- This embedding concerns ALL probability arrays, not the possibly non-Borel
image of realizable source responses. Existing subtype/Pi APIs supply it. -/
theorem rawResponse_embedding [Countable A] :
    MeasurableEmbedding (rawResponse (A:=A) (W:=W)) := by
  have hp : MeasurableSet {c : RawResponse A W | ∀ u, IsProbabilityMeasure (c u)} := by
    have h : MeasurableSet (⋂ u : List A, {c : RawResponse A W | IsProbabilityMeasure (c u)}) :=
      MeasurableSet.iInter (fun u =>
        ProbabilityMeasure.measurableSet_isProbabilityMeasure.preimage (measurable_pi_apply u))
    convert h using 1
    ext c
    simp
  let e : {c : RawResponse A W // ∀ u, IsProbabilityMeasure (c u)} ≃ᵐ ResponseState A W :=
    MeasurableEquiv.subtypePiEquivPi
  exact (MeasurableEmbedding.subtype_coe hp).comp e.symm.measurableEmbedding


/-- The original dependent coordinate kernel, restricted to probability arrays,
is a genuine Markov predictor on the entire declared canonical state space. -/
def probabilityCoordinateKernel (u : List A) : Kernel (ResponseState A W) (ObservationWord W u) :=
  (UEOT.V3.PredictionDependent.coordinateKernel u).comap rawResponse measurable_rawResponse

instance probabilityCoordinateKernel_isMarkov (u : List A) :
    IsMarkovKernel (probabilityCoordinateKernel (W:=W) u) where
  isProbabilityMeasure c := by change IsProbabilityMeasure (c u).toMeasure; infer_instance

/-- Last recursively computed belief of the entire recorded past. -/
def terminalPosterior (n : ℕ) (h : ObservedPrefix Z A W n) : ProbabilityMeasure Z :=
  (h (lastHistoryIndex n)).2.1

@[fun_prop] theorem measurable_terminalPosterior (n : ℕ) :
    Measurable (terminalPosterior (Z:=Z) (A:=A) (W:=W) n) := by
  unfold terminalPosterior
  fun_prop

variable [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W]
variable (P : Kernel (Z × A) Z) [IsMarkovKernel P]
variable (O : Kernel (Z × A) W) [IsMarkovKernel O]

/-- Actual recorded-prefix probability law of the same controlled source. -/
def observedPrefixLaw (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) : Measure (ObservedPrefix Z A W n) :=
  (homTrajMeasure (Measure.dirac r) (recordKernel P O π)).map (Preorder.frestrictLe n)

instance observedPrefixLaw_isProbability
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) : IsProbabilityMeasure (observedPrefixLaw P O π r n) :=
  Measure.isProbabilityMeasure_map (Preorder.measurable_frestrictLe n).aemeasurable

/-- Future kernel obtained by running the SAME P/O word from the actual
computed terminal filter; no future conditional law is supplied as a field. -/
def futureKernel (n : ℕ) (u : List A) : Kernel (ObservedPrefix Z A W n) (ObservationWord W u) :=
  wordKernel P O u ∘ₖ terminalBelief n

instance futureKernel_isMarkov (n : ℕ) (u : List A) : IsMarkovKernel (futureKernel P O n u) := by
  unfold futureKernel
  infer_instance

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
@[simp] theorem futureKernel_apply (n : ℕ) (u : List A) (h : ObservedPrefix Z A W n) :
    futureKernel P O n u h = responseLaw P O (terminalPosterior n h) u := rfl

/-- Generate the real past with π, retain its actual terminal latent, and
continue that latent with the specified word under the SAME P/O source. -/
def actualPastFutureJoint (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) (u : List A) :
    Measure (ObservedPrefix Z A W n × ObservationWord W u) :=
  (Kernel.id ∥ₖ wordKernel P O u) ∘ₘ
    (((homTrajMeasure (latentLift r) (physicalKernel P O π)).map
      (Preorder.frestrictLe n)).map (summarizePrefix n))

/-- Source-derived actual conditional-future factorization. The complete past
and terminal latent are coupled by the proved physical/filter prefix identity;
the continuation executes from that retained latent, without drawing a new one. -/
theorem actual_past_future_factorization
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) (u : List A) :
    actualPastFutureJoint P O π r n u =
      observedPrefixLaw P O π r n ⊗ₘ futureKernel P O n u := by
  rw [actualPastFutureJoint,actual_finite_prefix_consistency,Measure.parallelComp_comp_compProd]
  rfl

instance actualPastFutureJoint_isProbability
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) (u : List A) :
    IsProbabilityMeasure (actualPastFutureJoint P O π r n u) := by
  rw [actual_past_future_factorization]
  infer_instance

/-- In particular the intervention leaves the full already generated past law
unchanged; it does not reselect or regenerate successful past histories. -/
theorem actual_past_marginal
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) (u : List A) :
    (actualPastFutureJoint P O π r n u).fst = observedPrefixLaw P O π r n := by
  rw [actual_past_future_factorization,Measure.fst_compProd]


/-- Actual measurable past/future rectangles use this derived conditional law. -/
theorem actual_past_future_rectangle
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) (u : List A)
    {B : Set (ObservedPrefix Z A W n)} {E : Set (ObservationWord W u)}
    (hB : MeasurableSet B) (hE : MeasurableSet E) :
    actualPastFutureJoint P O π r n u (B ×ˢ E) =
      ∫⁻ h in B, futureKernel P O n u h E ∂observedPrefixLaw P O π r n := by
  rw [actual_past_future_factorization,Measure.compProd_apply_prod hB hE]

private theorem observedPrefixLaw_zero
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) :
    observedPrefixLaw P O π r 0 = Measure.dirac (fun _ : Finset.Iic 0 => r) := by
  rw [observedPrefixLaw,homTrajMeasure_prefix_zero,Measure.map_dirac' (by fun_prop)]
  rfl

theorem actual_initial_future_law
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (u : List A) :
    (actualPastFutureJoint P O π r 0 u).snd = responseLaw P O r.2.1 u := by
  rw [actual_past_future_factorization,Measure.snd_compProd,observedPrefixLaw_zero,
    Measure.dirac_bind (futureKernel P O 0 u).measurable]
  rfl

/-- Complete canonical response array of the actual observed past. -/
def actualRawCanonical (n : ℕ) (h : ObservedPrefix Z A W n) : RawResponse A W :=
  fun u => futureKernel P O n u h

def actualCanonical (n : ℕ) (h : ObservedPrefix Z A W n) : ResponseState A W :=
  response P O (terminalPosterior n h)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
@[fun_prop] theorem measurable_actualRawCanonical (n : ℕ) :
    Measurable (actualRawCanonical P O n) :=
  UEOT.V3.PredictionDependent.canonical_measurable (futureKernel P O n)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
@[fun_prop] theorem measurable_actualCanonical (n : ℕ) :
    Measurable (actualCanonical P O n) :=
  (measurable_response P O).comp (measurable_terminalPosterior n)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
/-- The original raw-Measure canonical state and the actual ProbabilityMeasure
response state are precisely the same coordinates under the subtype embedding. -/
theorem actualRawCanonical_eq_response (n : ℕ) (h : ObservedPrefix Z A W n) :
    actualRawCanonical P O n h = rawResponse (actualCanonical P O n h) := rfl

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
/-- Original P-PRED-01 sufficiency endpoint consumes the source-derived kernels. -/
theorem actual_raw_kernel_sufficient (n : ℕ) :
    ∀ u, ∃ L : Kernel (RawResponse A W) (ObservationWord W u),
      ∀ h, futureKernel P O n u h = L (actualRawCanonical P O n h) :=
  UEOT.V3.PredictionDependent.canonical_kernel_sufficient (futureKernel P O n)


omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
/-- The actual probability-valued canonical state itself admits Markov word
predictors; the raw original coordinate predictor was reused by comap. -/
theorem actual_probability_kernel_sufficient (n : ℕ) (u : List A) (h : ObservedPrefix Z A W n) :
    futureKernel P O n u h = probabilityCoordinateKernel u (actualCanonical P O n h) := rfl

/-- Original conditional-expectation consumer on the real past law. Together
with actual_past_future_factorization this is the actual future-event tower step. -/
theorem actual_canonical_event_condExp
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) (u : List A)
    {E : Set (ObservationWord W u)} (hE : MeasurableSet E) :
    (observedPrefixLaw P O π r n)[(fun h => (futureKernel P O n u h).real E) |
      MeasurableSpace.comap (actualRawCanonical P O n) inferInstance] =
        (fun h => (futureKernel P O n u h).real E) :=
  UEOT.V3.PredictionDependent.canonical_event_condExp (observedPrefixLaw P O π r n)
    (futureKernel P O n) (fun _ _ => by infer_instance) u hE

/-- Original minimality is now about the actual past and actual future source,
not an independently supplied family of purported predictive kernels. -/
theorem actual_raw_ae_minimal [Countable A]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) {S : Type*} [MeasurableSpace S]
    (s : ObservedPrefix Z A W n → S) (_hs : Measurable s)
    (L : (u : List A) → Kernel S (ObservationWord W u))
    (hL : ∀ u, ∀ᵐ h ∂observedPrefixLaw P O π r n, futureKernel P O n u h = L u (s h)) :
    UEOT.V3.PredictionAE.AEFactors (observedPrefixLaw P O π r n) (actualRawCanonical P O n) s :=
  UEOT.V3.PredictionDependent.canonical_ae_minimal (observedPrefixLaw P O π r n)
    (futureKernel P O n) s L hL

/-- Original mod-null sigma-information minimality consumer for this same
source-derived complete finite-word response family. -/
theorem actual_raw_ae_sigma_minimal [Countable A]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) {S : Type*} [MeasurableSpace S]
    (s : ObservedPrefix Z A W n → S) (_hs : Measurable s)
    (L : (u : List A) → Kernel S (ObservationWord W u))
    (hL : ∀ u, ∀ᵐ h ∂observedPrefixLaw P O π r n, futureKernel P O n u h = L u (s h)) :
    UEOT.V3.PredictionAE.AESigmaLE (observedPrefixLaw P O π r n) (actualRawCanonical P O n) s :=
  UEOT.V3.PredictionDependent.canonical_ae_sigma_minimal (observedPrefixLaw P O π r n)
    (futureKernel P O n) s L hL

/-- Minimality transports to the actual probability-valued response itself.
The extension below is only the existing embedding of ALL probability arrays;
no inverse map to a latent belief or realizable response image is used. -/
theorem actual_response_ae_minimal [Countable A]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) {S : Type*} [MeasurableSpace S]
    (s : ObservedPrefix Z A W n → S) (hs : Measurable s)
    (L : (u : List A) → Kernel S (ObservationWord W u))
    (hL : ∀ u, ∀ᵐ h ∂observedPrefixLaw P O π r n, futureKernel P O n u h = L u (s h)) :
    UEOT.V3.PredictionAE.AEFactors (observedPrefixLaw P O π r n) (actualCanonical P O n) s := by
  obtain ⟨d,hd,hEq⟩ := actual_raw_ae_minimal P O π r n s hs L hL
  obtain ⟨decode,hdecode,hleft⟩ := (rawResponse_embedding (A:=A) (W:=W)).exists_measurable_extend
    measurable_id (fun _ => ⟨response P O r.2.1⟩)
  refine ⟨decode ∘ d,hdecode.comp hd,?_⟩
  filter_upwards [hEq] with h hh
  rw [actualRawCanonical_eq_response] at hh
  exact (congr_fun hleft (actualCanonical P O n h)).symm.trans (congrArg decode hh)

theorem actual_response_ae_sigma_minimal [Countable A]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) {S : Type*} [MeasurableSpace S]
    (s : ObservedPrefix Z A W n → S) (hs : Measurable s)
    (L : (u : List A) → Kernel S (ObservationWord W u))
    (hL : ∀ u, ∀ᵐ h ∂observedPrefixLaw P O π r n, futureKernel P O n u h = L u (s h)) :
    UEOT.V3.PredictionAE.AESigmaLE (observedPrefixLaw P O π r n) (actualCanonical P O n) s :=
  UEOT.V3.PredictionAE.aeFactors_sigmaLE _ (actual_response_ae_minimal P O π r n s hs L hL)

/-- Append the literal record of this allowed first action/observation. -/
def appendObserved (n : ℕ) (h : ObservedPrefix Z A W n) (a : A) (w : W) :
    ObservedPrefix Z A W (n+1) :=
  appendHistory n (h,nextRecord P O (h (lastHistoryIndex n),(a,w)))

theorem terminalPosterior_appendObserved (n : ℕ) (h : ObservedPrefix Z A W n) (a : A) (w : W) :
    terminalPosterior (n+1) (appendObserved P O n h a w) =
      UEOT.V3.Compression.TheoryCompletion.ScientificClosure.c1ParametricPosteriorBelief P O
        ((terminalPosterior n h,a),w) := by
  simp [terminalPosterior,appendObserved,appendHistory,lastHistoryIndex,IicProdIoc_def,
    MeasurableEquiv.piSingleton,nextRecord]

/-- Source-to-canonical P-PRED-03: on the actual observation law, append and
update the SAME computed response state. Standard Borel observations are needed
only for the previously constructed ambient update, not source minimality. -/
theorem actual_canonical_recursion [StandardBorelSpace W] [Countable A]
    (n : ℕ) (h : ObservedPrefix Z A W n) (a : A) :
    ∀ᵐ w ∂UEOT.V3.GeneralBayesPosterior.observationLaw (terminalPosterior n h).toMeasure P O a,
      ambientUpdate P O (actualCanonical P O n h) a w =
        actualCanonical P O (n+1) (appendObserved P O n h a w) := by
  simpa only [actualCanonical,terminalPosterior_appendObserved] using
    ambientUpdate_actual_response_ae P O (terminalPosterior n h) a

namespace GaussianConsumer
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open MeasurablePredictiveResponseRecursion.GaussianConsumer

/-- The new source joint/predictor consumer is used at the existing actual
shared-Gaussian model. Its future is non-atomic even from a deterministic past. -/
theorem actual_initial_gaussian_future
    (π : Kernel (ℕ × ProbabilityMeasure (ℝ × ℝ)) ℤ) [IsMarkovKernel π] :
    ((actualPastFutureJoint allowedSource allowedObservation π
      (0,(c1ProbDirac (0,0),Sum.inl ())) 0 [(0 : ℤ)]).snd).fst = gaussianReal 0 1 := by
  rw [actual_initial_future_law]
  exact MeasurablePredictiveResponseRecursion.GaussianConsumer.origin_first_response

end GaussianConsumer

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveCanonicalSource
