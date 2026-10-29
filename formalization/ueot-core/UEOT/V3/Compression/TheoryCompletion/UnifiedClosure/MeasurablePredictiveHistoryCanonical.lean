import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveWordController

/-!
Original commitment: canonical predictive conclusions apply after a genuinely arbitrary observed-history past.
Existing result: same-source one-step latent/posterior consistency and actual finite/countable history paths.
Premise reduced: derive full past/retained-latent and past/future laws without a visible-belief-policy restriction.
Model: one SAME P/O source, arbitrary measurable full-history past controller; future memory is explicitly registered.
Consumer: source-derived canonical sufficiency/minimality for fresh adaptive futures on this actual past law.

The new source bridge is an induction over the public one-step consistency and
existing prefix append interfaces. It does not reference private declaration
names of frozen modules. Future memory may be a measurable function of the
retained observed prefix; in that case the sufficient state retains BOTH the
response and that memory. Canonical-alone minimality below uses empty fresh
future memory. No different-memory identification is asserted.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveHistoryCanonical
open MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel
open MeasurablePredictiveHistoryControl MeasurablePredictiveResponseRecursion
open MeasurablePredictiveWordController
open scoped ENNReal
attribute [local fun_prop] measurable_appendHistory
noncomputable section
variable {Z A W : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace W]
local instance : MeasurableSpace (History A W) := historySpace A W

abbrev ObservedPrefix (Z A W : Type*) [MeasurableSpace Z] (n : ℕ) :=
  (i : Finset.Iic n) → BeliefHistory Z A W

variable [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W]
variable (P : Kernel (Z × A) Z) [IsMarkovKernel P]
variable (O : Kernel (Z × A) W) [IsMarkovKernel O]
variable (π : HistoryPolicy A W) [IsMarkovKernel π]

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
private theorem lintegral_historyLatentLift (r : BeliefHistory Z A W)
    (F : BeliefHistory Z A W × Z → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q, F q ∂historyLatentLift r) = ∫⁻ x, F (r,x) ∂r.1.toMeasure := by
  rw [historyLatentLift,Kernel.id,Kernel.lintegral_deterministic_prod measurable_id _ _ hF]
  rfl

def summarizePrefix (n : ℕ)
    (h : (i : Finset.Iic n) → BeliefHistory Z A W × Z) :
    ((i : Finset.Iic n) → BeliefHistory Z A W) × Z :=
  (mapHistory Prod.fst n h,(h (lastHistoryIndex n)).2)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
@[fun_prop] theorem measurable_summarizePrefix (n : ℕ) :
    Measurable (summarizePrefix (Z:=Z) (A:=A) (W:=W) n) := by
  unfold summarizePrefix
  exact (measurable_mapHistory Prod.fst measurable_fst n).prodMk
    (measurable_snd.comp (measurable_pi_apply _))

def terminalBelief (n : ℕ) : Kernel ((i : Finset.Iic n) → BeliefHistory Z A W) Z :=
  MeasurablePredictiveLatentPath.beliefKernel.comap (fun h => (h (lastHistoryIndex n)).1) (by fun_prop)

private instance terminalBelief_isMarkov (n : ℕ) :
    IsMarkovKernel (terminalBelief (Z:=Z) (A:=A) (W:=W) n) := by
  unfold terminalBelief
  infer_instance

private theorem appendHistory_last {S : Type*} [MeasurableSpace S] (n : ℕ)
    (h : (i : Finset.Iic n) → S) (s : S) :
    appendHistory n (h,s) (lastHistoryIndex (n+1)) = s := by
  simp [appendHistory,lastHistoryIndex,IicProdIoc_def,MeasurableEquiv.piSingleton]

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
private theorem summarize_append (n : ℕ)
    (h : (i : Finset.Iic n) → BeliefHistory Z A W × Z) (q : BeliefHistory Z A W × Z) :
    summarizePrefix (n+1) (appendHistory n (h,q)) =
      (appendHistory n ((summarizePrefix n h).1,q.1),q.2) := by
  rw [summarizePrefix,mapHistory_appendHistory,appendHistory_last]
  rfl

/-- Every complete history-controller prefix has its actual retained latent
conditionally distributed as the SAME recursively computed posterior. -/
theorem actual_prefix_latent_consistency (r : BeliefHistory Z A W) (n : ℕ) :
    (((homTrajMeasure (historyLatentLift r) (physicalHistoryKernel P O π)).map
      (Preorder.frestrictLe n)).map (summarizePrefix n)) =
      ((homTrajMeasure (Measure.dirac r) (beliefHistoryKernel P O π)).map
        (Preorder.frestrictLe n)) ⊗ₘ terminalBelief n := by
  induction n with
  | zero =>
    apply (Measure.ext_iff_lintegral _).mpr
    intro F hF
    rw [lintegral_map hF (measurable_summarizePrefix 0),
      homTrajMeasure_prefix_zero, lintegral_map (f := fun h => F (summarizePrefix 0 h)) (by fun_prop) (by fun_prop),
      lintegral_historyLatentLift r _ (by fun_prop),
      Measure.lintegral_compProd hF, homTrajMeasure_prefix_zero,
      Measure.map_dirac' (by fun_prop), lintegral_dirac' _ (by fun_prop)]
    rfl
  | succ n ih =>
    let K := physicalHistoryKernel P O π
    let L := beliefHistoryKernel P O π
    let μ := (homTrajMeasure (historyLatentLift r) K).map (Preorder.frestrictLe n)
    let ν := (homTrajMeasure (Measure.dirac r) L).map (Preorder.frestrictLe n)
    let : IsMarkovKernel (homHistoryKernel K n) := isMarkovKernel_homHistoryKernel K n
    let : IsMarkovKernel (homHistoryKernel L n) := isMarkovKernel_homHistoryKernel L n
    apply (Measure.ext_iff_lintegral _).mpr
    intro F hF
    let G : (((i : Finset.Iic n) → BeliefHistory Z A W) × Z) → ℝ≥0∞ := fun hz =>
      ∫⁻ q, F (appendHistory n (hz.1,q.1),q.2) ∂K (hz.1 (lastHistoryIndex n),hz.2)
    have hG : Measurable G := by
      change Measurable (fun hz => ∫⁻ q, F (appendHistory n (hz.1,q.1),q.2)
        ∂(K.comap (fun hz : (((i : Finset.Iic n) → BeliefHistory Z A W) × Z) =>
          (hz.1 (lastHistoryIndex n),hz.2)) (by fun_prop)) hz)
      apply Measurable.lintegral_kernel_prod_right
      exact hF.comp ((measurable_appendHistory n).comp
        (measurable_fst.fst.prodMk measurable_snd.fst) |>.prodMk measurable_snd.snd)
    have hleft : (∫⁻ h, F h ∂((homTrajMeasure (historyLatentLift r) K).map
        (Preorder.frestrictLe (n+1))).map (summarizePrefix (n+1))) =
        ∫⁻ hz, G hz ∂ν ⊗ₘ terminalBelief n := by
      rw [lintegral_map hF (measurable_summarizePrefix (n+1)),
        ← homTrajMeasure_prefix_succ,
        lintegral_map (f := fun h => F (summarizePrefix (n+1) h)) (by fun_prop) (measurable_appendHistory n),
        Measure.lintegral_compProd (by fun_prop)]
      change (∫⁻ h, ∫⁻ q, F (summarizePrefix (n+1) (appendHistory n (h,q)))
        ∂K (h (lastHistoryIndex n)) ∂μ) = _
      simp_rw [summarize_append]
      change (∫⁻ h, G (summarizePrefix n h) ∂μ) = _
      rw [← lintegral_map hG (measurable_summarizePrefix n)]
      exact congrArg (fun ρ => ∫⁻ hz, G hz ∂ρ) ih
    rw [hleft, Measure.lintegral_compProd hG]
    have hJ : Measurable (fun h : (i : Finset.Iic (n+1)) → BeliefHistory Z A W =>
        ∫⁻ z, F (h,z) ∂terminalBelief (n+1) h) :=
      Measurable.lintegral_kernel_prod_right hF
    rw [Measure.lintegral_compProd hF, ← homTrajMeasure_prefix_succ,
      lintegral_map hJ (measurable_appendHistory n),
      Measure.lintegral_compProd (f := fun p =>
        ∫⁻ z, F (appendHistory n p,z) ∂terminalBelief (n+1) (appendHistory n p))
        (hJ.comp (measurable_appendHistory n))]
    apply lintegral_congr
    intro h
    change (∫⁻ z, G (h,z) ∂(h (lastHistoryIndex n)).1.toMeasure) = _
    have hstep := congrArg (fun ρ : Measure (BeliefHistory Z A W × Z) =>
      ∫⁻ q, F (appendHistory n (h,q.1),q.2) ∂ρ)
      (actual_history_one_step_consistency P O π (h (lastHistoryIndex n)))
    rw [Measure.lintegral_bind K.aemeasurable (by fun_prop),
      lintegral_historyLatentLift _ _ (by fun_prop),
      Measure.lintegral_bind historyLatentLift.aemeasurable (by fun_prop)] at hstep
    change (∫⁻ z, G (h,z) ∂(h (lastHistoryIndex n)).1.toMeasure) = _ at hstep
    rw [hstep]
    apply lintegral_congr
    intro q
    rw [lintegral_historyLatentLift _ _ (by fun_prop)]
    simp only [terminalBelief, Kernel.comap_apply, MeasurablePredictiveLatentPath.beliefKernel, appendHistory_last]
    rfl


/-- Actual full observed-prefix law for the arbitrary full-history controller. -/
def observedPrefixLaw (r : BeliefHistory Z A W) (n : ℕ) : Measure (ObservedPrefix Z A W n) :=
  (homTrajMeasure (Measure.dirac r) (beliefHistoryKernel P O π)).map (Preorder.frestrictLe n)

instance observedPrefixLaw_isProbability (r : BeliefHistory Z A W) (n : ℕ) :
    IsProbabilityMeasure (observedPrefixLaw P O π r n) :=
  Measure.isProbabilityMeasure_map (Preorder.measurable_frestrictLe n).aemeasurable

/-- Its interpretation as the actual physical experiment is the existing
public path transport, with no policy change or hidden-state read. -/
theorem observedPrefixLaw_physical (r : BeliefHistory Z A W) (n : ℕ) :
    observedPrefixLaw P O π r n =
      ((homTrajMeasure (historyLatentLift r) (physicalHistoryKernel P O π)).map
        (Preorder.frestrictLe n)).map (mapHistory Prod.fst n) :=
  (actual_finite_belief_history_path P O π r n).symm

def terminalPosterior (n : ℕ) (h : ObservedPrefix Z A W n) : ProbabilityMeasure Z :=
  (h (lastHistoryIndex n)).1

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
@[fun_prop] theorem measurable_terminalPosterior (n : ℕ) :
    Measurable (terminalPosterior (Z:=Z) (A:=A) (W:=W) n) := by unfold terminalPosterior; fun_prop

/-- Existing trajectory construction, exposed here only as a parameterized kernel. -/
private def pathKernel {S : Type*} [MeasurableSpace S] (Q : Kernel S S) [IsMarkovKernel Q] :
    Kernel S (ℕ → S) :=
  letI : ∀ n, IsMarkovKernel (homHistoryKernel Q n) := fun n => isMarkovKernel_homHistoryKernel Q n
  (Kernel.traj (homHistoryKernel Q) 0).comap (fun s => fun _ : Finset.Iic 0 => s)
    (measurable_pi_lambda _ (fun _ => measurable_id))

private instance pathKernel_isMarkov {S : Type*} [MeasurableSpace S]
    (Q : Kernel S S) [IsMarkovKernel Q] : IsMarkovKernel (pathKernel Q) := by unfold pathKernel; infer_instance

private theorem pathKernel_comp_measure {S : Type*} [MeasurableSpace S]
    (Q : Kernel S S) [IsMarkovKernel Q] (μ : Measure S) :
    pathKernel Q ∘ₘ μ = homTrajMeasure μ Q := by
  let : ∀ n, IsMarkovKernel (homHistoryKernel Q n) := fun n => isMarkovKernel_homHistoryKernel Q n
  let η : Kernel ((i : Finset.Iic (0 : ℕ)) → S) (ℕ → S) :=
    Kernel.traj (X:=fun _ : ℕ => S) (homHistoryKernel Q) 0
  change (η.comap (fun s => fun _ : Finset.Iic 0 => s) _) ∘ₘ μ =
    η ∘ₘ μ.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => S)).symm
  ext E hE
  rw [Measure.bind_apply hE (Kernel.aemeasurable _),Measure.bind_apply hE (Kernel.aemeasurable _),
    lintegral_map (η.measurable_coe hE) (by fun_prop)]
  rfl

variable [StandardBorelSpace W]
variable (ρ : HistoryPolicy A W) [IsMarkovKernel ρ]

private def physicalPathKernel : Kernel (BeliefHistory Z A W × Z) (ℕ → History A W) :=
  (pathKernel (physicalHistoryKernel P O ρ)).map (mapPath (fun q => q.1.2))

private instance physicalPathKernel_isMarkov : IsMarkovKernel (physicalPathKernel P O ρ) := by
  unfold physicalPathKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_mapPath _ (by fun_prop))

private theorem physicalPathKernel_comp_lift (r : BeliefHistory Z A W) :
    physicalPathKernel P O ρ ∘ₘ historyLatentLift r =
      MeasurablePredictiveAdaptiveCanonical.actualAdaptiveLaw P O ρ r.1 r.2 := by
  rw [MeasurablePredictiveAdaptiveCanonical.actualAdaptiveLaw,← pathKernel_comp_measure,
    Measure.map_comp _ _ (measurable_mapPath _ (by fun_prop))]
  rfl

/-- Future execution starts at the ACTUAL terminal latent, carrying the declared
new control memory. It advances that retained latent throughout the continuation. -/
def futureFromRetained (n : ℕ) (memory : ObservedPrefix Z A W n → History A W) (hm : Measurable memory) :
    Kernel (ObservedPrefix Z A W n × Z) (ℕ → History A W) :=
  (physicalPathKernel P O ρ).comap
    (fun hx => ((terminalPosterior n hx.1,memory hx.1),hx.2)) (by fun_prop)

instance futureFromRetained_isMarkov (n : ℕ) (memory : ObservedPrefix Z A W n → History A W)
    (hm : Measurable memory) : IsMarkovKernel (futureFromRetained P O ρ n memory hm) := by
  unfold futureFromRetained
  infer_instance

/-- Measurable conditional future kernel obtained from the source posterior.
The actual past/future law below DERIVES its conditional interpretation. -/
def futureKernel (n : ℕ) (memory : ObservedPrefix Z A W n → History A W) (hm : Measurable memory) :
    Kernel (ObservedPrefix Z A W n) (ℕ → History A W) :=
  futureFromRetained P O ρ n memory hm ∘ₖ (Kernel.id ×ₖ terminalBelief n)

instance futureKernel_isMarkov (n : ℕ) (memory : ObservedPrefix Z A W n → History A W)
    (hm : Measurable memory) : IsMarkovKernel (futureKernel P O ρ n memory hm) := by
  unfold futureKernel
  infer_instance

/-- Pointwise kernel binding to the SAME actual physical experiment. -/
theorem futureKernel_actual (n : ℕ) (memory : ObservedPrefix Z A W n → History A W)
    (hm : Measurable memory) (h : ObservedPrefix Z A W n) :
    futureKernel P O ρ n memory hm h =
      MeasurablePredictiveAdaptiveCanonical.actualAdaptiveLaw P O ρ (terminalPosterior n h) (memory h) := by
  rw [← physicalPathKernel_comp_lift P O ρ (terminalPosterior n h,memory h)]
  apply (Measure.ext_iff_lintegral _).mpr
  intro F hF
  rw [futureKernel,Kernel.lintegral_comp _ _ h hF,Kernel.id,
    Kernel.lintegral_deterministic_prod measurable_id _ h hF.lintegral_kernel,
    Measure.lintegral_bind (physicalPathKernel P O ρ).aemeasurable hF.aemeasurable,
    lintegral_historyLatentLift _ _ hF.lintegral_kernel]
  rfl

/-- Genuine joint experiment: run the arbitrary past controller, retain its
terminal latent, then execute the registered future controller from THAT latent. -/
def actualPastFutureJoint (r : BeliefHistory Z A W) (n : ℕ)
    (memory : ObservedPrefix Z A W n → History A W) (hm : Measurable memory) :
    Measure (ObservedPrefix Z A W n × (ℕ → History A W)) :=
  (Kernel.deterministic Prod.fst measurable_fst ×ₖ futureFromRetained P O ρ n memory hm) ∘ₘ
    (((homTrajMeasure (historyLatentLift r) (physicalHistoryKernel P O π)).map
      (Preorder.frestrictLe n)).map (summarizePrefix n))

omit [StandardBorelSpace W] in
/-- Full source-derived past/future conditional law, including the entire real
past and all future observations. There is no supplied conditional-future field. -/
theorem actual_past_future_factorization (r : BeliefHistory Z A W) (n : ℕ)
    (memory : ObservedPrefix Z A W n → History A W) (hm : Measurable memory) :
    actualPastFutureJoint P O π ρ r n memory hm =
      observedPrefixLaw P O π r n ⊗ₘ futureKernel P O ρ n memory hm := by
  rw [actualPastFutureJoint,actual_prefix_latent_consistency]
  apply (Measure.ext_iff_lintegral _).mpr
  intro F hF
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable,
    Measure.lintegral_compProd hF.lintegral_kernel,Measure.lintegral_compProd hF]
  apply lintegral_congr
  intro h
  simp_rw [Kernel.lintegral_deterministic_prod measurable_fst _ _ hF]
  have hf : Measurable (fun z : ℕ → History A W => F (h,z)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [futureKernel,Kernel.lintegral_comp _ _ h (g:=fun z => F (h,z)) hf,Kernel.id,
    Kernel.lintegral_deterministic_prod measurable_id _ h hf.lintegral_kernel]
  rfl

instance actualPastFutureJoint_isProbability (r : BeliefHistory Z A W) (n : ℕ)
    (memory : ObservedPrefix Z A W n → History A W) (hm : Measurable memory) :
    IsProbabilityMeasure (actualPastFutureJoint P O π ρ r n memory hm) := by
  rw [actual_past_future_factorization]
  infer_instance

omit [StandardBorelSpace W] in
theorem actual_past_marginal (r : BeliefHistory Z A W) (n : ℕ)
    (memory : ObservedPrefix Z A W n → History A W) (hm : Measurable memory) :
    (actualPastFutureJoint P O π ρ r n memory hm).fst = observedPrefixLaw P O π r n := by
  rw [actual_past_future_factorization,Measure.fst_compProd]

/-- Existing actual source word kernel after this arbitrary history-program past. -/
def wordFutureKernel (n : ℕ) (u : List A) : Kernel (ObservedPrefix Z A W n) (ObservationWord W u) :=
  wordKernel P O u ∘ₖ terminalBelief n

instance wordFutureKernel_isMarkov (n : ℕ) (u : List A) : IsMarkovKernel (wordFutureKernel P O n u) := by
  unfold wordFutureKernel
  infer_instance

/-- Same retained-latent past, then the actual original word execution. -/
def actualPastWordJoint (r : BeliefHistory Z A W) (n : ℕ) (u : List A) :
    Measure (ObservedPrefix Z A W n × ObservationWord W u) :=
  (Kernel.id ∥ₖ wordKernel P O u) ∘ₘ
    (((homTrajMeasure (historyLatentLift r) (physicalHistoryKernel P O π)).map
      (Preorder.frestrictLe n)).map (summarizePrefix n))

omit [StandardBorelSpace W] in
/-- Actual source conditional word law on the unrestricted history-program past. -/
theorem actual_past_word_factorization (r : BeliefHistory Z A W) (n : ℕ) (u : List A) :
    actualPastWordJoint P O π r n u = observedPrefixLaw P O π r n ⊗ₘ wordFutureKernel P O n u := by
  rw [actualPastWordJoint,actual_prefix_latent_consistency,Measure.parallelComp_comp_compProd]
  rfl

/-- Canonical state of this actual past: the complete response of its computed posterior. -/
def actualCanonical (n : ℕ) (h : ObservedPrefix Z A W n) : ResponseState A W :=
  response P O (terminalPosterior n h)

def actualRawCanonical (n : ℕ) (h : ObservedPrefix Z A W n) : MeasurablePredictiveCanonicalSource.RawResponse A W :=
  fun u => wordFutureKernel P O n u h

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] [StandardBorelSpace W] in
@[fun_prop] theorem measurable_actualCanonical (n : ℕ) : Measurable (actualCanonical P O n) :=
  (measurable_response P O).comp (measurable_terminalPosterior n)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] [StandardBorelSpace W] in
@[fun_prop] theorem measurable_actualRawCanonical (n : ℕ) : Measurable (actualRawCanonical P O n) :=
  UEOT.V3.PredictionDependent.canonical_measurable (wordFutureKernel P O n)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] [StandardBorelSpace W] in
theorem actualRawCanonical_eq_response (n : ℕ) (h : ObservedPrefix Z A W n) :
    actualRawCanonical P O n h = MeasurablePredictiveCanonicalSource.rawResponse (actualCanonical P O n h) := rfl

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] [StandardBorelSpace W] in
/-- The original dependent canonical sufficiency endpoint now consumes the
actual word kernels derived from an arbitrary observable-history past. -/
theorem actual_raw_kernel_sufficient (n : ℕ) (u : List A) :
    ∃ L : Kernel (MeasurablePredictiveCanonicalSource.RawResponse A W) (ObservationWord W u),
      ∀ h, wordFutureKernel P O n u h = L (actualRawCanonical P O n h) :=
  UEOT.V3.PredictionDependent.canonical_kernel_sufficient (wordFutureKernel P O n) u

/-- Empty fresh future control memory is a separately registered permission. -/
def freshFutureKernel (n : ℕ) (c : FreshController A W) : Kernel (ObservedPrefix Z A W n) (ℕ → History A W) :=
  letI : IsMarkovKernel c.1 := c.2
  futureKernel P O c.1 n (fun _ => []) measurable_const

instance freshFutureKernel_isMarkov (n : ℕ) (c : FreshController A W) :
    IsMarkovKernel (freshFutureKernel P O n c) := by
  let : IsMarkovKernel c.1 := c.2
  unfold freshFutureKernel
  infer_instance

theorem freshFutureKernel_actual (n : ℕ) (c : FreshController A W) (h : ObservedPrefix Z A W n) :
    freshFutureKernel P O n c h = MeasurablePredictiveWordController.freshLaw P O c (terminalPosterior n h) := by
  let : IsMarkovKernel c.1 := c.2
  exact futureKernel_actual P O c.1 n (fun _ => []) measurable_const h

variable [Countable A]

omit [StandardBorelSpace W] in
/-- Original countable-word minimality, now with the actual full-history past law. -/
theorem actual_raw_ae_minimal
    (r : BeliefHistory Z A W) (n : ℕ) {S : Type*} [MeasurableSpace S]
    (s : ObservedPrefix Z A W n → S)
    (L : (u : List A) → Kernel S (ObservationWord W u))
    (hL : ∀ u, ∀ᵐ h ∂observedPrefixLaw P O π r n, wordFutureKernel P O n u h = L u (s h)) :
    UEOT.V3.PredictionAE.AEFactors (observedPrefixLaw P O π r n) (actualRawCanonical P O n) s :=
  UEOT.V3.PredictionDependent.canonical_ae_minimal (observedPrefixLaw P O π r n) (wordFutureKernel P O n) s L hL

/-- The hypothesis predicts every actual fresh adaptive continuation kernel.
Physically implemented word controllers restrict it to original word predictions. -/
theorem actual_response_adaptive_ae_minimal
    (defaultAction : A) (defaultObservation : W) (r : BeliefHistory Z A W) (n : ℕ)
    {S : Type*} [MeasurableSpace S] (s : ObservedPrefix Z A W n → S)
    (L : FreshController A W → {κ : Kernel S (ℕ → History A W) // IsMarkovKernel κ})
    (hL : ∀ c, ∀ᵐ h ∂observedPrefixLaw P O π r n, freshFutureKernel P O n c h = (L c).1 (s h)) :
    UEOT.V3.PredictionAE.AEFactors (observedPrefixLaw P O π r n) (actualCanonical P O n) s := by
  have hword (u : List A) : ∀ᵐ h ∂observedPrefixLaw P O π r n,
      wordFutureKernel P O n u h =
        (((L (wordAsController defaultAction u)).1).map (observationProjection u defaultObservation)) (s h) := by
    filter_upwards [hL (wordAsController defaultAction u)] with h hh
    have he := congrArg (fun μ : Measure (ℕ → History A W) => μ.map (observationProjection u defaultObservation)) hh
    rw [freshFutureKernel_actual] at he
    change (MeasurablePredictiveAdaptiveCanonical.actualAdaptiveLaw P O (controller u defaultAction)
      (terminalPosterior n h) []).map (observationProjection u defaultObservation) = _ at he
    rw [actual_controller_word_law] at he
    rw [Kernel.map_apply _ (measurable_observationProjection u defaultObservation)]
    exact he
  obtain ⟨d,hd,hEq⟩ := actual_raw_ae_minimal P O π r n s
    (fun u => ((L (wordAsController defaultAction u)).1).map (observationProjection u defaultObservation)) hword
  obtain ⟨decode,hdecode,hleft⟩ := (MeasurablePredictiveCanonicalSource.rawResponse_embedding (A:=A) (W:=W)).exists_measurable_extend
    measurable_id (fun _ => ⟨response P O r.1⟩)
  refine ⟨decode ∘ d,hdecode.comp hd,?_⟩
  filter_upwards [hEq] with h hh
  rw [actualRawCanonical_eq_response] at hh
  exact (congr_fun hleft (actualCanonical P O n h)).symm.trans (congrArg decode hh)

theorem actual_response_adaptive_ae_sigma_minimal
    (defaultAction : A) (defaultObservation : W) (r : BeliefHistory Z A W) (n : ℕ)
    {S : Type*} [MeasurableSpace S] (s : ObservedPrefix Z A W n → S)
    (L : FreshController A W → {κ : Kernel S (ℕ → History A W) // IsMarkovKernel κ})
    (hL : ∀ c, ∀ᵐ h ∂observedPrefixLaw P O π r n, freshFutureKernel P O n c h = (L c).1 (s h)) :
    UEOT.V3.PredictionAE.AESigmaLE (observedPrefixLaw P O π r n) (actualCanonical P O n) s :=
  UEOT.V3.PredictionAE.aeFactors_sigmaLE _
    (actual_response_adaptive_ae_minimal P O π defaultAction defaultObservation r n s L hL)

variable [MeasurableSingletonClass A]

/-- Explicit measurable predictor on response PLUS the independently registered
controller memory. No inverse to a realizable-response image is used. -/
def memoryPredictor : Kernel (ResponseHistory A W) (ℕ → History A W) :=
  (pathKernel (responseHistoryKernel P O ρ)).map (mapPath Prod.snd)

instance memoryPredictor_isMarkov : IsMarkovKernel (memoryPredictor P O ρ) := by
  unfold memoryPredictor
  exact Kernel.IsMarkovKernel.map _ (measurable_mapPath Prod.snd measurable_snd)

omit [StandardBorelSpace Z] in
private theorem memoryPredictor_apply (c : ResponseState A W) (h0 : History A W) :
    memoryPredictor P O ρ (c,h0) = MeasurablePredictiveAdaptiveCanonical.adaptiveFutureKernel P O ρ h0 c := by
  rw [memoryPredictor,Kernel.map_apply _ (measurable_mapPath Prod.snd measurable_snd),
    MeasurablePredictiveAdaptiveCanonical.adaptiveFutureKernel,
    Kernel.map_apply _ (measurable_mapPath Prod.snd measurable_snd)]
  rfl

/-- Actual conditional future law factors through (response, registered memory).
A history-dependent memory is kept in that state; it is never erased silently. -/
theorem futureKernel_response_memory_factor (n : ℕ)
    (memory : ObservedPrefix Z A W n → History A W) (hm : Measurable memory) (h : ObservedPrefix Z A W n) :
    futureKernel P O ρ n memory hm h = memoryPredictor P O ρ (actualCanonical P O n h,memory h) := by
  rw [futureKernel_actual,MeasurablePredictiveAdaptiveCanonical.actual_adaptive_factorization]
  exact (memoryPredictor_apply P O ρ (actualCanonical P O n h) (memory h)).symm

/-- In particular every actual fresh adaptive continuation admits a measurable
Markov predictor from the original canonical response alone, after this true
arbitrary full-history past. Fresh memory is explicitly empty on both sides. -/
theorem actual_adaptive_kernel_sufficient (n : ℕ) (c : FreshController A W) :
    ∃ L : Kernel (ResponseState A W) (ℕ → History A W), IsMarkovKernel L ∧
      ∀ h, freshFutureKernel P O n c h = L (actualCanonical P O n h) := by
  let : IsMarkovKernel c.1 := c.2
  refine ⟨MeasurablePredictiveAdaptiveCanonical.adaptiveFutureKernel P O c.1 [],inferInstance,?_⟩
  intro h
  rw [freshFutureKernel_actual]
  exact MeasurablePredictiveAdaptiveCanonical.actual_adaptive_factorization P O c.1 (terminalPosterior n h) []

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveHistoryCanonical
