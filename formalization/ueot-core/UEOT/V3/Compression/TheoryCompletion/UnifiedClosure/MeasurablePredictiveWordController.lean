import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveAdaptiveCanonical

/-!
Original commitment: every finite open-loop test is an actual fresh history-controller experiment.
Existing result: actual retained-latent history paths and response dynamics agree for the same controller.
Premise reduced: recover the original source word law by projecting an executed deterministic word controller.
Model: empty initial control memory; explicit permitted default action after the registered finite word.
Consumer: adaptive-only predictive minimality must use this physical source bridge, not a mixed protocol catalogue.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveWordController
open MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel UEOT.V3.GeneralBayesPosterior
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open MeasurablePredictiveResponseRecursion MeasurablePredictiveHistoryControl
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Z A W : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace W]
local instance : MeasurableSpace (History A W) := historySpace A W

variable [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W]
variable (P : Kernel (Z × A) Z) [IsMarkovKernel P]
variable (O : Kernel (Z × A) W) [IsMarkovKernel O]

/-- Execute the registered word's actual posterior updates and literal event appends. -/
def consumeWord : (u : List A) → BeliefHistory Z A W → ObservationWord W u → BeliefHistory Z A W
  | [],r,_ => r
  | a::u,r,ws => consumeWord u (nextBelief P O (r,(a,ws.1))) ws.2

@[fun_prop] theorem measurable_consumeWord (u : List A) :
    Measurable (fun q : BeliefHistory Z A W × ObservationWord W u => consumeWord P O u q.1 q.2) := by
  induction u with
  | nil => exact measurable_fst
  | cons a u ih =>
    change Measurable (fun q : BeliefHistory Z A W × (W × ObservationWord W u) =>
      consumeWord P O u (nextBelief P O (q.1,(a,q.2.1))) q.2.2)
    exact ih.comp (((measurable_nextBelief P O).comp (by fun_prop)).prodMk (by fun_prop))

omit [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Z]
  [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
/-- Append the last actual observation, preserving the original TProd order. -/
def snocWord (a : A) : (u : List A) → ObservationWord W u → W → ObservationWord W (u++[a])
  | [],_,w => (w,PUnit.unit)
  | _::u,ws,w => (ws.1,snocWord a u ws.2 w)

omit [MeasurableSpace A] [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
@[fun_prop] theorem measurable_snocWord (u : List A) (a : A) :
    Measurable (fun q : ObservationWord W u × W => snocWord a u q.1 q.2) := by
  induction u with
  | nil => exact measurable_snd.prodMk measurable_const
  | cons b u ih => exact measurable_fst.fst.prodMk (ih.comp (measurable_fst.snd.prodMk measurable_snd))

@[simp] theorem consumeWord_snoc (u : List A) (r : BeliefHistory Z A W)
    (ws : ObservationWord W u) (a : A) (w : W) :
    consumeWord P O (u++[a]) r (snocWord a u ws w) =
      nextBelief P O (consumeWord P O u r ws,(a,w)) := by
  induction u generalizing r with
  | nil => rfl
  | cons b u ih => exact ih _ ws.2

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
private theorem responseLaw_nil (b : ProbabilityMeasure Z) :
    responseLaw P O b [] = Measure.dirac PUnit.unit := by
  ext E hE
  rw [responseLaw,wordKernel,Measure.bind_apply hE (Kernel.aemeasurable _)]
  simp only [Kernel.const_apply,lintegral_const,measure_univ, mul_one]

private theorem lintegral_response_cons (b : ProbabilityMeasure Z) (a : A) (u : List A)
    (F : ObservationWord W (a::u) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ws, F ws ∂responseLaw P O b (a::u)) =
      ∫⁻ w, ∫⁻ ys, F (w,ys)
        ∂responseLaw P O (c1ParametricPosteriorBelief P O ((b,a),w)) u
        ∂observationLaw b.toMeasure P O a := by
  have : IsProbabilityMeasure (observationLaw b.toMeasure P O a) := by unfold observationLaw; infer_instance
  change (∫⁻ ws : W × ObservationWord W u, F ws ∂responseLaw P O b (a::u)) = _
  rw [← actual_word_factorization,Measure.lintegral_compProd hF]
  rfl

/-- Predict the next observation after literally consuming this SAME word. -/
def finalObservationKernel (u : List A) (r : BeliefHistory Z A W) (a : A) :
    Kernel (ObservationWord W u) W :=
  (c1BeliefObservationKernel P O).comap
    (fun ws => ((consumeWord P O u r ws).1,a))
    (((measurable_fst.comp ((measurable_consumeWord P O u).comp
      (measurable_const.prodMk measurable_id)))).prodMk measurable_const)

instance finalObservationKernel_isMarkov (u : List A) (r : BeliefHistory Z A W) (a : A) :
    IsMarkovKernel (finalObservationKernel P O u r a) := by unfold finalObservationKernel; infer_instance

private theorem lintegral_response_snoc (u : List A) (r : BeliefHistory Z A W) (a : A)
    (F : ObservationWord W (u++[a]) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ws, ∫⁻ w, F (snocWord a u ws w) ∂finalObservationKernel P O u r a ws
      ∂responseLaw P O r.1 u) = ∫⁻ ws, F ws ∂responseLaw P O r.1 (u++[a]) := by
  induction u generalizing r with
  | nil =>
    have hn : (∫⁻ ws : ObservationWord W [], ∫⁻ w, F (w,PUnit.unit)
        ∂finalObservationKernel P O [] r a ws ∂responseLaw P O r.1 []) =
        ∫⁻ w, F (w,PUnit.unit) ∂observationLaw r.1.toMeasure P O a := by
      rw [responseLaw_nil]
      calc
        _ = ∫⁻ w, F (w,PUnit.unit) ∂finalObservationKernel P O [] r a PUnit.unit :=
          lintegral_dirac' (f:=fun ws : ObservationWord W [] => ∫⁻ w, F (w,PUnit.unit)
            ∂finalObservationKernel P O [] r a ws) PUnit.unit (measurable_of_countable _)
        _ = _ := by
          rw [show finalObservationKernel P O [] r a PUnit.unit = observationLaw r.1.toMeasure P O a from
            c1BeliefActionJoint_fst_eq_observationLaw P O r.1 a]
    change (∫⁻ ws : ObservationWord W [], ∫⁻ w, F (w,PUnit.unit)
      ∂finalObservationKernel P O [] r a ws ∂responseLaw P O r.1 []) = _
    rw [hn]
    calc
      _ = ∫⁻ w, ∫⁻ ys, F (w,ys) ∂responseLaw P O
          (c1ParametricPosteriorBelief P O ((r.1,a),w)) [] ∂observationLaw r.1.toMeasure P O a := by
        apply lintegral_congr
        intro w
        rw [responseLaw_nil]
        exact (lintegral_dirac' (f:=fun ys : ObservationWord W [] => F (w,ys))
          PUnit.unit (hF.comp (measurable_const.prodMk measurable_id))).symm
      _ = _ := (lintegral_response_cons P O r.1 a [] F hF).symm
  | cons b u ih =>
    have hG : Measurable (fun ws : ObservationWord W (b::u) =>
        ∫⁻ w, F (snocWord a (b::u) ws w) ∂finalObservationKernel P O (b::u) r a ws) := by
      apply Measurable.lintegral_kernel_prod_right
      exact hF.comp (measurable_snocWord (b::u) a)
    change _ = ∫⁻ ws : ObservationWord W (b::(u++[a])), F ws ∂responseLaw P O r.1 (b::(u++[a]))
    rw [lintegral_response_cons P O r.1 b u _ hG,
      lintegral_response_cons P O r.1 b (u++[a]) F hF]
    apply lintegral_congr
    intro w
    exact ih (nextBelief P O (r,(b,w))) (fun ys => F (w,ys)) (hF.comp (measurable_const.prodMk measurable_id))

/-- The longer SAME-source response is obtained by appending one observation
from the terminal posterior computed while consuming its actual prefix. -/
theorem actual_word_snoc_factorization (u : List A) (r : BeliefHistory Z A W) (a : A) :
    (responseLaw P O r.1 u ⊗ₘ finalObservationKernel P O u r a).map
      (fun q => snocWord a u q.1 q.2) = responseLaw P O r.1 (u++[a]) := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro F hF
  rw [lintegral_map hF (measurable_snocWord u a),
    Measure.lintegral_compProd (f:=fun q : ObservationWord W u × W => F (snocWord a u q.1 q.2))
      (hF.comp (measurable_snocWord u a))]
  exact lintegral_response_snoc P O u r a F hF

private theorem consumeWord_length (u : List A) (r : BeliefHistory Z A W) (ws : ObservationWord W u) :
    (consumeWord P O u r ws).2.length = r.2.length + u.length := by
  induction u generalizing r with
  | nil => simp [consumeWord]
  | cons a u ih =>
    change (consumeWord P O u (nextBelief P O (r,(a,ws.1))) ws.2).2.length = _
    rw [ih]
    simp only [nextBelief,List.length_append,List.length_cons,List.length_nil]
    omega

/-- A literal fresh full-history controller: prescribed actions for the word,
then the explicit permitted default action forever. Clock is h.length. -/
def controller (u : List A) (defaultAction : A) : HistoryPolicy A W :=
  Kernel.deterministic (fun h => u.getD h.length defaultAction)
    ((measurable_of_countable (fun n : ℕ => u.getD n defaultAction)).comp measurable_historyLength)

instance controller_isMarkov (u : List A) (defaultAction : A) :
    IsMarkovKernel (controller (W:=W) u defaultAction) := by unfold controller; infer_instance

private theorem lintegral_controller_step (v : List A) (defaultAction : A)
    (r : BeliefHistory Z A W) (F : BeliefHistory Z A W → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, F s ∂beliefHistoryKernel P O (controller v defaultAction) r) =
      ∫⁻ w, F (nextBelief P O (r,(v.getD r.2.length defaultAction,w)))
        ∂c1BeliefObservationKernel P O (r.1,v.getD r.2.length defaultAction) := by
  rw [beliefHistoryKernel,Kernel.lintegral_snd _ _ hF,Kernel.lintegral_compProd]
  simp_rw [Kernel.lintegral_deterministic' (measurable_nextBelief P O) hF]
  rw [sampledBelief,Kernel.lintegral_compProd]
  · simp only [controller,Kernel.comap_apply,Kernel.deterministic_apply]
    have hm : Measurable (fun a : A => ∫⁻ w, F (nextBelief P O (r,(a,w)))
        ∂c1BeliefObservationKernel P O (r.1,a)) := by
      change Measurable (fun a => ∫⁻ w, F (nextBelief P O (r,(a,w)))
        ∂((c1BeliefObservationKernel P O).comap (fun a : A => (r.1,a))
          (measurable_const.prodMk measurable_id)) a)
      exact Measurable.lintegral_kernel_prod_right (hF.comp ((measurable_nextBelief P O).comp (by fun_prop)))
    exact lintegral_dirac' _ hm
  all_goals fun_prop

private theorem source_state_successor (v u : List A) (defaultAction : A) (b : ProbabilityMeasure Z) :
    beliefHistoryKernel P O (controller v defaultAction) ∘ₘ
      (responseLaw P O b u).map (consumeWord P O u (b,([] : History A W))) =
      (responseLaw P O b (u++[v.getD u.length defaultAction])).map
        (consumeWord P O (u++[v.getD u.length defaultAction]) (b,([] : History A W))) := by
  let a := v.getD u.length defaultAction
  let r : BeliefHistory Z A W := (b,[])
  have hc (w : List A) : Measurable (consumeWord P O w r) :=
    (measurable_consumeWord P O w).comp (measurable_const.prodMk measurable_id)
  apply (Measure.ext_iff_lintegral _).mpr
  intro F hF
  rw [Measure.lintegral_bind (beliefHistoryKernel P O (controller v defaultAction)).aemeasurable hF.aemeasurable,
    lintegral_map hF.lintegral_kernel (hc u)]
  simp_rw [lintegral_controller_step P O v defaultAction _ F hF,consumeWord_length]
  simp only [show r.2.length = 0 from rfl,zero_add]
  rw [lintegral_map hF (hc (u++[a])),
    ← lintegral_response_snoc P O u r a (fun ws => F (consumeWord P O (u++[a]) r ws))
      (hF.comp (hc (u++[a])))]
  simp_rw [consumeWord_snoc]
  rfl

/-- Actual time-n marginal of the SAME literal controller, before the registered
word ends. The posterior and full history come from the executed observations. -/
theorem actual_belief_prefix_law (v : List A) (defaultAction : A) (b : ProbabilityMeasure Z)
    (n : ℕ) (hn : n ≤ v.length) :
    (homTrajMeasure (Measure.dirac (b,([] : History A W)))
      (beliefHistoryKernel P O (controller v defaultAction))).map (fun z => z n) =
      (responseLaw P O b (v.take n)).map (consumeWord P O (v.take n) (b,([] : History A W))) := by
  induction n with
  | zero =>
    rw [UEOT.V3.Compression.Objecthood.homTrajMeasure_time_zero_general,List.take_zero,responseLaw_nil]
    change Measure.dirac (b,([] : History A W)) = (Measure.dirac PUnit.unit).map
      (fun _ : PUnit => (b,([] : History A W)))
    exact (Measure.map_dirac' measurable_const PUnit.unit).symm
  | succ n ih =>
    have hlt : n < v.length := by omega
    rw [UEOT.V3.Compression.Objecthood.homTrajMeasure_time_succ_general,ih (by omega),
      List.take_succ_eq_append_getElem hlt]
    have ha : v.getD (v.take n).length defaultAction = v[n] := by
      rw [List.length_take,Nat.min_eq_left (by omega),List.getD_eq_getElem v defaultAction hlt]
    exact (source_state_successor P O v (v.take n) defaultAction b).trans
      (congrArg (fun w : List A => (responseLaw P O b w).map (consumeWord P O w (b,([] : History A W))))
        (congrArg (fun a => v.take n ++ [a]) ha))

/-- The real retained-latent execution, projected at the word horizon, has this
same source-derived final posterior/history law. No latent is restarted. -/
theorem actual_physical_word_state (u : List A) (defaultAction : A) (b : ProbabilityMeasure Z) :
    (homTrajMeasure (historyLatentLift (b,([] : History A W)))
      (physicalHistoryKernel P O (controller u defaultAction))).map (fun z => (z u.length).1) =
      (responseLaw P O b u).map (consumeWord P O u (b,([] : History A W))) := by
  have h := congrArg (fun μ : Measure (ℕ → BeliefHistory Z A W) => μ.map (fun z => z u.length))
    (actual_belief_history_path P O (controller u defaultAction) (b,([] : History A W)))
  rw [Measure.map_map (measurable_pi_apply u.length) (measurable_mapPath Prod.fst measurable_fst)] at h
  change (homTrajMeasure (historyLatentLift (b,([] : History A W)))
    (physicalHistoryKernel P O (controller u defaultAction))).map (fun z => (z u.length).1) = _ at h
  rw [h]
  exact (actual_belief_prefix_law P O u defaultAction b u.length le_rfl).trans
    (congrArg (fun w : List A => (responseLaw P O b w).map (consumeWord P O w (b,([] : History A W))))
      (List.take_length (l:=u)))

omit [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace Z]
  [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
private def events : (u : List A) → ObservationWord W u → History A W
  | [],_ => []
  | a::u,ws => (a,ws.1)::events u ws.2

private theorem consumeWord_history (u : List A) (r : BeliefHistory Z A W) (ws : ObservationWord W u) :
    (consumeWord P O u r ws).2 = r.2 ++ events u ws := by
  induction u generalizing r with
  | nil => simp [consumeWord,events]
  | cons a u ih =>
    change (consumeWord P O u (nextBelief P O (r,(a,ws.1))) ws.2).2 = _
    rw [ih]
    simp [nextBelief,events,List.append_assoc]

/-- Total observation read: the default affects only missing coordinates. -/
def readObservation (defaultObservation : W) (h : History A W) (k : ℕ) : W :=
  Sum.elim (fun _ => defaultObservation) Prod.snd ((historyCode h).2 k)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
@[fun_prop] theorem measurable_readObservation (defaultObservation : W) (k : ℕ) :
    Measurable (fun h : History A W => readObservation defaultObservation h k) :=
  (measurable_const.sumElim measurable_snd).comp
    ((measurable_pi_apply k).comp (measurable_snd.comp measurable_historyCode))

/-- Ordered word-observation projection from the actual complete history. -/
def readWord (defaultObservation : W) : (u : List A) → ℕ → History A W → ObservationWord W u
  | [],_,_ => PUnit.unit
  | _::u,k,h => (readObservation defaultObservation h k,readWord defaultObservation u (k+1) h)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
@[fun_prop] theorem measurable_readWord (defaultObservation : W) (u : List A) (k : ℕ) :
    Measurable (readWord (A:=A) defaultObservation u k) := by
  induction u generalizing k with
  | nil => exact measurable_const
  | cons a u ih => exact (measurable_readObservation defaultObservation k).prodMk (ih (k+1))

omit [MeasurableSpace A] [MeasurableSpace W] [MeasurableSpace.CountablyGenerated W] in
private theorem readWord_events (defaultObservation : W) (u : List A) (h : History A W)
    (ws : ObservationWord W u) :
    readWord defaultObservation u h.length (h ++ events u ws) = ws := by
  induction u generalizing h with
  | nil => cases ws; rfl
  | cons a u ih =>
    apply Prod.ext
    · simp [readWord,readObservation,historyCode,events,List.getElem?_append]
    · simpa only [List.length_append,List.length_cons,List.length_nil,List.append_assoc,
        List.singleton_append,events,readWord] using ih (h++[(a,ws.1)]) ws.2

private theorem readWord_consumeWord (defaultObservation : W) (u : List A)
    (b : ProbabilityMeasure Z) (ws : ObservationWord W u) :
    readWord defaultObservation u 0 (consumeWord P O u (b,([] : History A W)) ws).2 = ws := by
  rw [consumeWord_history]
  exact readWord_events defaultObservation u [] ws

/-- A concrete measurable projection of the actual history path at |u|. -/
def observationProjection (u : List A) (defaultObservation : W) (h : ℕ → History A W) :
    ObservationWord W u := readWord defaultObservation u 0 (h u.length)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
@[fun_prop] theorem measurable_observationProjection (u : List A) (defaultObservation : W) :
    Measurable (observationProjection (A:=A) u defaultObservation) :=
  (measurable_readWord defaultObservation u 0).comp (measurable_pi_apply u.length)

variable [StandardBorelSpace W]

/-- Exact physical source bridge: projecting the real fresh history-controller
experiment recovers the original wordKernel response, with all observations retained. -/
theorem actual_controller_word_law (u : List A) (defaultAction : A) (defaultObservation : W)
    (b : ProbabilityMeasure Z) :
    (MeasurablePredictiveAdaptiveCanonical.actualAdaptiveLaw P O (controller u defaultAction) b []).map
      (observationProjection u defaultObservation) = responseLaw P O b u := by
  have h := congrArg (fun μ : Measure (BeliefHistory Z A W) =>
      μ.map (fun r => readWord defaultObservation u 0 r.2))
    (actual_physical_word_state P O u defaultAction b)
  have hf : Measurable (fun r : BeliefHistory Z A W => readWord defaultObservation u 0 r.2) :=
    (measurable_readWord defaultObservation u 0).comp measurable_snd
  have hm : Measurable (fun z : ℕ → BeliefHistory Z A W × Z => (z u.length).1) :=
    (measurable_pi_apply u.length).fst
  have hc : Measurable (consumeWord P O u (b,([] : History A W))) :=
    (measurable_consumeWord P O u).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_map hf hm,Measure.map_map hf hc] at h
  change _ = (responseLaw P O b u).map (fun ws =>
    readWord defaultObservation u 0 (consumeWord P O u (b,([] : History A W)) ws).2) at h
  simp_rw [readWord_consumeWord] at h
  rw [Measure.map_id'] at h
  rw [MeasurablePredictiveAdaptiveCanonical.actualAdaptiveLaw,
    Measure.map_map (measurable_observationProjection u defaultObservation)
      (measurable_mapPath _ (by fun_prop))]
  exact h

/-- Programs in the actual history-controller class, without an externally
supplied open-loop branch or a desired response certificate. -/
abbrev FreshController (A W : Type*) [MeasurableSpace A] [MeasurableSpace W] :=
  {π : HistoryPolicy A W // IsMarkovKernel π}

/-- The registered word is an actual member of the SAME controller class. -/
def wordAsController (defaultAction : A) (u : List A) : FreshController A W :=
  ⟨controller u defaultAction,inferInstance⟩

/-- Actual fresh physical future, initialized with empty control memory. -/
def freshLaw (c : FreshController A W) (b : ProbabilityMeasure Z) : Measure (ℕ → History A W) :=
  letI : IsMarkovKernel c.1 := c.2
  MeasurablePredictiveAdaptiveCanonical.actualAdaptiveLaw P O c.1 b []

variable [Countable A]

/-- Relative minimality for predictors of ALL actual fresh adaptive controllers.
Only the countable family of physically implemented word controllers is used to
assemble a common null set; no uncountable common-a.e. claim is made. -/
theorem actual_response_adaptive_ae_minimal
    (defaultAction : A) (defaultObservation : W)
    (pastPolicy : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel pastPolicy]
    (r : MeasurablePredictiveJointPath.RecordState Z A W) (n : ℕ)
    {S : Type*} [MeasurableSpace S]
    (s : MeasurablePredictiveCanonicalSource.ObservedPrefix Z A W n → S) (hs : Measurable s)
    (L : FreshController A W → {κ : Kernel S (ℕ → History A W) // IsMarkovKernel κ})
    (hL : ∀ c, ∀ᵐ h ∂MeasurablePredictiveCanonicalSource.observedPrefixLaw P O pastPolicy r n,
      freshLaw P O c (MeasurablePredictiveCanonicalSource.terminalPosterior n h) = (L c).1 (s h)) :
    UEOT.V3.PredictionAE.AEFactors
      (MeasurablePredictiveCanonicalSource.observedPrefixLaw P O pastPolicy r n)
      (MeasurablePredictiveCanonicalSource.actualCanonical P O n) s := by
  apply MeasurablePredictiveCanonicalSource.actual_response_ae_minimal P O pastPolicy r n s hs
    (fun u => ((L (wordAsController defaultAction u)).1).map (observationProjection u defaultObservation))
  intro u
  filter_upwards [hL (wordAsController defaultAction u)] with h hh
  have he := congrArg (fun μ : Measure (ℕ → History A W) => μ.map (observationProjection u defaultObservation)) hh
  change (MeasurablePredictiveAdaptiveCanonical.actualAdaptiveLaw P O (controller u defaultAction)
    (MeasurablePredictiveCanonicalSource.terminalPosterior n h) []).map (observationProjection u defaultObservation) = _ at he
  rw [actual_controller_word_law] at he
  rw [Kernel.map_apply _ (measurable_observationProjection u defaultObservation)]
  exact he

/-- The original canonical sigma-information lower bound now applies to
statistics predicting every fresh adaptive experiment in that SAME source. -/
theorem actual_response_adaptive_ae_sigma_minimal
    (defaultAction : A) (defaultObservation : W)
    (pastPolicy : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel pastPolicy]
    (r : MeasurablePredictiveJointPath.RecordState Z A W) (n : ℕ)
    {S : Type*} [MeasurableSpace S]
    (s : MeasurablePredictiveCanonicalSource.ObservedPrefix Z A W n → S) (hs : Measurable s)
    (L : FreshController A W → {κ : Kernel S (ℕ → History A W) // IsMarkovKernel κ})
    (hL : ∀ c, ∀ᵐ h ∂MeasurablePredictiveCanonicalSource.observedPrefixLaw P O pastPolicy r n,
      freshLaw P O c (MeasurablePredictiveCanonicalSource.terminalPosterior n h) = (L c).1 (s h)) :
    UEOT.V3.PredictionAE.AESigmaLE
      (MeasurablePredictiveCanonicalSource.observedPrefixLaw P O pastPolicy r n)
      (MeasurablePredictiveCanonicalSource.actualCanonical P O n) s :=
  UEOT.V3.PredictionAE.aeFactors_sigmaLE _
    (actual_response_adaptive_ae_minimal P O defaultAction defaultObservation pastPolicy r n s hs L hL)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveWordController
