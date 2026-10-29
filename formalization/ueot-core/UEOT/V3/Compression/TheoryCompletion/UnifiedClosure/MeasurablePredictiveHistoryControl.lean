import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveCanonicalSource
import UEOT.V3.Compression.Objecthood.ExactPathLawDiscountedHittingTransform

/-!
Original commitment: canonical response dynamics support arbitrary measurable observed-history controllers.
Existing result: actual P/O disintegration and source-derived measurable ambient response update.
Premise reduced: derive seeded latent/filter and complete history path transport for the SAME controller.
Model: registered initial belief, Standard Borel observations/latent, countable measurable actions; policy reads ONLY List(action,observation).
Consumer: finite and countable actual action-observation path laws, with no latent resampling or policy replacement.

The finite-history sigma algebra records length and EVERY ordered event coordinate,
with a separate missing-coordinate symbol. It does not use a discrete sigma algebra
on uncountable observations. Future actions may depend on the whole recorded past;
no extra latent, belief or response oracle is exposed to the history controller.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveHistoryControl
open MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel UEOT.V3.GeneralBayesPosterior
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open MeasurablePredictiveResponseRecursion
open scoped ENNReal
attribute [local fun_prop] measurable_appendHistory
noncomputable section

abbrev History (A W : Type*) := List (A × W)

def historyCode {A W : Type*} (h : History A W) : ℕ × (ℕ → Unit ⊕ (A × W)) :=
  (h.length,fun k => match h[k]? with | none => Sum.inl () | some e => Sum.inr e)

/-- Natural full finite-history sigma algebra, without a global List instance. -/
abbrev historySpace (A W : Type*) [MeasurableSpace A] [MeasurableSpace W] :
    MeasurableSpace (History A W) := MeasurableSpace.comap historyCode inferInstance

local instance {A W : Type*} [MeasurableSpace A] [MeasurableSpace W] :
    MeasurableSpace (History A W) := historySpace A W

abbrev HistoryPolicy (A W : Type*) [MeasurableSpace A] [MeasurableSpace W] :=
  Kernel (History A W) A

variable {Z A W : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace W]

@[fun_prop] theorem measurable_historyCode : Measurable (historyCode (A:=A) (W:=W)) :=
  comap_measurable _

@[fun_prop] theorem measurable_historyLength : Measurable (List.length : History A W → ℕ) :=
  measurable_fst.comp measurable_historyCode

private def symbolAt (h : History A W) (k : ℕ) : Unit ⊕ (A × W) := (historyCode h).2 k

@[fun_prop] private theorem measurable_symbolAt (k : ℕ) : Measurable (fun h : History A W => symbolAt h k) :=
  (measurable_pi_apply k).comp (measurable_snd.comp measurable_historyCode)

omit [MeasurableSpace A] [MeasurableSpace W] in
private theorem symbolAt_append (h : History A W) (e : A × W) (k : ℕ) :
    symbolAt (h ++ [e]) k = if k < h.length then symbolAt h k else
      if k = h.length then Sum.inr e else Sum.inl () := by
  by_cases hk : k < h.length
  · simp [symbolAt,historyCode,List.getElem?_append,hk]
  · by_cases he : k = h.length
    · subst k; simp [symbolAt,historyCode,List.getElem?_append]
    · have hn : k-h.length ≠ 0 := by omega
      simp [symbolAt,historyCode,List.getElem?_append,hk,he,hn]

/-- Literal append is measurable for arbitrary measurable event alphabets. -/
@[fun_prop] theorem measurable_historyAppend :
    Measurable (fun p : History A W × (A × W) => p.1 ++ [p.2]) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun p : History A W × (A × W) => historyCode (p.1 ++ [p.2]))
  apply Measurable.prodMk
  · simpa only [historyCode,List.length_append,List.length_singleton,Function.comp_def] using
      (measurable_historyLength.comp measurable_fst).add_const 1
  · apply measurable_pi_lambda
    intro k
    change Measurable (fun p : History A W × (A × W) => symbolAt (p.1 ++ [p.2]) k)
    simp_rw [symbolAt_append]
    apply Measurable.ite (measurableSet_lt measurable_const (measurable_historyLength.comp measurable_fst))
    · exact (measurable_symbolAt k).comp measurable_fst
    · exact Measurable.ite
        (measurableSet_eq_fun measurable_const (measurable_historyLength.comp measurable_fst))
        (measurable_inr.comp measurable_snd) measurable_const

omit [MeasurableSpace A] [MeasurableSpace W] in
/-- The encoding loses no part of the literal observed history. -/
theorem historyCode_injective : Function.Injective (historyCode (A:=A) (W:=W)) := by
  intro h g heq
  have hl : h.length = g.length := congrArg Prod.fst heq
  apply List.ext_getElem hl
  intro k hk hg
  have he := congrFun (congrArg Prod.snd heq) k
  simpa [historyCode,List.getElem?_eq_getElem hk,List.getElem?_eq_getElem hg] using he

local instance symbolSingleton [MeasurableSingletonClass A] [MeasurableSingletonClass W] :
    MeasurableSingletonClass (Unit ⊕ (A × W)) where
  measurableSet_singleton s := by
    cases s with
    | inl u => simpa only [Set.image_singleton] using (MeasurableSet.singleton u).inl_image
    | inr e => simpa only [Set.image_singleton] using (MeasurableSet.singleton e).inr_image

local instance historySingleton [MeasurableSingletonClass A] [MeasurableSingletonClass W] :
    MeasurableSingletonClass (History A W) where
  measurableSet_singleton h := by
    have heq : ({h} : Set (History A W)) = historyCode ⁻¹' {historyCode h} := by
      ext g
      simp only [Set.mem_singleton_iff,Set.mem_preimage]
      exact historyCode_injective.eq_iff.symm
    rw [heq]
    exact measurable_historyCode (MeasurableSet.singleton _)


abbrev BeliefHistory (Z A W : Type*) [MeasurableSpace Z] := ProbabilityMeasure Z × History A W
abbrev ResponseHistory (A W : Type*) [MeasurableSpace W] := ResponseState A W × History A W

variable [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W]
variable (P : Kernel (Z × A) Z) [IsMarkovKernel P]
variable (O : Kernel (Z × A) W) [IsMarkovKernel O]
variable (π : HistoryPolicy A W) [IsMarkovKernel π]

/-- Filter update and literal append of the SAME sampled action/observation. -/
def nextBelief (q : BeliefHistory Z A W × (A × W)) : BeliefHistory Z A W :=
  (c1ParametricPosteriorBelief P O ((q.1.1,q.2.1),q.2.2),q.1.2 ++ [q.2])

@[fun_prop] theorem measurable_nextBelief : Measurable (nextBelief P O) := by
  unfold nextBelief
  exact ((measurable_c1ParametricPosteriorBelief P O).comp
    ((measurable_fst.fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)).prodMk
      (measurable_historyAppend.comp (measurable_fst.snd.prodMk measurable_snd))

def sampledBelief : Kernel (BeliefHistory Z A W) (A × W) :=
  π.comap Prod.snd measurable_snd ⊗ₖ
    (c1BeliefObservationKernel P O).comap (fun q => (q.1.1,q.2)) (by fun_prop)

instance sampledBelief_isMarkov : IsMarkovKernel (sampledBelief P O π) := by unfold sampledBelief; infer_instance

def beliefHistoryKernel : Kernel (BeliefHistory Z A W) (BeliefHistory Z A W) :=
  Kernel.snd (sampledBelief P O π ⊗ₖ Kernel.deterministic (nextBelief P O) (measurable_nextBelief P O))

instance beliefHistoryKernel_isMarkov : IsMarkovKernel (beliefHistoryKernel P O π) := by
  unfold beliefHistoryKernel
  infer_instance

/-- Initial consistency lift samples only the registered latent uncertainty. -/
def historyLatentLift : Kernel (BeliefHistory Z A W) (BeliefHistory Z A W × Z) :=
  Kernel.id ×ₖ MeasurablePredictiveLatentPath.beliefKernel.comap Prod.fst measurable_fst

instance historyLatentLift_isMarkov : IsMarkovKernel (historyLatentLift (Z:=Z) (A:=A) (W:=W)) := by
  unfold historyLatentLift
  infer_instance

def sampledPhysical : Kernel (BeliefHistory Z A W × Z) (A × (W × Z)) :=
  π.comap (fun q => q.1.2) (by fun_prop) ⊗ₖ
    (c1OneStepJoint P O).comap (fun q => (q.1.2,q.2)) (by fun_prop)

instance sampledPhysical_isMarkov : IsMarkovKernel (sampledPhysical P O π) := by unfold sampledPhysical; infer_instance

def nextPhysical (q : (BeliefHistory Z A W × Z) × (A × (W × Z))) : BeliefHistory Z A W × Z :=
  (nextBelief P O (q.1.1,(q.2.1,q.2.2.1)),q.2.2.2)

@[fun_prop] theorem measurable_nextPhysical : Measurable (nextPhysical P O) := by
  unfold nextPhysical
  exact ((measurable_nextBelief P O).comp (by fun_prop)).prodMk (by fun_prop)

/-- The actual latent is advanced by P/O and retained between steps. -/
def physicalHistoryKernel : Kernel (BeliefHistory Z A W × Z) (BeliefHistory Z A W × Z) :=
  Kernel.snd (sampledPhysical P O π ⊗ₖ Kernel.deterministic (nextPhysical P O) (measurable_nextPhysical P O))

instance physicalHistoryKernel_isMarkov : IsMarkovKernel (physicalHistoryKernel P O π) := by
  unfold physicalHistoryKernel
  infer_instance

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
private theorem lintegral_historyLatentLift (r : BeliefHistory Z A W)
    (F : BeliefHistory Z A W × Z → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q, F q ∂historyLatentLift r) = ∫⁻ x, F (r,x) ∂r.1.toMeasure := by
  rw [historyLatentLift,Kernel.id,Kernel.lintegral_deterministic_prod measurable_id _ _ hF]
  rfl

private theorem lintegral_physicalHistoryKernel (q : BeliefHistory Z A W × Z)
    (F : BeliefHistory Z A W × Z → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, F s ∂physicalHistoryKernel P O π q) =
      ∫⁻ a, ∫⁻ wz, F (nextBelief P O (q.1,(a,wz.1)),wz.2)
        ∂c1OneStepJoint P O (q.2,a) ∂π q.1.2 := by
  rw [physicalHistoryKernel,Kernel.lintegral_snd _ _ hF,Kernel.lintegral_compProd]
  simp_rw [Kernel.lintegral_deterministic' (measurable_nextPhysical P O) hF]
  rw [sampledPhysical,Kernel.lintegral_compProd]
  · rfl
  all_goals fun_prop

private theorem lintegral_beliefHistoryKernel (r : BeliefHistory Z A W)
    (F : BeliefHistory Z A W → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, F s ∂beliefHistoryKernel P O π r) =
      ∫⁻ a, ∫⁻ w, F (nextBelief P O (r,(a,w)))
        ∂c1BeliefObservationKernel P O (r.1,a) ∂π r.2 := by
  rw [beliefHistoryKernel,Kernel.lintegral_snd _ _ hF,Kernel.lintegral_compProd]
  simp_rw [Kernel.lintegral_deterministic' (measurable_nextBelief P O) hF]
  rw [sampledBelief,Kernel.lintegral_compProd]
  · rfl
  all_goals fun_prop

/-- Seeded consistency is derived for the literal observed-history controller;
no pointwise lumpability of arbitrary (belief,latent) pairs is assumed. -/
theorem actual_history_one_step_consistency (r : BeliefHistory Z A W) :
    physicalHistoryKernel P O π ∘ₘ historyLatentLift r =
      historyLatentLift ∘ₘ beliefHistoryKernel P O π r := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro F hF
  rw [Measure.lintegral_bind (physicalHistoryKernel P O π).aemeasurable hF.aemeasurable,
    lintegral_historyLatentLift r _ hF.lintegral_kernel,
    Measure.lintegral_bind historyLatentLift.aemeasurable hF.aemeasurable]
  simp_rw [lintegral_physicalHistoryKernel P O π _ F hF]
  rw [lintegral_beliefHistoryKernel P O π r _ hF.lintegral_kernel]
  simp_rw [lintegral_historyLatentLift _ F hF]
  have hm : Measurable (fun xa : Z × A =>
      ∫⁻ wz, F (nextBelief P O (r,(xa.2,wz.1)),wz.2)
        ∂c1OneStepJoint P O (xa.1,xa.2)) := by
    exact Measurable.lintegral_kernel_prod_right (by fun_prop)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro a
  have : IsProbabilityMeasure (observationLaw r.1.toMeasure P O a) := by unfold observationLaw; infer_instance
  rw [← MeasurablePredictiveLatentPath.lintegral_belief_joint P O r.1 a _ (by fun_prop),
    c1BeliefActionJoint_apply_eq_existing,← c1PosteriorSection_factorization,
    Measure.lintegral_compProd (by fun_prop)]
  rw [show c1BeliefObservationKernel P O (r.1,a) = observationLaw r.1.toMeasure P O a from
    c1BeliefActionJoint_fst_eq_observationLaw P O r.1 a]
  rfl

private def summarizeHistoryPrefix (n : ℕ)
    (h : (i : Finset.Iic n) → BeliefHistory Z A W × Z) :
    ((i : Finset.Iic n) → BeliefHistory Z A W) × Z :=
  (mapHistory Prod.fst n h,(h (lastHistoryIndex n)).2)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
@[fun_prop] private theorem measurable_summarizeHistoryPrefix (n : ℕ) :
    Measurable (summarizeHistoryPrefix (Z:=Z) (A:=A) (W:=W) n) := by
  unfold summarizeHistoryPrefix
  exact (measurable_mapHistory Prod.fst measurable_fst n).prodMk
    (measurable_snd.comp (measurable_pi_apply _))

private def terminalHistoryBelief (n : ℕ) : Kernel ((i : Finset.Iic n) → BeliefHistory Z A W) Z :=
  MeasurablePredictiveLatentPath.beliefKernel.comap (fun h => (h (lastHistoryIndex n)).1) (by fun_prop)

private instance terminalHistoryBelief_isMarkov (n : ℕ) :
    IsMarkovKernel (terminalHistoryBelief (Z:=Z) (A:=A) (W:=W) n) := by
  unfold terminalHistoryBelief
  infer_instance

private theorem appendHistory_last {S : Type*} [MeasurableSpace S] (n : ℕ)
    (h : (i : Finset.Iic n) → S) (s : S) :
    appendHistory n (h,s) (lastHistoryIndex (n+1)) = s := by
  simp [appendHistory,lastHistoryIndex,IicProdIoc_def,MeasurableEquiv.piSingleton]

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
private theorem summarize_history_append (n : ℕ)
    (h : (i : Finset.Iic n) → BeliefHistory Z A W × Z) (q : BeliefHistory Z A W × Z) :
    summarizeHistoryPrefix (n+1) (appendHistory n (h,q)) =
      (appendHistory n ((summarizeHistoryPrefix n h).1,q.1),q.2) := by
  rw [summarizeHistoryPrefix,mapHistory_appendHistory,appendHistory_last]
  rfl

/-- Every complete history-controller prefix has its actual retained latent
conditionally distributed as the SAME recursively computed posterior. -/
private theorem actual_history_prefix_consistency (r : BeliefHistory Z A W) (n : ℕ) :
    (((homTrajMeasure (historyLatentLift r) (physicalHistoryKernel P O π)).map
      (Preorder.frestrictLe n)).map (summarizeHistoryPrefix n)) =
      ((homTrajMeasure (Measure.dirac r) (beliefHistoryKernel P O π)).map
        (Preorder.frestrictLe n)) ⊗ₘ terminalHistoryBelief n := by
  induction n with
  | zero =>
    apply (Measure.ext_iff_lintegral _).mpr
    intro F hF
    rw [lintegral_map hF (measurable_summarizeHistoryPrefix 0),
      homTrajMeasure_prefix_zero, lintegral_map (f := fun h => F (summarizeHistoryPrefix 0 h)) (by fun_prop) (by fun_prop),
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
        (Preorder.frestrictLe (n+1))).map (summarizeHistoryPrefix (n+1))) =
        ∫⁻ hz, G hz ∂ν ⊗ₘ terminalHistoryBelief n := by
      rw [lintegral_map hF (measurable_summarizeHistoryPrefix (n+1)),
        ← homTrajMeasure_prefix_succ,
        lintegral_map (f := fun h => F (summarizeHistoryPrefix (n+1) h)) (by fun_prop) (measurable_appendHistory n),
        Measure.lintegral_compProd (by fun_prop)]
      change (∫⁻ h, ∫⁻ q, F (summarizeHistoryPrefix (n+1) (appendHistory n (h,q)))
        ∂K (h (lastHistoryIndex n)) ∂μ) = _
      simp_rw [summarize_history_append]
      change (∫⁻ h, G (summarizeHistoryPrefix n h) ∂μ) = _
      rw [← lintegral_map hG (measurable_summarizeHistoryPrefix n)]
      exact congrArg (fun ρ => ∫⁻ hz, G hz ∂ρ) ih
    rw [hleft, Measure.lintegral_compProd hG]
    have hJ : Measurable (fun h : (i : Finset.Iic (n+1)) → BeliefHistory Z A W =>
        ∫⁻ z, F (h,z) ∂terminalHistoryBelief (n+1) h) :=
      Measurable.lintegral_kernel_prod_right hF
    rw [Measure.lintegral_compProd hF, ← homTrajMeasure_prefix_succ,
      lintegral_map hJ (measurable_appendHistory n),
      Measure.lintegral_compProd (f := fun p =>
        ∫⁻ z, F (appendHistory n p,z) ∂terminalHistoryBelief (n+1) (appendHistory n p))
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
    simp only [terminalHistoryBelief, Kernel.comap_apply, MeasurablePredictiveLatentPath.beliefKernel, appendHistory_last]
    rfl


/-- Full recorded belief/history path law of the literal retained-latent run. -/
theorem actual_finite_belief_history_path (r : BeliefHistory Z A W) (n : ℕ) :
    (((homTrajMeasure (historyLatentLift r) (physicalHistoryKernel P O π)).map
      (Preorder.frestrictLe n)).map (mapHistory Prod.fst n)) =
      (homTrajMeasure (Measure.dirac r) (beliefHistoryKernel P O π)).map (Preorder.frestrictLe n) := by
  have h := congrArg (fun μ : Measure ((((i : Finset.Iic n) → BeliefHistory Z A W)) × Z) =>
    μ.map Prod.fst) (actual_history_prefix_consistency P O π r n)
  rw [Measure.map_map measurable_fst (measurable_summarizeHistoryPrefix n)] at h
  change _ = (((homTrajMeasure (Measure.dirac r) (beliefHistoryKernel P O π)).map
    (Preorder.frestrictLe n)) ⊗ₘ terminalHistoryBelief n).fst at h
  rw [Measure.fst_compProd] at h
  exact h

theorem actual_belief_history_path (r : BeliefHistory Z A W) :
    (homTrajMeasure (historyLatentLift r) (physicalHistoryKernel P O π)).map (mapPath Prod.fst) =
      homTrajMeasure (Measure.dirac r) (beliefHistoryKernel P O π) := by
  let : IsProbabilityMeasure ((homTrajMeasure (historyLatentLift r) (physicalHistoryKernel P O π)).map
      (mapPath Prod.fst)) :=
    Measure.isProbabilityMeasure_map (measurable_mapPath Prod.fst measurable_fst).aemeasurable
  apply pathMeasure_eq_of_prefix_eq
  intro n
  rw [Measure.map_map (Preorder.measurable_frestrictLe n)
      (measurable_mapPath Prod.fst measurable_fst),frestrictLe_mapPath Prod.fst n,
    ← Measure.map_map (measurable_mapHistory Prod.fst measurable_fst n)
      (Preorder.measurable_frestrictLe n)]
  exact actual_finite_belief_history_path P O π r n

variable [Countable A] [MeasurableSingletonClass A] [StandardBorelSpace W]

/-- Replace only the current belief by its actual complete response array;
the entire action-observation history is retained literally. -/
def projectResponse (r : BeliefHistory Z A W) : ResponseHistory A W :=
  (response P O r.1,r.2)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] [StandardBorelSpace W] [Countable A] [MeasurableSingletonClass A] in
@[fun_prop] theorem measurable_projectResponse : Measurable (projectResponse P O) :=
  ((measurable_response P O).comp measurable_fst).prodMk measurable_snd

def nextResponse (q : ResponseHistory A W × (A × W)) : ResponseHistory A W :=
  (ambientUpdate P O q.1.1 q.2.1 q.2.2,q.1.2 ++ [q.2])

omit [StandardBorelSpace Z] in
@[fun_prop] theorem measurable_nextResponse : Measurable (nextResponse P O) := by
  unfold nextResponse
  exact ((measurable_ambientUpdate_joint P O).comp
    (measurable_fst.fst.prodMk measurable_snd)).prodMk
      (measurable_historyAppend.comp (measurable_fst.snd.prodMk measurable_snd))

def sampledResponse : Kernel (ResponseHistory A W) (A × W) :=
  π.comap Prod.snd measurable_snd ⊗ₖ
    ambientObservation.comap (fun q => (q.1.1,q.2)) (by fun_prop)

instance sampledResponse_isMarkov : IsMarkovKernel (sampledResponse π) := by
  unfold sampledResponse
  infer_instance

/-- The response process runs EXACTLY the same π on its literal observed past.
It does not choose a policy from a belief or inspect the hidden state. -/
def responseHistoryKernel : Kernel (ResponseHistory A W) (ResponseHistory A W) :=
  Kernel.snd (sampledResponse π ⊗ₖ
    Kernel.deterministic (nextResponse P O) (measurable_nextResponse P O))

instance responseHistoryKernel_isMarkov : IsMarkovKernel (responseHistoryKernel P O π) := by
  unfold responseHistoryKernel
  infer_instance

omit [StandardBorelSpace Z] in
private theorem lintegral_responseHistoryKernel (r : ResponseHistory A W)
    (F : ResponseHistory A W → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, F s ∂responseHistoryKernel P O π r) =
      ∫⁻ a, ∫⁻ w, F (nextResponse P O (r,(a,w))) ∂ambientObservation (r.1,a) ∂π r.2 := by
  rw [responseHistoryKernel,Kernel.lintegral_snd _ _ hF,Kernel.lintegral_compProd]
  simp_rw [Kernel.lintegral_deterministic' (measurable_nextResponse P O) hF]
  rw [sampledResponse,Kernel.lintegral_compProd]
  · rfl
  all_goals fun_prop

/-- Actual joint step transport includes action/observation correlations through
the appended full history. Only actual-observation-a.e. posterior versions are used. -/
theorem actual_history_response_step (r : BeliefHistory Z A W) :
    (beliefHistoryKernel P O π r).map (projectResponse P O) =
      responseHistoryKernel P O π (projectResponse P O r) := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro F hF
  rw [lintegral_map hF (measurable_projectResponse P O)]
  have hc : Measurable (fun s => F (projectResponse P O s)) :=
    hF.comp (measurable_projectResponse P O)
  rw [lintegral_beliefHistoryKernel P O π r (fun s => F (projectResponse P O s)) hc,
    lintegral_responseHistoryKernel P O π (projectResponse P O r) F hF]
  change (∫⁻ a, ∫⁻ w, F (projectResponse P O (nextBelief P O (r,(a,w))))
    ∂c1BeliefObservationKernel P O (r.1,a) ∂π r.2) = _
  apply lintegral_congr
  intro a
  rw [show c1BeliefObservationKernel P O (r.1,a) = observationLaw r.1.toMeasure P O a from
    c1BeliefActionJoint_fst_eq_observationLaw P O r.1 a]
  change _ = ∫⁻ w, F (nextResponse P O (projectResponse P O r,(a,w)))
    ∂ambientObservation (response P O r.1,a)
  rw [ambientObservation_actual]
  apply lintegral_congr_ae
  filter_upwards [ambientUpdate_actual_response_ae P O r.1 a] with w hw
  simp only [projectResponse,nextBelief,nextResponse]
  rw [hw]

/-- Existing path naturality transports the full response/history path of this
same history policy. No altered selector or Markov-in-belief policy is substituted. -/
theorem actual_response_history_path (r : BeliefHistory Z A W) :
    (homTrajMeasure (Measure.dirac r) (beliefHistoryKernel P O π)).map (mapPath (projectResponse P O)) =
      homTrajMeasure (Measure.dirac (projectResponse P O r)) (responseHistoryKernel P O π) := by
  have hl : StrongLumpability (beliefHistoryKernel P O π) (responseHistoryKernel P O π)
      (projectResponse P O) (measurable_projectResponse P O) :=
    (strongLumpability_iff_apply _ _ _ _).mpr (actual_history_response_step P O π)
  have h := homTrajMeasure_path_naturality (Measure.dirac r)
    (beliefHistoryKernel P O π) (responseHistoryKernel P O π)
    (projectResponse P O) (measurable_projectResponse P O) hl
  simpa only [Measure.map_dirac' (measurable_projectResponse P O)] using h

/-- Actual retained-latent source to complete response/history path. The source
latent is initialized once and is advanced by P/O at every later step. -/
theorem actual_physical_response_history_path (r : BeliefHistory Z A W) :
    (homTrajMeasure (historyLatentLift r) (physicalHistoryKernel P O π)).map
      (mapPath (fun q => projectResponse P O q.1)) =
      homTrajMeasure (Measure.dirac (projectResponse P O r)) (responseHistoryKernel P O π) := by
  calc
    _ = ((homTrajMeasure (historyLatentLift r) (physicalHistoryKernel P O π)).map (mapPath Prod.fst)).map
        (mapPath (projectResponse P O)) :=
      (Measure.map_map (measurable_mapPath _ (measurable_projectResponse P O))
        (measurable_mapPath Prod.fst measurable_fst)).symm
    _ = _ := by rw [actual_belief_history_path,actual_response_history_path]

/-- The entire literal action-observation history sequence has the same law.
This compares the actual physical experiment with its computed response process. -/
theorem actual_action_observation_history_path (b : ProbabilityMeasure Z) :
    (homTrajMeasure (historyLatentLift (b,([] : History A W))) (physicalHistoryKernel P O π)).map
      (mapPath (fun q => q.1.2)) =
      (homTrajMeasure (Measure.dirac (response P O b,([] : History A W)))
        (responseHistoryKernel P O π)).map (mapPath Prod.snd) := by
  have h := congrArg (fun μ : Measure (ℕ → ResponseHistory A W) => μ.map (mapPath Prod.snd))
    (actual_physical_response_history_path P O π (b,([] : History A W)))
  have hm : Measurable (fun q : BeliefHistory Z A W × Z => projectResponse P O q.1) :=
    (measurable_projectResponse P O).comp measurable_fst
  rw [Measure.map_map (measurable_mapPath Prod.snd measurable_snd) (measurable_mapPath _ hm)] at h
  exact h

/-- Every finite complete action-observation prefix is preserved, with the same
registered initial belief and the same arbitrary measurable history controller. -/
theorem actual_finite_action_observation_history_path (b : ProbabilityMeasure Z) (n : ℕ) :
    ((homTrajMeasure (historyLatentLift (b,([] : History A W))) (physicalHistoryKernel P O π)).map
      (Preorder.frestrictLe n)).map (mapHistory (fun q => q.1.2) n) =
      ((homTrajMeasure (Measure.dirac (response P O b,([] : History A W)))
        (responseHistoryKernel P O π)).map (Preorder.frestrictLe n)).map (mapHistory Prod.snd n) := by
  have h := congrArg (fun μ : Measure (ℕ → History A W) => μ.map (Preorder.frestrictLe n))
    (actual_action_observation_history_path P O π b)
  rw [Measure.map_map (Preorder.measurable_frestrictLe n)
      (measurable_mapPath _ (by fun_prop)),
    Measure.map_map (Preorder.measurable_frestrictLe n) (measurable_mapPath Prod.snd measurable_snd),
    frestrictLe_mapPath,frestrictLe_mapPath,
    ← Measure.map_map (measurable_mapHistory _ (by fun_prop) n) (Preorder.measurable_frestrictLe n),
    ← Measure.map_map (measurable_mapHistory Prod.snd measurable_snd n) (Preorder.measurable_frestrictLe n)] at h
  exact h

namespace GaussianConsumer
open MeasurablePredictiveResponseRecursion.GaussianConsumer

/-- The SAME non-atomic shared-Gaussian source is consumed by every measurable
integer-action full-observation-history policy, not just belief-Markov policies. -/
theorem actual_gaussian_history_path (π : HistoryPolicy ℤ ℝ) [IsMarkovKernel π]
    (b : ProbabilityMeasure (ℝ × ℝ)) :
    (homTrajMeasure (historyLatentLift (b,([] : History ℤ ℝ)))
      (physicalHistoryKernel allowedSource allowedObservation π)).map (mapPath (fun q => q.1.2)) =
      (homTrajMeasure (Measure.dirac (response allowedSource allowedObservation b,([] : History ℤ ℝ)))
        (responseHistoryKernel allowedSource allowedObservation π)).map (mapPath Prod.snd) :=
  actual_action_observation_history_path allowedSource allowedObservation π b

end GaussianConsumer

namespace MemoryWitness

def coin : PMF Bool := PMF.uniformOfFintype Bool

def transition : Kernel (Unit × Bool) Unit := Kernel.const _ (Measure.dirac ())
instance transition_isMarkov : IsMarkovKernel transition := by unfold transition; infer_instance

def observation : Kernel (Unit × Bool) Bool := Kernel.const _ coin.toMeasure
instance observation_isMarkov : IsMarkovKernel observation := by unfold observation; infer_instance

/-- The first two actions are fixed; at time two the policy uses the FIRST
observation, which is absent from the common last event of the witness histories. -/
def memoryAction (h : History Bool Bool) : Bool :=
  if h.length < 2 then false else Sum.elim (fun _ => false) Prod.snd (symbolAt h 0)

def policy : HistoryPolicy Bool Bool := Kernel.deterministic memoryAction (measurable_of_countable _)
instance policy_isMarkov : IsMarkovKernel policy := by unfold policy; infer_instance

def firstFalse : History Bool Bool := [(false,false),(false,true)]
def firstTrue : History Bool Bool := [(false,true),(false,true)]

/-- Equal time and last action/observation do not determine this permitted
controller's actual action law; earlier observed history matters. -/
theorem strictly_history_sensitive :
    firstFalse.length = firstTrue.length ∧ firstFalse.getLast? = firstTrue.getLast? ∧
      policy firstFalse ≠ policy firstTrue := by
  refine ⟨rfl,rfl,?_⟩
  intro h
  have hm := congrArg (fun μ : Measure Bool => μ {false}) h
  norm_num [policy,Kernel.deterministic_apply,memoryAction,firstFalse,firstTrue,symbolAt,historyCode] at hm

def historyRow (h : History Bool Bool) : PMF (History Bool Bool) :=
  coin.map (fun w => h ++ [(memoryAction h,w)])

def historyKernel : Kernel (History Bool Bool) (History Bool Bool) :=
  Kernel.ofFunOfCountable (fun h => (historyRow h).toMeasure)

instance historyKernel_isMarkov : IsMarkovKernel historyKernel where
  isProbabilityMeasure h := by change IsProbabilityMeasure (historyRow h).toMeasure; infer_instance

private theorem observation_law (b : ProbabilityMeasure Unit) (a : Bool) :
    observationLaw b.toMeasure transition observation a = coin.toMeasure := by
  ext E hE
  rw [observationLaw,Measure.bind_apply hE (Kernel.aemeasurable _)]
  simp [fixedActionKernel,observation,Kernel.comap_apply]

/-- The witness's history-only row is derived from the SAME actual P/O/filter
row, without computing or replacing its posterior version. -/
private theorem actual_history_row (r : BeliefHistory Unit Bool Bool) :
    (beliefHistoryKernel transition observation policy r).map Prod.snd = historyKernel r.2 := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro F hF
  rw [lintegral_map hF measurable_snd,
    lintegral_beliefHistoryKernel transition observation policy r (fun s => F s.2) (hF.comp measurable_snd)]
  simp only [policy,Kernel.deterministic_apply]
  rw [lintegral_dirac' _ (measurable_of_finite _)]
  rw [show c1BeliefObservationKernel transition observation (r.1,memoryAction r.2) = coin.toMeasure from
    (c1BeliefActionJoint_fst_eq_observationLaw transition observation r.1 _).trans (observation_law r.1 _)]
  change (∫⁻ w, F (r.2 ++ [(memoryAction r.2,w)]) ∂coin.toMeasure) =
    ∫⁻ ys, F ys ∂(historyRow r.2).toMeasure
  rw [historyRow,← PMF.toMeasure_map _ _ (measurable_of_finite _),
    lintegral_map hF (measurable_of_finite _)]

/-- Source-path realization of the history-sensitive policy, initialized at
the same registered latent belief and empty actual event history. -/
private theorem actual_history_path (b : ProbabilityMeasure Unit) :
    (homTrajMeasure (historyLatentLift (b,([] : History Bool Bool)))
      (physicalHistoryKernel transition observation policy)).map (mapPath (fun q => q.1.2)) =
      homTrajMeasure (Measure.dirac ([] : History Bool Bool)) historyKernel := by
  have hl := (strongLumpability_iff_apply (beliefHistoryKernel transition observation policy)
    historyKernel Prod.snd measurable_snd).mpr actual_history_row
  have hp := homTrajMeasure_path_naturality (Measure.dirac (b,([] : History Bool Bool)))
    (beliefHistoryKernel transition observation policy) historyKernel Prod.snd measurable_snd hl
  rw [Measure.map_dirac' measurable_snd] at hp
  calc
    _ = ((homTrajMeasure (historyLatentLift (b,([] : History Bool Bool)))
        (physicalHistoryKernel transition observation policy)).map (mapPath Prod.fst)).map (mapPath Prod.snd) :=
      (Measure.map_map (measurable_mapPath Prod.snd measurable_snd)
        (measurable_mapPath Prod.fst measurable_fst)).symm
    _ = _ := by rw [actual_belief_history_path]; exact hp

private theorem bind_history_measure (p : PMF (History Bool Bool)) :
    (p.bind historyRow).toMeasure = historyKernel ∘ₘ p.toMeasure := by
  ext E hE
  rw [PMF.toMeasure_bind_apply (p:=p) (f:=historyRow) E hE,Measure.bind_apply hE (Kernel.aemeasurable _),lintegral_countable']
  apply tsum_congr
  intro h
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  change p h * (historyRow h).toMeasure E = (historyRow h).toMeasure E * p h
  exact mul_comm _ _

private theorem history_time_two :
    (homTrajMeasure (Measure.dirac ([] : History Bool Bool)) historyKernel).map
      (fun z => z 2) = ((historyRow []).bind historyRow).toMeasure := by
  rw [UEOT.V3.Compression.Objecthood.homTrajMeasure_time_succ_general _ _ 1,
    homTrajMeasure_dirac_time_one]
  exact (bind_history_measure (historyRow [])).symm

private theorem first_histories_mass :
    ((historyRow []).bind historyRow) firstFalse = 1/4 ∧
      ((historyRow []).bind historyRow) firstTrue = 1/4 := by
  rw [historyRow,PMF.bind_map]
  norm_num [PMF.bind_apply,PMF.map_apply,tsum_fintype,historyRow,coin,
    PMF.uniformOfFintype_apply,memoryAction,firstFalse,firstTrue,symbolAt,historyCode]
  rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]
  norm_num

/-- Both differing decisions are reached with positive probability in the
literal actual source run: no selected histories or successful-only resampling. -/
theorem actual_positive_memory_histories (b : ProbabilityMeasure Unit) :
    let μ := (homTrajMeasure (historyLatentLift (b,([] : History Bool Bool)))
      (physicalHistoryKernel transition observation policy)).map (fun z => z 2 |>.1.2)
    μ {firstFalse} = 1/4 ∧ μ {firstTrue} = 1/4 := by
  dsimp only
  have he := congrArg (fun μ : Measure (ℕ → History Bool Bool) => μ.map (fun z => z 2))
    (actual_history_path b)
  rw [Measure.map_map (measurable_pi_apply 2) (measurable_mapPath _ (by fun_prop)),
    history_time_two] at he
  change (homTrajMeasure (historyLatentLift (b,([] : History Bool Bool)))
      (physicalHistoryKernel transition observation policy)).map
      (fun z => (z 2).1.2) = _ at he
  rw [he]
  simp only [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  exact first_histories_mass

end MemoryWitness

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveHistoryControl
