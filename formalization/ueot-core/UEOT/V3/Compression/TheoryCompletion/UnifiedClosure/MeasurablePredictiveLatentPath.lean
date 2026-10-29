import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveJointPath

/-!
Original commitment: the posterior recorder represents the same controlled latent experiment.
Existing result: C1 joint disintegration and finite visible-belief record transport.
Reduced premise: derive latent/filter consistency from P/O execution, not a supplied conditional law.
Model: nonempty Standard Borel latent state, countably generated observations, measurable Markov policy.
Consumer: the same clocked record kernel; initial latent is sampled from the registered belief.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveLatentPath
open MeasureTheory ProbabilityTheory
open UEOT.V3.GeneralBayesPosterior
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open MeasurablePredictiveJointPath
open UEOT.V3.DynamicsKernel
open scoped ENNReal
attribute [local fun_prop] measurable_appendHistory
noncomputable section
variable {Z A W : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace W]
variable [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W]

/-- Read the actual probability law represented by a belief. -/
def beliefKernel : Kernel (ProbabilityMeasure Z) Z where
  toFun b := b.toMeasure
  measurable' := measurable_subtype_coe

instance beliefKernel_isMarkov : IsMarkovKernel (beliefKernel (Z:=Z)) where
  isProbabilityMeasure b := by change IsProbabilityMeasure b.toMeasure; infer_instance

/-- Consistency lift: retain the entire record and draw its latent from its own belief. -/
def latentLift : Kernel (RecordState Z A W) (RecordState Z A W × Z) :=
  Kernel.id ×ₖ beliefKernel.comap (fun r => r.2.1) (by fun_prop)

instance latentLift_isMarkov : IsMarkovKernel (latentLift (Z:=Z) (A:=A) (W:=W)) := by
  unfold latentLift
  infer_instance

/-- Primitive observation/next-latent execution, before taking any belief mixture. -/
def physicalEvent (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O] :
    Kernel ((RecordState Z A W × Z) × A) (W × Z) :=
  (c1OneStepJoint P O).comap (fun q => (q.1.2,q.2)) (by fun_prop)

instance physicalEvent_isMarkov (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O] : IsMarkovKernel (physicalEvent P O) := by
  unfold physicalEvent
  infer_instance

/-- The action reads the retained clock/belief; the actual latent only enters P/O. -/
def sampledPhysical (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π] :
    Kernel (RecordState Z A W × Z) (A × (W × Z)) :=
  (π.comap (fun q => (q.1.1,q.1.2.1)) (by fun_prop)) ⊗ₖ physicalEvent P O

instance sampledPhysical_isMarkov (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π] :
    IsMarkovKernel (sampledPhysical P O π) := by unfold sampledPhysical; infer_instance

/-- Keep the actual next latent while computing the SAME recursive filter from the observation. -/
def nextPhysical (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (q : (RecordState Z A W × Z) × (A × (W × Z))) : RecordState Z A W × Z :=
  (nextRecord P O (q.1.1,(q.2.1,q.2.2.1)),q.2.2.2)

@[fun_prop] theorem measurable_nextPhysical (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O] : Measurable (nextPhysical P O) := by
  unfold nextPhysical
  fun_prop

/-- Actual P/O/filter dynamics on a retained latent; no latent resampling between steps. -/
def physicalKernel (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π] :
    Kernel (RecordState Z A W × Z) (RecordState Z A W × Z) :=
  Kernel.snd (sampledPhysical P O π ⊗ₖ
    Kernel.deterministic (nextPhysical P O) (measurable_nextPhysical P O))

instance physicalKernel_isMarkov (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π] :
    IsMarkovKernel (physicalKernel P O π) := by unfold physicalKernel; infer_instance

/-- Actual P/O execution from the registered belief disintegrates through the SAME filter. -/
theorem actual_latent_joint_disintegration (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O] (b : ProbabilityMeasure Z) (a : A) :
    c1OneStepJoint P O ∘ₘ c1BeliefActionMeasure (b,a) =
      observationLaw b.toMeasure P O a ⊗ₘ c1PosteriorSection P O b a := by
  change c1BeliefActionJoint P O (b,a) = _
  rw [c1BeliefActionJoint_apply_eq_existing, c1PosteriorSection_factorization]

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
/-- The lift samples the latent once from the current belief and keeps the record literally. -/
theorem lintegral_latentLift (r : RecordState Z A W)
    (F : RecordState Z A W × Z → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q, F q ∂latentLift r) = ∫⁻ z, F (r,z) ∂r.2.1.toMeasure := by
  rw [latentLift, Kernel.id, Kernel.lintegral_deterministic_prod measurable_id _ _ hF]
  rfl

/-- Literal one-step integral: the old latent enters P/O, while the policy only sees its record. -/
theorem lintegral_physicalKernel (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (q : RecordState Z A W × Z) (F : RecordState Z A W × Z → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ s, F s ∂physicalKernel P O π q) =
      ∫⁻ a, ∫⁻ wz, F (nextRecord P O (q.1,(a,wz.1)),wz.2)
        ∂c1OneStepJoint P O (q.2,a) ∂π (q.1.1,q.1.2.1) := by
  rw [physicalKernel, Kernel.lintegral_snd _ _ hF, Kernel.lintegral_compProd]
  simp_rw [Kernel.lintegral_deterministic' (measurable_nextPhysical P O) hF]
  rw [sampledPhysical, Kernel.lintegral_compProd]
  · rfl
  all_goals fun_prop

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
/-- The belief mixture is the literal primitive transition/observation experiment. -/
theorem lintegral_belief_joint (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O] (b : ProbabilityMeasure Z) (a : A)
    (F : W × Z → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wz, F wz ∂c1BeliefActionJoint P O (b,a)) =
      ∫⁻ x, ∫⁻ wz, F wz ∂c1OneStepJoint P O (x,a) ∂b.toMeasure := by
  change (∫⁻ wz, F wz ∂(c1OneStepJoint P O ∘ₘ c1BeliefActionMeasure (b,a))) = _
  rw [Measure.lintegral_bind (c1OneStepJoint P O).aemeasurable hF.aemeasurable]
  change (∫⁻ xa, (∫⁻ wz, F wz ∂c1OneStepJoint P O xa)
    ∂b.toMeasure.prod (Measure.dirac a)) = _
  rw [Measure.prod_dirac, lintegral_map]
  all_goals fun_prop

/-- Integral semantics of the existing recorder, retaining action/observation correlations. -/
theorem lintegral_recordKernel (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (F : RecordState Z A W → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, F s ∂recordKernel P O π r) =
      ∫⁻ a, ∫⁻ w, F (nextRecord P O (r,(a,w)))
        ∂c1BeliefObservationKernel P O (r.2.1,a) ∂π (r.1,r.2.1) := by
  change (∫⁻ s, F s ∂Kernel.snd (sampledEvent P O π ⊗ₖ
    Kernel.deterministic (nextRecord P O) (measurable_nextRecord P O)) r) = _
  rw [Kernel.lintegral_snd _ _ hF, Kernel.lintegral_compProd]
  simp_rw [Kernel.lintegral_deterministic' (measurable_nextRecord P O) hF]
  rw [sampledEvent, Kernel.lintegral_compProd]
  · rfl
  all_goals fun_prop

/-- Conditional consistency is proved after drawing the latent from the registered
belief. Pointwise lumpability of arbitrary raw `(belief,latent)` pairs is not assumed. -/
theorem one_step_consistency_lintegral (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (F : RecordState Z A W × Z → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ q, F q ∂(physicalKernel P O π ∘ₘ latentLift r)) =
      ∫⁻ q, F q ∂(latentLift ∘ₘ recordKernel P O π r) := by
  rw [Measure.lintegral_bind (physicalKernel P O π).aemeasurable hF.aemeasurable,
    lintegral_latentLift r _ hF.lintegral_kernel,
    Measure.lintegral_bind latentLift.aemeasurable hF.aemeasurable]
  simp_rw [lintegral_physicalKernel P O π _ F hF]
  rw [lintegral_recordKernel P O π r _ (by
    have hm := (hF.lintegral_kernel (κ := latentLift))
    exact hm)]
  simp_rw [lintegral_latentLift _ F hF]
  have hm : Measurable (fun xa : Z × A =>
      ∫⁻ wz, F (nextRecord P O (r,(xa.2,wz.1)),wz.2)
        ∂c1OneStepJoint P O (xa.1,xa.2)) := by
    exact Measurable.lintegral_kernel_prod_right (by fun_prop)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro a
  have : IsProbabilityMeasure (observationLaw r.2.1.toMeasure P O a) := by
    unfold observationLaw
    infer_instance
  rw [← lintegral_belief_joint P O r.2.1 a _ (by fun_prop),
    c1BeliefActionJoint_apply_eq_existing, ← c1PosteriorSection_factorization,
    Measure.lintegral_compProd (by fun_prop)]
  rw [show c1BeliefObservationKernel P O (r.2.1,a) =
    observationLaw r.2.1.toMeasure P O a from
    c1BeliefActionJoint_fst_eq_observationLaw P O r.2.1 a]
  rfl

/-- The actual latent/filter step preserves the posterior consistency lift.
This identity integrates only the registered initial latent uncertainty. -/
theorem actual_one_step_consistency (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) :
    physicalKernel P O π ∘ₘ latentLift r = latentLift ∘ₘ recordKernel P O π r := by
  ext s hs
  have h := one_step_consistency_lintegral P O π r (s.indicator (fun _ => 1))
    (measurable_const.indicator hs)
  simpa [lintegral_indicator, hs] using h

/-- A proved stochastic intertwining, rather than pointwise raw-state lumpability. -/
theorem actual_kernel_intertwining (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π] :
    physicalKernel P O π ∘ₖ latentLift = latentLift ∘ₖ recordKernel P O π := by
  ext r s hs
  rw [Kernel.comp_apply, Kernel.comp_apply]
  exact congrArg (fun μ : Measure (RecordState Z A W × Z) => μ s)
    (actual_one_step_consistency P O π r)

/-- Summarize a genuine latent trajectory prefix without dropping any observed record. -/
def summarizePrefix (n : ℕ)
    (h : (i : Finset.Iic n) → RecordState Z A W × Z) :
    ((i : Finset.Iic n) → RecordState Z A W) × Z :=
  (mapHistory Prod.fst n h,(h (lastHistoryIndex n)).2)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
@[fun_prop] theorem measurable_summarizePrefix (n : ℕ) :
    Measurable (summarizePrefix (Z:=Z) (A:=A) (W:=W) n) := by
  unfold summarizePrefix
  exact (measurable_mapHistory Prod.fst measurable_fst n).prodMk
    (measurable_snd.comp (measurable_pi_apply _))

/-- Last filter of the entire observed prefix, not a separately chosen latent law. -/
def terminalBelief (n : ℕ) : Kernel ((i : Finset.Iic n) → RecordState Z A W) Z :=
  beliefKernel.comap (fun h => (h (lastHistoryIndex n)).2.1) (by fun_prop)

instance terminalBelief_isMarkov (n : ℕ) :
    IsMarkovKernel (terminalBelief (Z:=Z) (A:=A) (W:=W) n) := by
  unfold terminalBelief
  infer_instance

private theorem appendHistory_last {S : Type*} [MeasurableSpace S] (n : ℕ)
    (h : (i : Finset.Iic n) → S) (s : S) :
    appendHistory n (h,s) (lastHistoryIndex (n+1)) = s := by
  simp [appendHistory, lastHistoryIndex, IicProdIoc_def, MeasurableEquiv.piSingleton]

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W] in
private theorem summarize_append (n : ℕ)
    (h : (i : Finset.Iic n) → RecordState Z A W × Z) (q : RecordState Z A W × Z) :
    summarizePrefix (n+1) (appendHistory n (h,q)) =
      (appendHistory n ((summarizePrefix n h).1,q.1),q.2) := by
  rw [summarizePrefix, mapHistory_appendHistory, appendHistory_last]
  rfl

/-- Every complete finite observed record of the actual retained-latent experiment
has its last latent conditionally distributed as the SAME recursively computed filter. -/
theorem actual_finite_prefix_consistency (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) :
    (((homTrajMeasure (latentLift r) (physicalKernel P O π)).map
      (Preorder.frestrictLe n)).map (summarizePrefix n)) =
      ((homTrajMeasure (Measure.dirac r) (recordKernel P O π)).map
        (Preorder.frestrictLe n)) ⊗ₘ terminalBelief n := by
  induction n with
  | zero =>
    apply (Measure.ext_iff_lintegral _).mpr
    intro F hF
    rw [lintegral_map hF (measurable_summarizePrefix 0),
      homTrajMeasure_prefix_zero, lintegral_map (f := fun h => F (summarizePrefix 0 h)) (by fun_prop) (by fun_prop),
      lintegral_latentLift r _ (by fun_prop),
      Measure.lintegral_compProd hF, homTrajMeasure_prefix_zero,
      Measure.map_dirac' (by fun_prop), lintegral_dirac' _ (by fun_prop)]
    rfl
  | succ n ih =>
    let K := physicalKernel P O π
    let L := recordKernel P O π
    let μ := (homTrajMeasure (latentLift r) K).map (Preorder.frestrictLe n)
    let ν := (homTrajMeasure (Measure.dirac r) L).map (Preorder.frestrictLe n)
    let : IsMarkovKernel (homHistoryKernel K n) := isMarkovKernel_homHistoryKernel K n
    let : IsMarkovKernel (homHistoryKernel L n) := isMarkovKernel_homHistoryKernel L n
    apply (Measure.ext_iff_lintegral _).mpr
    intro F hF
    let G : (((i : Finset.Iic n) → RecordState Z A W) × Z) → ℝ≥0∞ := fun hz =>
      ∫⁻ q, F (appendHistory n (hz.1,q.1),q.2) ∂K (hz.1 (lastHistoryIndex n),hz.2)
    have hG : Measurable G := by
      change Measurable (fun hz => ∫⁻ q, F (appendHistory n (hz.1,q.1),q.2)
        ∂(K.comap (fun hz : (((i : Finset.Iic n) → RecordState Z A W) × Z) =>
          (hz.1 (lastHistoryIndex n),hz.2)) (by fun_prop)) hz)
      apply Measurable.lintegral_kernel_prod_right
      exact hF.comp ((measurable_appendHistory n).comp
        (measurable_fst.fst.prodMk measurable_snd.fst) |>.prodMk measurable_snd.snd)
    have hleft : (∫⁻ h, F h ∂((homTrajMeasure (latentLift r) K).map
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
    have hJ : Measurable (fun h : (i : Finset.Iic (n+1)) → RecordState Z A W =>
        ∫⁻ z, F (h,z) ∂terminalBelief (n+1) h) :=
      Measurable.lintegral_kernel_prod_right hF
    rw [Measure.lintegral_compProd hF, ← homTrajMeasure_prefix_succ,
      lintegral_map hJ (measurable_appendHistory n),
      Measure.lintegral_compProd (f := fun p =>
        ∫⁻ z, F (appendHistory n p,z) ∂terminalBelief (n+1) (appendHistory n p))
        (hJ.comp (measurable_appendHistory n))]
    apply lintegral_congr
    intro h
    change (∫⁻ z, G (h,z) ∂(h (lastHistoryIndex n)).2.1.toMeasure) = _
    have hstep := one_step_consistency_lintegral P O π (h (lastHistoryIndex n))
      (fun q => F (appendHistory n (h,q.1),q.2)) (by fun_prop)
    rw [Measure.lintegral_bind K.aemeasurable (by fun_prop),
      lintegral_latentLift _ _ (by fun_prop),
      Measure.lintegral_bind latentLift.aemeasurable (by fun_prop)] at hstep
    change (∫⁻ z, G (h,z) ∂(h (lastHistoryIndex n)).2.1.toMeasure) = _ at hstep
    rw [hstep]
    apply lintegral_congr
    intro q
    rw [lintegral_latentLift _ _ (by fun_prop)]
    simp only [terminalBelief, Kernel.comap_apply, beliefKernel, appendHistory_last]
    rfl

/-- The entire finite observed record is the recorder law of the SAME physical run. -/
theorem actual_finite_observed_path (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) (n : ℕ) :
    (((homTrajMeasure (latentLift r) (physicalKernel P O π)).map
      (Preorder.frestrictLe n)).map (mapHistory Prod.fst n)) =
      (homTrajMeasure (Measure.dirac r) (recordKernel P O π)).map
        (Preorder.frestrictLe n) := by
  have h := congrArg (fun μ : Measure ((((i : Finset.Iic n) → RecordState Z A W)) × Z) =>
    μ.map Prod.fst) (actual_finite_prefix_consistency P O π r n)
  rw [Measure.map_map measurable_fst (measurable_summarizePrefix n)] at h
  change _ = (((homTrajMeasure (Measure.dirac r) (recordKernel P O π)).map
    (Preorder.frestrictLe n)) ⊗ₘ terminalBelief n).fst at h
  rw [Measure.fst_compProd] at h
  exact h

/-- Existing countable-path uniqueness upgrades the derived finite-source
identities to the entire observed-record path law; it does not add a payoff claim. -/
theorem actual_observed_path (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (r : RecordState Z A W) :
    (homTrajMeasure (latentLift r) (physicalKernel P O π)).map (mapPath Prod.fst) =
      homTrajMeasure (Measure.dirac r) (recordKernel P O π) := by
  let : IsProbabilityMeasure ((homTrajMeasure (latentLift r) (physicalKernel P O π)).map
      (mapPath Prod.fst)) :=
    Measure.isProbabilityMeasure_map (measurable_mapPath Prod.fst measurable_fst).aemeasurable
  apply pathMeasure_eq_of_prefix_eq
  intro n
  rw [Measure.map_map (Preorder.measurable_frestrictLe n)
      (measurable_mapPath Prod.fst measurable_fst), frestrictLe_mapPath Prod.fst n,
    ← Measure.map_map (measurable_mapHistory Prod.fst measurable_fst n)
      (Preorder.measurable_frestrictLe n)]
  exact actual_finite_observed_path P O π r n

variable {Y H N : Type*} [MeasurableSpace Y] [MeasurableSpace H] [MeasurableSpace N]
variable [StandardBorelSpace Y] [StandardBorelSpace H] [Nonempty Y] [Nonempty H]
variable (noise : Measure N) [IsProbabilityMeasure noise]
variable (visible : (Y × A) × N → Y) (hv : Measurable visible)
variable (hidden : ((Y × H) × A) × N → H) (hh : Measurable hidden)
variable (sensor : Kernel (Y × A) W) [IsMarkovKernel sensor]
variable (π : Kernel (ℕ × ProbabilityMeasure Y) A) [IsMarkovKernel π]

/-- Actual retained microscopic latent trajectories, their recursive filter and
all sampled actions/observations have the computed visible C1 record law.
The initial microscopic latent is drawn from b; the action reads ONLY clock and
visible belief, through liftedPolicy. -/
theorem actual_source_finite_visible_joint_path
    (b : ProbabilityMeasure (Y × H)) (n : ℕ) :
    ((((homTrajMeasure (latentLift (0,(b,Sum.inl ())))
      (physicalKernel (MeasurablePredictiveSource.source noise visible hv hidden hh)
        (MeasurablePredictiveSensor.liftedSensor sensor) (liftedPolicy π))).map
      (Preorder.frestrictLe n)).map (mapHistory Prod.fst n)).map
      (mapHistory projectRecord n)) =
    (homTrajMeasure (Measure.dirac (0,(MeasurablePredictiveSource.coordinate b,Sum.inl ())))
      (recordKernel (MeasurablePredictiveSource.visibleKernel noise visible hv) sensor π)).map
      (Preorder.frestrictLe n) := by
  rw [actual_finite_observed_path]
  exact actual_finite_joint_path noise visible hv hidden hh sensor π b n

/-- Countable actual-source record law, derived from all finite coupled prefixes. -/
theorem actual_source_visible_joint_path (b : ProbabilityMeasure (Y × H)) :
    (homTrajMeasure (latentLift (0,(b,Sum.inl ())))
      (physicalKernel (MeasurablePredictiveSource.source noise visible hv hidden hh)
        (MeasurablePredictiveSensor.liftedSensor sensor) (liftedPolicy π))).map
      (mapPath (fun q => projectRecord q.1)) =
    homTrajMeasure (Measure.dirac (0,(MeasurablePredictiveSource.coordinate b,Sum.inl ())))
      (recordKernel (MeasurablePredictiveSource.visibleKernel noise visible hv) sensor π) := by
  have hp : Measurable (fun q : RecordState (Y × H) A W × (Y × H) => projectRecord q.1) := by
    fun_prop
  let : IsProbabilityMeasure ((homTrajMeasure (latentLift (0,(b,Sum.inl ())))
      (physicalKernel (MeasurablePredictiveSource.source noise visible hv hidden hh)
        (MeasurablePredictiveSensor.liftedSensor sensor) (liftedPolicy π))).map
      (mapPath (fun q => projectRecord q.1))) :=
    Measure.isProbabilityMeasure_map (measurable_mapPath _ hp).aemeasurable
  apply pathMeasure_eq_of_prefix_eq
  intro n
  rw [Measure.map_map (Preorder.measurable_frestrictLe n) (measurable_mapPath _ hp),
    frestrictLe_mapPath (fun q : RecordState (Y × H) A W × (Y × H) => projectRecord q.1) n,
    ← Measure.map_map (measurable_mapHistory _ hp n) (Preorder.measurable_frestrictLe n)]
  have h := actual_source_finite_visible_joint_path noise visible hv hidden hh sensor π b n
  rw [Measure.map_map (measurable_mapHistory projectRecord measurable_projectRecord n)
    (measurable_mapHistory Prod.fst measurable_fst n)] at h
  exact h

/-- Literal time-varying current-visible-belief policies use the same source,
initial belief and policy family on both sides. -/
theorem actual_source_timevarying_joint_path
    (policies : ℕ → Kernel (ProbabilityMeasure Y) A) [∀ t, IsMarkovKernel (policies t)]
    (b : ProbabilityMeasure (Y × H)) :
    (homTrajMeasure (latentLift (0,(b,Sum.inl ())))
      (physicalKernel (MeasurablePredictiveSource.source noise visible hv hidden hh)
        (MeasurablePredictiveSensor.liftedSensor sensor) (liftedPolicy (timedPolicy policies)))).map
      (mapPath (fun q => projectRecord q.1)) =
    homTrajMeasure (Measure.dirac (0,(MeasurablePredictiveSource.coordinate b,Sum.inl ())))
      (recordKernel (MeasurablePredictiveSource.visibleKernel noise visible hv) sensor
        (timedPolicy policies)) :=
  actual_source_visible_joint_path noise visible hv hidden hh sensor (timedPolicy policies) b

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveLatentPath
