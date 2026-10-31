import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeNativeHomeostasis
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionGOASource

/-!
Original promise: P5/P12 organizational maintenance belongs to THIS native execution source.
Existing exact source: mode-free safeRepairKernel, actual P5 physical shadow, native full AST law and actual post-probe P12 carrier.
Premise reduced: derive initial state, one literal-tick kernel exchange and complete organization path law; no assumed clock/law equality.
Class: original restoring ASTs, actual returned p/q, original parent/modes/labels/fees; canonical organization is an explicit lossy readout, not a replacement record source.
Consumer: original P5 homeostatic marginals and maintained-parent P12 endpoint on the same native source; no clock grouping or added repair action.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultNativeOrganization
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.FiniteDiscountedControl UEOT.V3.DynamicsKernel UEOT.V3.ViabilityTrajectory UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.TheoryCompletion
open RegisterFaultDynamicProbeLifecycle RegisterSemanticInstructionScale RegisterActuatorScaleSource
open UEOT.V3.Compression.Objecthood UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultSource
open RegisterFaultJointRecord RegisterFaultInfiniteRecord RegisterInstructionPurposeScale
open RegisterInstructionRecoveryScale RegisterInstructionGOASource RegisterInstructionHomeostasis
open RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite RegisterFaultDynamicProbe
open scoped ENNReal
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩
set_option backward.isDefEq.respectTransparency false
local instance {n : ℕ} : MeasurableSpace (RepairOrganizationState (State n) Action Bool) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (RepairOrganizationState (State n) Action Bool) := ⟨fun _=>trivial⟩

def organization {n : ℕ} (i : Fin n) (m : Mechanism) (x : State n) :
    RepairOrganizationState (State n) Action Bool :=
  canonicalRepairOrganizationState (substrate i) codec m.goal x

/-- Exactly the original P5 system, without altering its repair or fault row. -/
def system {n : ℕ} (i : Fin n) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1) :=
  finiteJointRecurrentHomeostasisSystem
    (physical i) (target i m.goal) (target_fixed i m.goal) (certificate i m.goal)
    (substrate i) codec m.goal (compiled_dynamics_implements i m.goal)
    (fault i) epsilon he (actual_fault_envelope i m.goal)

private theorem map_mix {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X→Y) (Q F : PMF X) (epsilon : NNReal) (he : epsilon≤1) :
    (recurrentFaultMix Q F epsilon he).map f=
      recurrentFaultMix (Q.map f) (F.map f) epsilon he :=by
  classical
  ext y
  simp only [PMF.map_apply,recurrentFaultMix_apply,tsum_fintype]
  have hp (x : X) :
      (if y=f x then ((1-epsilon : NNReal) : ENNReal)*Q x+(epsilon : ENNReal)*F x else 0)=
      ((1-epsilon : NNReal) : ENNReal)*(if y=f x then Q x else 0)+
        (epsilon : ENNReal)*(if y=f x then F x else 0) :=by split_ifs <;> simp
  simp_rw [hp]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]

/-- One original mode-free organization step is one actual physical-mode step,
including fault ticks. Rebuilding code/controller costs no additional tick. -/
theorem actual_organization_row {n : ℕ} (i : Fin n) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (x : State n) :
    (system i m epsilon he).mixedKernel (organization i m x)=
      (sourceLaw i m epsilon he x).map (organization i m) :=by
  have hphys:=actual_physical_row i m epsilon he (compile i m.goal)
    (actual_compiled_restores i m.goal) x
  rw [←hphys,RegisterFaultControlSource.physicalSource,map_mix]
  change recurrentFaultMix
    (safeRepairKernel (substrate i) codec (physical i) (organization i m x))
    (fault i (organization i m x)) epsilon he=_
  congr 1
  simp [fault,damage,organization,canonicalRepairOrganizationState,codec,PMF.pure_map]

def organizationKernel {n : ℕ} (i : Fin n) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) :
    Kernel (RepairOrganizationState (State n) Action Bool) (RepairOrganizationState (State n) Action Bool) :=
  Kernel.ofFunOfCountable fun s=>((system i m epsilon he).mixedKernel s).toMeasure

instance organizationKernel_markov {n : ℕ} (i : Fin n) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) : IsMarkovKernel (organizationKernel i m epsilon he) where
  isProbabilityMeasure s:=by change IsProbabilityMeasure ((system i m epsilon he).mixedKernel s).toMeasure;infer_instance

/-- Native words are read as their actual retained physical parent and the
already protected original source program. No record is removed or resampled. -/
def readWord {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n) (o : Organism n)
    (es : List Event) := organization i m (run i m (astPolicy p) ⟨0,o.physical,o⟩ es).2.2.physical

private theorem run_memory {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (c : Config (astPolicy p)) (hc : c.2.1=c.2.2.physical) (es : List Event) :
    (run i m (astPolicy p) c es).2.1=(run i m (astPolicy p) c es).2.2.physical :=by
  induction es generalizing c with
  | nil=>exact hc
  | cons e es ih=>apply ih;rfl

private theorem native_action {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n) (o : Organism n) (es : List Event) :
    ∀ᵐ e ∂(eventLaw noise epsilon he (astPolicy p) (run i m (astPolicy p) ⟨0,o.physical,o⟩ es)).toMeasure,
      e.1=interpret p (run i m (astPolicy p) ⟨0,o.physical,o⟩ es).2.2.physical :=by
  rw [ae_iff,PMF.toMeasure_apply_eq_zero_iff _ ((Set.toFinite _).measurableSet)]
  apply Set.disjoint_left.mpr
  intro e hs hbad
  apply (PMF.mem_support_iff _ _).mp hs
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) ENNReal.zero_ne_top).mp
  rw [eventLaw_toReal]
  simp only [ENNReal.toReal_zero]
  have hprob : (astPolicy p).actionProb (run i m (astPolicy p) ⟨0,o.physical,o⟩ es).2.1 e.1=
      (if e.1=interpret p (run i m (astPolicy p) ⟨0,o.physical,o⟩ es).2.1 then (1 : ℝ) else 0) :=by
    simp [astPolicy,selectorPolicy]
  rw [eventWeight,hprob,run_memory i m p _ rfl es,if_neg hbad]
  simp

/-- Exact exchange for the native source's actual one-tick row. -/
theorem native_organization_row {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n)
    (hc : restorationCheck i m.goal p=true) (o : Organism n) (es : List Event) :
    (wordKernel i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩ es).map (readWord i m p o)=
      organizationKernel i m epsilon he (readWord i m p o es) :=by
  let c:=run i m (astPolicy p) ⟨0,o.physical,o⟩ es
  change ((eventLaw noise epsilon he (astPolicy p) c).map (fun e=>es++[e])).toMeasure.map (readWord i m p o)=_
  rw [←PMF.toMeasure_map _ _ (measurable_of_finite _),Measure.map_map (measurable_of_countable _) (measurable_of_finite _)]
  have hevent : (fun e=>readWord i m p o (es++[e]))=ᵐ[(eventLaw noise epsilon he (astPolicy p) c).toMeasure]
      (fun e=>organization i m (resetState i m c.2.2.physical e.2.1)) :=by
    filter_upwards [native_action i noise m epsilon he p o es] with e ha
    change organization i m (run i m (astPolicy p) ⟨0,o.physical,o⟩ (es++[e])).2.2.physical=_
    have happ : run i m (astPolicy p) ⟨0,o.physical,o⟩ (es++[e])=advance i m (astPolicy p) c e :=by
      unfold RegisterFaultInfiniteRecord.run
      rw [List.foldl_append]
      rfl
    rw [happ]
    change organization i m (modeRecordStep i m c.2.2 e.1 e.2.1 e.2.2).transaction.parentAfter.physical=_
    rw [step_physical,ha,actual_mode_next i m p hc]
  change (eventLaw noise epsilon he (astPolicy p) c).toMeasure.map (fun e=>readWord i m p o (es++[e]))=_
  rw [Measure.map_congr hevent]
  have hmode : (eventLaw noise epsilon he (astPolicy p) c).map (fun e=>e.2.1)=RegisterFaultControlModel.modeLaw epsilon he :=by
    have h:=congrArg (fun q : PMF (Bool×Bool)=>q.map Prod.fst)
      (RegisterInstructionNativeSource.event_primitive_law noise epsilon he (astPolicy p) c)
    rw [PMF.map_comp] at h
    exact h.trans (primitive_mode noise epsilon he)
  let g : Bool→RepairOrganizationState (State n) Action Bool:=fun mode=>organization i m (resetState i m c.2.2.physical mode)
  have hmaps:=congrArg (fun q : PMF Bool=>q.map g) hmode
  rw [PMF.map_comp] at hmaps
  calc
    _ = ((eventLaw noise epsilon he (astPolicy p) c).map (g∘(fun e : Event=>e.2.1))).toMeasure :=
      PMF.toMeasure_map _ _ (measurable_of_finite _)
    _ = ((RegisterFaultControlModel.modeLaw epsilon he).map g).toMeasure := congrArg PMF.toMeasure hmaps
    _ = _ :=by
      change _=((system i m epsilon he).mixedKernel (organization i m c.2.2.physical)).toMeasure
      rw [actual_organization_row,sourceLaw,PMF.map_comp]
      rfl

/-- Complete P5 organizational trajectory is the same native source readout,
including time zero; no separate clock or path-law identity is assumed. -/
theorem native_organization_path_law {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n)
    (hc : restorationCheck i m.goal p=true) (o : Organism n) :
    (wordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩).map (mapPath (readWord i m p o))=
      homTrajMeasure (Measure.dirac (organization i m o.physical)) (organizationKernel i m epsilon he) :=by
  have hl : StrongLumpability (wordKernel i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩)
      (organizationKernel i m epsilon he) (readWord i m p o) (measurable_of_countable _) :=by
    apply (strongLumpability_iff_apply _ _ _ _).mpr
    exact native_organization_row i noise m epsilon he p hc o
  have h:=homTrajMeasure_path_naturality (Measure.dirac ([] : List Event))
    (wordKernel i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩)
    (organizationKernel i m epsilon he) (readWord i m p o) (measurable_of_countable _) hl
  rw [Measure.map_dirac' (measurable_of_countable _)] at h
  exact h

/-- Read the ACTUAL protected parent program as well as physical state. The
controller coordinate is the original P5 representation of that source bit;
it does not replace the literal AST or its fee/birth/label records. -/
def readRecord {n : ℕ} (i : Fin n) (r : ModeRecord n) : RepairOrganizationState (State n) Action Bool:=
  canonicalRepairOrganizationState (substrate i) codec r.transaction.parentBefore.program r.transaction.parentBefore.physical

@[fun_prop] theorem measurable_readRecord {n : ℕ} (i : Fin n) : Measurable (readRecord i):=
  fun _ _=>trivial

private theorem run_program {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (c : Config (astPolicy p)) (es : List Event) :
    (run i m (astPolicy p) c es).2.2.program=c.2.2.program :=by
  induction es generalizing c with
  | nil=>rfl
  | cons e es ih=>
    rw [run,List.foldl_cons]
    exact (ih _).trans (step_program i m c.2.2 e.1 e.2.1 e.2.2)

/-- The actual record's organization keeps the actual parent physical/program
coordinates. Source alignment is proved, not an installation of a target bit. -/
theorem actual_record_readout {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (ho : o.program=m.goal) (z : ℕ→List Event) (t : ℕ) :
    readRecord i (RegisterFaultInfiniteRecord.recordAt i m (astPolicy p) ⟨0,o.physical,o⟩ z t)=
      readWord i m p o (z t) :=by
  have hbefore (parent : Organism n) (e : Event) :
      (modeRecordStep i m parent e.1 e.2.1 e.2.2).transaction.parentBefore=parent :=by
    rcases e with ⟨a,mode,label⟩
    cases mode <;> rfl
  unfold RegisterFaultInfiniteRecord.recordAt readRecord readWord organization
  rw [hbefore,run_program,ho]

private theorem run_history {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (c : Config (astPolicy p)) (es : List Event) :
    (run i m (astPolicy p) c es).2.2.history=c.2.2.history :=by
  induction es generalizing c with
  | nil=>rfl
  | cons e es ih=>
    rw [run,List.foldl_cons]
    exact (ih _).trans (step_history i m c.2.2 e.1 e.2.1 e.2.2)

/-- Reattaching the original source history reconstructs the ACTUAL native
parent, not merely another object with an assigned identity. Holds for every
word and every AST, without a restoration or correct-target assumption. -/
theorem actual_parent_reconstructed {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (z : ℕ→List Event) (t : ℕ) :
    parentView o.history (readRecord i (RegisterFaultInfiniteRecord.recordAt i m (astPolicy p) ⟨0,o.physical,o⟩ z t))=
      (RegisterFaultInfiniteRecord.recordAt i m (astPolicy p) ⟨0,o.physical,o⟩ z t).transaction.parentBefore :=by
  have hbefore : (RegisterFaultInfiniteRecord.recordAt i m (astPolicy p) ⟨0,o.physical,o⟩ z t).transaction.parentBefore=
      (run i m (astPolicy p) ⟨0,o.physical,o⟩ (z t)).2.2 :=by
    unfold RegisterFaultInfiniteRecord.recordAt
    generalize eventAt z t=e
    rcases e with ⟨a,mode,label⟩
    cases mode <;> rfl
  have hh : (RegisterFaultInfiniteRecord.recordAt i m (astPolicy p) ⟨0,o.physical,o⟩ z t).transaction.parentBefore.history=o.history :=by
    rw [hbefore]
    exact run_history i m p _ _
  cases hr : (RegisterFaultInfiniteRecord.recordAt i m (astPolicy p) ⟨0,o.physical,o⟩ z t).transaction.parentBefore with
  | mk hist x bit=>
    have hhist : hist=o.history:=by simpa only [hr] using hh
    simp [readRecord,parentView,canonicalRepairOrganizationState,codec,hr,hhist]

/-- The whole actual native record source has this exact parent reconstruction
at every original transaction, including failed/fault records. -/
theorem native_parent_reconstructed {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n) (o : Organism n) :
    ∀ᵐ rs ∂recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩,
      ∀t : ℕ,parentView o.history (readRecord i (rs t))=(rs t).transaction.parentBefore :=by
  have hE : MeasurableSet {rs : ℕ→ModeRecord n |
      ∀t : ℕ,parentView o.history (readRecord i (rs t))=(rs t).transaction.parentBefore} :=by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun t=>(show MeasurableSet {r : ModeRecord n |
      parentView o.history (readRecord i r)=r.transaction.parentBefore} from trivial).preimage (measurable_pi_apply t)
  rw [recordPathLaw]
  apply (ae_map_iff (measurable_recordStream i m (astPolicy p) ⟨0,o.physical,o⟩).aemeasurable hE).2
  exact ae_of_all _ (fun z t=>actual_parent_reconstructed i m p o z t)

/-- Complete initial-inclusive organizational law, now read directly from the
SAME native FULL records. No histories/fees are changed in that original law. -/
theorem actual_record_organization_path_law {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n)
    (hc : restorationCheck i m.goal p=true) (o : Organism n) (ho : o.program=m.goal) :
    (recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩).map (mapPath (readRecord i))=
      homTrajMeasure (Measure.dirac (organization i m o.physical)) (organizationKernel i m epsilon he) :=by
  rw [recordPathLaw,Measure.map_map (measurable_mapPath _ (measurable_readRecord i))
    (measurable_recordStream i m (astPolicy p) ⟨0,o.physical,o⟩)]
  have hf : (mapPath (readRecord i)∘(fun z t=>RegisterFaultInfiniteRecord.recordAt i m (astPolicy p) ⟨0,o.physical,o⟩ z t))=
      mapPath (readWord i m p o) :=by
    funext z t
    exact actual_record_readout i m p o ho z t
  rw [hf]
  exact native_organization_path_law i noise m epsilon he p hc o

/-- Actual literal-time marginal equals the original P5 finite recursion at
THAT SAME time, including the actual possibly damaged post-probe initial state. -/
theorem actual_organization_marginal {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n)
    (hc : restorationCheck i m.goal p=true) (o : Organism n) (ho : o.program=m.goal) (t : ℕ) :
    (recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩).map (fun rs=>readRecord i (rs t))=
      (homeostaticMarginal (system i m epsilon he).mixedKernel (PMF.pure (organization i m o.physical)) t).toMeasure :=by
  have h:=congrArg (fun mu : Measure (ℕ→RepairOrganizationState (State n) Action Bool)=>mu.map (fun z=>z t))
    (actual_record_organization_path_law i noise m epsilon he p hc o ho)
  rw [Measure.map_map (measurable_pi_apply t) (measurable_mapPath _ (measurable_readRecord i))] at h
  have hm:=stationaryTrajMeasure_coordinate
    (fun s (_ : Unit)=>(system i m epsilon he).mixedKernel s) (fun _=>())
    (PMF.pure (organization i m o.physical)) t
  exact h.trans (by simpa [stationaryTrajMeasure,stationaryKernel,organizationKernel,homeostaticMarginal,PMF.toMeasure_pure] using hm)

/-- Original P12 maintained-parent carrier is now an ACTUAL native-source
all-time statement. The old P5 marginal endpoint is genuinely consumed at the
same literal transaction time, and no target/reset premise is needed. -/
theorem actual_post_parent_p12_native {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal) (b : Bool)
    (hs : classify price width d u (sourceData m width omega)=.repair b) :
    let parent:=postProbeParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    ∀ᵐ rs ∂recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,parent.physical,parent⟩,
      ∀t : ℕ,readRecord i (rs t)∈(system i m epsilon he).carrier ∧
        (lineage i).SameObject (parentView o.history (readRecord i (rs t))) parent :=by
  dsimp only
  have hp:=(postProbeParent_program i m omega o).trans ho
  have hc:=accepted_repair_restores i m price width d u omega b hs
  have hold:=actual_post_parent_p12_carrier i m epsilon he omega o ho
  have hstay:=homeostaticMarginal_staysIn (system i m epsilon he).mixedKernel
    (PMF.pure (organization i m (postProbeParent i m omega o).physical))
    (system i m epsilon he).carrier hold.2.1
    (fun _ h=>(system i m epsilon he).mixed_stays_carrier h)
  apply ae_all_iff.mpr
  intro t
  have horg : ∀ᵐ s ∂(homeostaticMarginal (system i m epsilon he).mixedKernel
      (PMF.pure (organization i m (postProbeParent i m omega o).physical)) t).toMeasure,
      s∈(system i m epsilon he).carrier ∧
        (lineage i).SameObject (parentView o.history s) (postProbeParent i m omega o) :=by
    rw [ae_iff,PMF.toMeasure_apply_eq_zero_iff _ ((Set.toFinite _).measurableSet)]
    apply Set.disjoint_left.mpr
    intro s hs hbad
    exact hbad ⟨hstay t hs,hold.2.2 t s hs⟩
  rw [←actual_organization_marginal i noise m epsilon he _ hc _ hp t] at horg
  exact ae_of_ae_map ((measurable_readRecord i).comp (measurable_pi_apply t)).aemeasurable horg

/-- BOTH actual returned programs consume the original P5 law at their actual
fine/coarse post-probe initial parents. No replacement policy is chosen. -/
theorem accepted_pair_organization_laws {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal) (b : Bool)
    (hs : classify price width d u (sourceData m width omega)=.repair b) :
    let parent:=postProbeParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    let q:=returnedProgram i p
    ((recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,parent.physical,parent⟩).map (mapPath (readRecord i))=
      homTrajMeasure (Measure.dirac (organization i m parent.physical)) (organizationKernel i m epsilon he)) ∧
    ((recordPathLaw (0 : Fin 1) noise m epsilon he (astPolicy q)
      ⟨0,(projectOrganism i parent).physical,projectOrganism i parent⟩).map (mapPath (readRecord 0))=
      homTrajMeasure (Measure.dirac (organization 0 m (projectOrganism i parent).physical)) (organizationKernel 0 m epsilon he)) :=by
  dsimp only
  have hc:=accepted_repair_restores i m price width d u omega b hs
  have hp:=(postProbeParent_program i m omega o).trans ho
  have hsyn:=RegisterFaultDynamicProbeInfinite.returned_synthesis i
    (classify price width d u (sourceData m width omega))
  exact ⟨actual_record_organization_path_law i noise m epsilon he _ hc _ hp,
    actual_record_organization_path_law 0 noise m epsilon he _
      ((returned_restoration_iff i m.goal _ _ hsyn).mp hc) _ hp⟩

private theorem measurable_joint_p12 {n N : ℕ} (i : Fin n) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) :
    MeasurableSet {z : (Coordinate N→Bool×Bool)×(ℕ→ModeRecord n) | ∀b : Bool,∀t : ℕ,
      classify price width d u (sourceData m width z.1)=.repair b→
        readRecord i (z.2 t)∈(system i m epsilon he).carrier ∧
        (lineage i).SameObject (parentView o.history (readRecord i (z.2 t))) (postProbeParent i m z.1 o)} :=by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro b
  apply MeasurableSet.iInter
  intro t
  let E : Set ((Coordinate N→Bool×Bool)×RepairOrganizationState (State n) Action Bool):=
    {v | classify price width d u (sourceData m width v.1)=.repair b→
      v.2∈(system i m epsilon he).carrier ∧
      (lineage i).SameObject (parentView o.history v.2) (postProbeParent i m v.1 o)}
  exact ((Set.toFinite E).measurableSet).preimage
    (measurable_fst.prodMk ((measurable_readRecord i).comp ((measurable_pi_apply t).comp measurable_snd)))

/-- ONE original training×native-deployment AE event: actual accepted p has
original P5 carrier/P12 parent identity at every SAME literal time. No Good,
positive-rate assumption, posterior filtering or resampling is required. -/
theorem actual_joint_p12_native {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) (ho : o.program=m.goal) :
    ∀ᵐ z ∂ RegisterFaultDynamicProbeInfinite.jointLaw (N:=N) i noise m epsilon he price width d u o,
      ∀b : Bool,∀t : ℕ,classify price width d u (sourceData m width z.1)=.repair b→
        readRecord i (z.2 t)∈(system i m epsilon he).carrier ∧
        (lineage i).SameObject (parentView o.history (readRecord i (z.2 t))) (postProbeParent i m z.1 o) :=by
  apply Measure.ae_compProd_of_ae_ae (measurable_joint_p12 i m epsilon he price width d u o)
  apply ae_of_all
  intro omega
  rw [ae_all_iff]
  intro b
  by_cases hs : classify price width d u (sourceData m width omega)=.repair b
  · filter_upwards [actual_post_parent_p12_native i noise m epsilon he price width d u omega o ho b hs] with rs hr
    exact fun t _=>hr t
  · exact ae_of_all _ (fun _ _ h=>False.elim (hs h))

/-- The SAME joint source now has native P5/P12 organization, genuine
long-run health AND original literal parent/resource/prepay. Environmental
funding remains the original explicit contract; no clock conversion occurs. -/
theorem funded_joint_p5_p12_native {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) (ho : o.program=m.goal)
    (cap g initial : ℝ) (hcap : (m.writeCost : ℝ)≤cap) (hg : cap≤g) (hi : 0 ≤ initial) :
    ∀ᵐ z ∂ RegisterFaultDynamicProbeInfinite.jointLaw (N:=N) i noise m epsilon he price width d u o,
      RegisterFaultDynamicProbeResource.wholeRecords i m o z∈RegisterFaultDynamicProbeLifecycle.SameParentTrace o.history ∧
      UEOT.V3.Compression.Objecthood.ResourceClosure.ResourceViable initial (fun _=>g)
        (fun t=>(RegisterFaultDynamicProbeResource.wholeRecords i m o z t).transaction.expenditure) ∧
      (∀t,(RegisterFaultDynamicProbeResource.wholeRecords i m o z t).transaction.expenditure≤
        RegisterFaultDynamicProbeResource.balance i m o initial g z t+g) ∧
      (∀b : Bool,classify price width d u (sourceData m width z.1)=.repair b→
        z.2∈RegisterFaultDynamicProbeNativeHomeostasis.frequency i epsilon ∧
        (epsilon<1→∀N : ℕ,∃t≥N,Legitimate i (z.2 t).transaction.parentAfter) ∧
        ∀t : ℕ,readRecord i (z.2 t)∈(system i m epsilon he).carrier ∧
          (lineage i).SameObject (parentView o.history (readRecord i (z.2 t))) (postProbeParent i m z.1 o)) :=by
  filter_upwards [actual_joint_p12_native (N:=N) i noise m epsilon he price width d u o ho,
    RegisterFaultDynamicProbeNativeHomeostasis.funded_joint_repair_long_run (N:=N) i noise m epsilon he price width d u o ho cap g initial hcap hg hi] with z hp hz
  refine ⟨hz.1,hz.2.1,hz.2.2.1,?_⟩
  intro b hb
  have hlife:=hz.2.2.2 b hb
  exact ⟨hlife.1,hlife.2.2.1,fun t=>hp b t hb⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultNativeOrganization
