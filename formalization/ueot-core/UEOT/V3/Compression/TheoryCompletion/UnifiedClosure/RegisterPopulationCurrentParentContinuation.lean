import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFiniteGenerationCommonConsumer

/-!
Original promise: the actual birth episode's SAME retained owner continues with viable resources.
Existing results: exact finite owner/phase execution, same-source discovery/P8/Price and one finite wallet; native ANY-AST laws/P5.
Reduced premise: derive the actual terminal root's state/program/owner and seed its native law, then debit its true remaining wallet.
Family: original single founder, THIS AST, plan [0,0,h], all faults/None/reads; NEW registered continuation inflow g>=cap before each real tail fee only.
Consumer: finite-base-preserving joint continuation, actual current-parent P5/P12/life, and whole-account P6/prepay; no closed-wallet infinity or population GOD.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationCurrentParentContinuation
open Set MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite RegisterFaultDynamicProbe
open RegisterInstructionPurposeScale RegisterSemanticInstructionScale RegisterActuatorScaleSource
open RegisterInstructionRecoveryScale RegisterFaultDynamicProbeLifecycle
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord Identity)
open RegisterPopulationHistorySource (Store Request)
open RegisterFiniteGenerationCommonConsumer
open scoped BigOperators ENNReal
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ClockedRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ClockedRecord n) := ⟨fun _=>trivial⟩
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _=>trivial⟩

private theorem root_length_pos {n : ℕ} (s : Store n) (p : ClockedOrganism n)
    (hp : RegisterPopulationHistorySource.lookup s 0=some p) : 0<s.length :=by
  cases s with
  | nil=>simp [RegisterPopulationHistorySource.lookup] at hp
  | cons a s=>simp

/-- Every real root update retains the actual history/program/owner. Missing
or other-slot dispatch does not replace root0 or install an extra founder. -/
theorem old_next_root {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request)
    (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s 0=some p) :
    ∃p',RegisterPopulationHistorySource.lookup (RegisterOwnProgramPopulation.next i c s q) 0=some p' ∧
      p'.organism.program=p.organism.program ∧ p'.organism.history=p.organism.history ∧ p'.identity=p.identity :=by
  by_cases hq : q.parent=0
  · have hh : RegisterPopulationHistorySource.lookup s q.parent=some p:=by rw [hq];exact hp
    have hr:=RegisterOwnProgramPopulation.retained_parent_identity i c s q p hh
    refine ⟨(RegisterTimestampedBirthSource.step i ⟨p.organism.program,c⟩
      {p with clock:=s.length} q.action q.mode q.label).parentAfter,
      by simpa only [hq] using hr.1,?_,?_,rfl⟩
    · exact step_program i ⟨p.organism.program,c⟩ p.organism q.action q.mode q.label
    · exact step_history i ⟨p.organism.program,c⟩ p.organism q.action q.mode q.label
  · refine ⟨p,?_,rfl,rfl,rfl⟩
    exact (RegisterOwnProgramPopulation.next_other_slot i c s q 0 (root_length_pos s p hp) hq).trans hp

theorem old_run_root {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request)
    (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s 0=some p) :
    ∃p',RegisterPopulationHistorySource.lookup (RegisterOwnProgramPopulation.run i c s es) 0=some p' ∧
      p'.organism.program=p.organism.program ∧ p'.organism.history=p.organism.history ∧ p'.identity=p.identity :=by
  induction es generalizing s p with
  | nil=>exact ⟨p,hp,rfl,rfl,rfl⟩
  | cons q es ih=>
    obtain ⟨p',hp',hg,hh,hi⟩:=old_next_root i c s q p hp
    obtain ⟨p'',hp'',hg',hh',hi'⟩:=ih _ p' hp'
    exact ⟨p'',hp'',hg'.trans hg,hh'.trans hh,hi'.trans hi⟩

variable {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
  (omega : Coordinate N→Bool×Bool) (o : ClockedOrganism n) (h : Bool) (w : Fin 3→Bool×Bool)

def oldTerminalStore : Store n := RegisterOwnProgramPopulation.run i m.writeCost
  (RegisterFaultDynamicProbePopulation.registeredParent i m omega o.organism)
  (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w)

/-- getD is an executable totalization; root_exists below proves the fallback
is NEVER used on this complete source, even when the first birth fails. -/
def oldTerminalRoot : ClockedOrganism n :=
  (RegisterPopulationHistorySource.lookup (oldTerminalStore i m price width d u omega o h w) 0).getD
    ⟨postProbeParent i m omega o.organism,[(0,false)],0⟩

theorem root_exists :
    RegisterPopulationHistorySource.lookup (oldTerminalStore i m price width d u omega o h w) 0=
      some (oldTerminalRoot i m price width d u omega o h w) ∧
    (oldTerminalRoot i m price width d u omega o h w).organism.program=o.organism.program ∧
    (oldTerminalRoot i m price width d u omega o h w).organism.history=o.organism.history ∧
    (oldTerminalRoot i m price width d u omega o h w).identity=[(0,false)] :=by
  obtain ⟨p,hp,hg,hh,hi⟩:=old_run_root i m.writeCost
    (RegisterFaultDynamicProbePopulation.registeredParent i m omega o.organism) _
    ⟨postProbeParent i m omega o.organism,[(0,false)],0⟩
    (RegisterFaultDynamicProbePopulation.registered_lookup i m omega o.organism)
  have heq : oldTerminalRoot i m price width d u omega o h w=p:=by
    simp only [oldTerminalRoot,oldTerminalStore] at hp ⊢
    rw [hp]
    rfl
  rw [heq]
  exact ⟨hp,hg.trans (postProbeParent_program i m omega o.organism),
    hh.trans (RegisterFaultDynamicProbeLifecycle.postProbeParent_history i m omega o.organism),hi⟩

/-- This is the actual terminal store root, including its CURRENT physical
state and stored last-update clock. There is no target/post-training reset. -/
def currentParent : ClockedOrganism n :=
  RegisterPopulationOwnerClockTransport.parentView o.identity (o.clock+2*N)
    (oldTerminalRoot i m price width d u omega o h w)

theorem actual_current_lookup :
    RegisterPopulationHistorySource.lookup
      (RegisterPopulationOwnerClockTransport.run i m.writeCost (o.clock+2*N)
        [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
        (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w)) 0=
      some (currentParent i m price width d u omega o h w) :=by
  rw [←RegisterPopulationOwnerClockTransport.actual_registered_postClocked i m omega o,
    RegisterPopulationOwnerClockTransport.run_view,RegisterPopulationOwnerClockTransport.lookup_view]
  change (RegisterPopulationHistorySource.lookup (oldTerminalStore i m price width d u omega o h w) 0).map
    (RegisterPopulationOwnerClockTransport.parentView o.identity (o.clock+2*N))=_
  rw [(root_exists i m price width d u omega o h w).1]
  rfl

theorem current_parent_source :
    (currentParent i m price width d u omega o h w).organism.program=o.organism.program ∧
    (currentParent i m price width d u omega o h w).organism.history=o.organism.history ∧
    (currentParent i m price width d u omega o h w).identity=o.identity ∧
    (currentParent i m price width d u omega o h w).organism=
      (oldTerminalRoot i m price width d u omega o h w).organism ∧
    (currentParent i m price width d u omega o h w).clock=o.clock+2*N+
      (oldTerminalRoot i m price width d u omega o h w).clock :=by
  have hs:=root_exists i m price width d u omega o h w
  refine ⟨hs.2.1,hs.2.2.1,?_,rfl,?_⟩
  · simp only [currentParent,RegisterPopulationOwnerClockTransport.parentView,hs.2.2.2,
      RegisterPopulationOwnerClockTransport.ownerView,List.flatMap_cons,List.flatMap_nil,ite_true,List.append_nil]
  · simp only [currentParent,RegisterPopulationOwnerClockTransport.parentView,hs.2.2.2,
      RegisterPopulationOwnerClockTransport.root,ne_eq,not_true_eq_false,and_false,ite_false]

theorem current_same_founder :
    (RegisterTimestampedBirthSource.lineage i m).SameObject (currentParent i m price width d u omega o h w)
      (RegisterFaultDynamicProbeClocked.postClocked i m omega o) :=
  (current_parent_source i m price width d u omega o h w).2.2.1.trans
    (RegisterFaultDynamicProbeClocked.actual_post_identity i m omega o).symm

abbrev Base (N B : ℕ) := RegisterFaultDynamicProbeParentDiscovery.Sample N B
abbrev Words := ℕ→List RegisterTimestampedBirthSource.Event

/-- Actual native source conditional on the ACTUAL current root and THIS AST.
Fresh native primitives are generated by the unchanged original word law. -/
def continuationKernel (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (B : ℕ) :
    Kernel (Base N B) Words where
  toFun:=fun z=>
    let parent:=currentParent i m price width d u z.1.1 o h z.1.2
    let p:=returnedAST i (classify price width d u (sourceData m width z.1.1))
    RegisterFaultInfiniteRecord.wordPathLaw i noise m epsilon he (astPolicy p)
      ⟨0,parent.organism.physical,parent.organism⟩
  measurable':=measurable_of_finite _
instance continuationKernel_markov (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (B : ℕ) :
    IsMarkovKernel (continuationKernel (N:=N) i m price width d u o h noise epsilon he B) :=
  ⟨fun _=>by dsimp [continuationKernel];infer_instance⟩

/-- Full finite base, ALL measurements, then its actual parent's native tail.
The law is not a product with an unrelated initial-state witness. -/
def jointLaw (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (B : ℕ) :
    Measure (Base N B×Words) :=
  RegisterFaultDynamicProbeParentDiscovery.jointLaw noise epsilon he confuser N B ⊗ₘ
    continuationKernel (N:=N) i m price width d u o h noise epsilon he B
instance jointLaw_probability (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (B : ℕ) :
    IsProbabilityMeasure (jointLaw (N:=N) i m price width d u o h noise epsilon he confuser B) :=by
  unfold jointLaw
  infer_instance

theorem finite_marginal (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (B : ℕ) :
    (jointLaw (N:=N) i m price width d u o h noise epsilon he confuser B).fst=
      RegisterFaultDynamicProbeParentDiscovery.jointLaw noise epsilon he confuser N B :=Measure.fst_compProd _ _

/-- Clocked records start with the actual root's stored CURRENT clock. The
new native local time0 does not erase that real source timestamp. -/
def nativeRecords {B : ℕ} (z : Base N B×Words) : ℕ→ClockedRecord n :=
  RegisterFaultDynamicProbeClocked.recordAt i m
    (currentParent i m price width d u z.1.1.1 o h z.1.1.2) z.2

@[fun_prop] theorem measurable_nativeRecords {B : ℕ} :
    Measurable (nativeRecords (N:=N) (B:=B) i m price width d u o h) :=by
  apply measurable_from_prod_countable_right
  intro z
  simpa only [nativeRecords] using RegisterFaultDynamicProbeClocked.measurable_records i m
    (currentParent i m price width d u z.1.1 o h z.1.2)

/-- The finite wallet records retain every one of the original writes and
None slots. Marked observations are then paid at their declared tariff. -/
def finiteRecords {B : ℕ} (z : Base N B) : List (Option (ClockedRecord n)) :=
  RegisterPopulationFiniteEpisodeResource.wholeTrace i m price width d u z.1.1 o
    (RegisterFaultDynamicProbeParentDiscovery.plan h z.1.2)
def switchTime (B : ℕ) : ℕ :=2*N+3+B

def finiteBill {B : ℕ} (r : NNReal) (z : Base N B) : ℕ→ℝ :=fullCost
  (finiteRecords i m price width d u o h z) B r

def tailInflow (K : ℕ) (g : ℝ) (t : ℕ) : ℝ :=if K≤t then g else 0
def tailFee (K : ℕ) (rs : ℕ→ClockedRecord n) (t : ℕ) : ℝ :=if K≤t then (rs (t-K)).expenditure else 0

def wholeCost {B : ℕ} (r : NNReal) (z : Base N B×Words) (t : ℕ) : ℝ :=
  finiteBill i m price width d u o h r z.1 t+
    tailFee (switchTime (N:=N) B) (nativeRecords i m price width d u o h z) t

def remaining {B : ℕ} (reserve : ℝ) (r : NNReal) (z : Base N B) : ℝ :=
  cumulativeResourceBalance reserve (fun _=>0) (finiteBill i m price width d u o h r z) (switchTime (N:=N) B)

private theorem step_cost_bounds (i : Fin n) (m : Mechanism) (o : ClockedOrganism n)
    (a : Action) (mode label : Bool) :
    0≤(RegisterTimestampedBirthSource.step i m o a mode label).expenditure ∧
      (RegisterTimestampedBirthSource.step i m o a mode label).expenditure≤ m.writeCost :=by
  cases mode <;> cases a <;>
    simp [RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,cost,m.writeCost.coe_nonneg]

theorem native_fee_bounds {B : ℕ} (z : Base N B×Words) (t : ℕ) :
    0≤(nativeRecords i m price width d u o h z t).expenditure ∧
      (nativeRecords i m price width d u o h z t).expenditure≤ m.writeCost :=
  step_cost_bounds i m _ _ _ _

theorem actual_remaining_nonnegative {B : ℕ} (r : NNReal) (cap reserve : ℝ)
    (hc : (m.writeCost : ℝ)≤cap)
    (hr : ((2*N+3 : ℕ) : ℝ)*cap+(B : ℝ)*r≤reserve) (z : Base N B) :
    0≤remaining i m price width d u o h reserve r z :=
  complete_finite_wallet i m price width d u z.1.1 o h z.1.2 B r cap reserve hc hr _

/-- One continuous ledger: no tail supply in the finite experiment; g arrives
BEFORE each genuine native tail transaction. It starts with the SAME R. -/
theorem whole_p6 {B : ℕ} (r : NNReal) (cap reserve g : ℝ)
    (hc : (m.writeCost : ℝ)≤cap) (hg : cap≤g)
    (hr : ((2*N+3 : ℕ) : ℝ)*cap+(B : ℝ)*r≤reserve) (z : Base N B×Words) :
    ResourceViable reserve (tailInflow (switchTime (N:=N) B) g)
      (wholeCost i m price width d u o h r z) :=by
  have hb:=complete_finite_wallet i m price width d u z.1.1.1 o h z.1.1.2 B r cap reserve hc hr
  have ht : ResourceViable 0 (tailInflow (switchTime (N:=N) B) g)
      (tailFee (switchTime (N:=N) B) (nativeRecords i m price width d u o h z)) :=by
    apply resourceViable_of_pointwise_cost_le_replenish _ _ _ le_rfl
    intro t
    by_cases hK : switchTime (N:=N) B≤t
    · simp only [tailFee,tailInflow,hK,ite_true]
      exact ((native_fee_bounds i m price width d u o h z _).2.trans hc).trans hg
    · simp only [tailFee,tailInflow,hK,ite_false,le_refl]
  rw [resourceViable_iff_cumulative_cost_le] at hb ht ⊢
  intro K
  have hbK:=hb K
  have htK:=ht K
  simp only [Finset.sum_const_zero,add_zero] at hbK
  simp only [zero_add] at htK
  simp only [wholeCost,Finset.sum_add_distrib]
  exact (add_le_add hbK htK).trans_eq (by rfl)

theorem whole_prepay {B : ℕ} (r : NNReal) (cap reserve g : ℝ)
    (hc : (m.writeCost : ℝ)≤cap) (hg : cap≤g)
    (hr : ((2*N+3 : ℕ) : ℝ)*cap+(B : ℝ)*r≤reserve) (z : Base N B×Words) (t : ℕ) :
    wholeCost i m price width d u o h r z t≤
      cumulativeResourceBalance reserve (tailInflow (switchTime (N:=N) B) g)
        (wholeCost i m price width d u o h r z) t+tailInflow (switchTime (N:=N) B) g t :=by
  have hv:=(resourceViable_iff_cumulative_cost_le _ _ _).mp
    (whole_p6 i m price width d u o h r cap reserve g hc hg hr z) (t+1)
  simp only [Finset.sum_range_succ] at hv
  simp only [cumulativeResourceBalance]
  linarith

/-- No fresh bank account or reserve replacement at the boundary: the native
phase begins with exactly the actual unspent finite wallet. -/
theorem actual_balance_at_switch {B : ℕ} (reserve g : ℝ) (r : NNReal) (z : Base N B×Words) :
    cumulativeResourceBalance reserve (tailInflow (switchTime (N:=N) B) g)
      (wholeCost i m price width d u o h r z) (switchTime (N:=N) B)=
      remaining i m price width d u o h reserve r z.1 :=by
  simp only [remaining,cumulativeResourceBalance,wholeCost]
  have hz : ∑t∈Finset.range (switchTime (N:=N) B),tailInflow (switchTime (N:=N) B) g t=0 :=by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [tailInflow,not_le.mpr (Finset.mem_range.mp ht),ite_false]
  have hc : ∑t∈Finset.range (switchTime (N:=N) B),
      tailFee (switchTime (N:=N) B) (nativeRecords i m price width d u o h z) t=0 :=by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [tailFee,not_le.mpr (Finset.mem_range.mp ht),ite_false]
  simp only [Finset.sum_add_distrib,hz,hc,add_zero,Finset.sum_const_zero]

/-- ALL original finite inputs and native failures remain; P6 does not charge
another statistical risk event or condition on discovery/repair success. -/
theorem same_joint_p6 (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (B : ℕ)
    (r : NNReal) (cap reserve g : ℝ) (hc : (m.writeCost : ℝ)≤cap) (hg : cap≤g)
    (hr : ((2*N+3 : ℕ) : ℝ)*cap+(B : ℝ)*r≤reserve) :
    ∀ᵐ z ∂jointLaw (N:=N) i m price width d u o h noise epsilon he confuser B,
      ResourceViable reserve (tailInflow (switchTime (N:=N) B) g) (wholeCost i m price width d u o h r z) ∧
      ∀t,wholeCost i m price width d u o h r z t≤
        cumulativeResourceBalance reserve (tailInflow (switchTime (N:=N) B) g)
          (wholeCost i m price width d u o h r z) t+tailInflow (switchTime (N:=N) B) g t :=by
  exact ae_of_all _ (fun z=>⟨whole_p6 i m price width d u o h r cap reserve g hc hg hr z,
    whole_prepay i m price width d u o h r cap reserve g hc hg hr z⟩)

/-- Exact ANY-AST native erasure at THIS actual episode terminal root. -/
theorem conditional_native_erasure (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    {B : ℕ} (z : Base N B) :
    (continuationKernel (N:=N) i m price width d u o h noise epsilon he B z).map
      (fun words t=>RegisterTimestampedBirthSource.eraseRecord
        (nativeRecords i m price width d u o h (z,words) t))=
      RegisterFaultInfiniteRecord.recordPathLaw i noise m epsilon he
        (astPolicy (returnedAST i (classify price width d u (sourceData m width z.1.1))))
        ⟨0,(currentParent i m price width d u z.1.1 o h z.1.2).organism.physical,
          (currentParent i m price width d u z.1.1 o h z.1.2).organism⟩ :=by
  change (RegisterFaultInfiniteRecord.wordPathLaw i noise m epsilon he _ _).map _=_
  unfold RegisterFaultInfiniteRecord.recordPathLaw
  congr 1
  funext words t
  exact RegisterFaultDynamicProbeClocked.actual_record_erases i m _ _ words t

open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis UEOT.V3.ViabilityKernel
open RegisterFaultSource RegisterInstructionHomeostasis
local instance : Fintype (RepairOrganizationState (State n) Action Bool) :=repairOrganizationStateFintype
local instance : MeasurableSpace (RepairOrganizationState (State n) Action Bool) :=⊤
local instance : MeasurableSingletonClass (RepairOrganizationState (State n) Action Bool) :=⟨fun _=>trivial⟩

/-- Generic actual-source P5 carrier entry at the CURRENT state, including
bad states. The original same-tick marginal theorem supplies every time. -/
private theorem native_carrier (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (p : Instruction n) (hc : restorationCheck i m.goal p=true)
    (parent : Organism n) (hp : parent.program=m.goal) :
    ∀ᵐ rs ∂ RegisterFaultInfiniteRecord.recordPathLaw i noise m epsilon he (astPolicy p)
      ⟨0,parent.physical,parent⟩,
      ∀t : ℕ,RegisterFaultNativeOrganization.readRecord i (rs t)∈
        (RegisterFaultNativeOrganization.system i m epsilon he).carrier :=by
  have hs : StaysIn (PMF.pure (RegisterFaultNativeOrganization.organization i m parent.physical))
      (RegisterFaultNativeOrganization.system i m epsilon he).carrier :=by
    intro s hs
    have heq : s=RegisterFaultNativeOrganization.organization i m parent.physical:=by simpa using hs
    rw [heq]
    exact (carrier_iff_program i m.goal _).mpr rfl
  have hstay:=homeostaticMarginal_staysIn (RegisterFaultNativeOrganization.system i m epsilon he).mixedKernel
    (PMF.pure (RegisterFaultNativeOrganization.organization i m parent.physical)) _ hs
    (fun _ h=>(RegisterFaultNativeOrganization.system i m epsilon he).mixed_stays_carrier h)
  apply ae_all_iff.mpr
  intro t
  have horg : ∀ᵐ s ∂(homeostaticMarginal (RegisterFaultNativeOrganization.system i m epsilon he).mixedKernel
      (PMF.pure (RegisterFaultNativeOrganization.organization i m parent.physical)) t).toMeasure,
      s∈(RegisterFaultNativeOrganization.system i m epsilon he).carrier :=by
    rw [ae_iff,PMF.toMeasure_apply_eq_zero_iff _ ((Set.toFinite _).measurableSet)]
    exact Set.disjoint_left.mpr (fun s hsupport hbad=>hbad (hstay t hsupport))
  rw [←RegisterFaultNativeOrganization.actual_organization_marginal i noise m epsilon he p hc parent hp t] at horg
  exact ae_of_ae_map ((RegisterFaultNativeOrganization.measurable_readRecord i).comp
    (measurable_pi_apply t)).aemeasurable horg

/-- P5 and P12 concern these ACTUAL native records, with full owner and clock
metadata retained. Organizational reconstruction is exact for the actual
parent organism; identity is supplied by the real source, never Bool history. -/
def NativeFacts (epsilon : NNReal) (he : epsilon≤1) (parent : ClockedOrganism n)
    (rs : ℕ→ClockedRecord n) : Prop :=
  (fun t=>RegisterTimestampedBirthSource.eraseRecord (rs t))∈
    RegisterFaultDynamicProbeNativeHomeostasis.frequency i epsilon ∧
  ∀t : ℕ,RegisterFaultNativeOrganization.readRecord i (RegisterTimestampedBirthSource.eraseRecord (rs t))∈
      (RegisterFaultNativeOrganization.system i m epsilon he).carrier ∧
    RegisterFaultDynamicProbeLifecycle.parentView parent.organism.history
      (RegisterFaultNativeOrganization.readRecord i (RegisterTimestampedBirthSource.eraseRecord (rs t)))=
        (rs t).parentBefore.organism ∧
    (rs t).parentBefore.identity=parent.identity ∧ (rs t).parentAfter.identity=parent.identity ∧
    (rs t).parentBefore.clock=parent.clock+t ∧ (rs t).parentAfter.clock=parent.clock+t+1

private theorem measurable_NativeFacts (epsilon : NNReal) (he : epsilon≤1) (parent : ClockedOrganism n) :
    MeasurableSet {rs | NativeFacts i m epsilon he parent rs} :=by
  unfold NativeFacts
  rw [Set.ofPred_and]
  apply MeasurableSet.inter
  · exact (RegisterFaultDynamicProbeNativeHomeostasis.measurable_frequency i epsilon).preimage
      (measurable_pi_lambda _ (fun t=>(show Measurable RegisterTimestampedBirthSource.eraseRecord from
        fun _ _=>trivial).comp (measurable_pi_apply t)))
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun t=>(show MeasurableSet {r : ClockedRecord n |
      RegisterFaultNativeOrganization.readRecord i (RegisterTimestampedBirthSource.eraseRecord r)∈
        (RegisterFaultNativeOrganization.system i m epsilon he).carrier ∧
      RegisterFaultDynamicProbeLifecycle.parentView parent.organism.history
        (RegisterFaultNativeOrganization.readRecord i (RegisterTimestampedBirthSource.eraseRecord r))=r.parentBefore.organism ∧
      r.parentBefore.identity=parent.identity ∧ r.parentAfter.identity=parent.identity ∧
      r.parentBefore.clock=parent.clock+t ∧ r.parentAfter.clock=parent.clock+t+1} from trivial).preimage
        (measurable_pi_apply t)

/-- No physical target seed is assumed: the actual current root is used by
BOTH the source kernel and these original P5/P12/life consumers. -/
theorem conditional_native_facts (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    {B : ℕ} (z : Base N B) (ho : o.organism.program=m.goal) (b : Bool)
    (hs : classify price width d u (sourceData m width z.1.1)=.repair b) :
    ∀ᵐ words ∂continuationKernel (N:=N) i m price width d u o h noise epsilon he B z,
      NativeFacts i m epsilon he (currentParent i m price width d u z.1.1 o h z.1.2)
        (nativeRecords i m price width d u o h (z,words)) :=by
  let parent:=currentParent i m price width d u z.1.1 o h z.1.2
  let p:=returnedAST i (classify price width d u (sourceData m width z.1.1))
  have hp : parent.organism.program=m.goal:=
    (current_parent_source i m price width d u z.1.1 o h z.1.2).1.trans ho
  have hc : restorationCheck i m.goal p=true:=accepted_repair_restores i m price width d u z.1.1 b hs
  have hfreq:=RegisterFaultDynamicProbeNativeHomeostasis.native_frequency i noise m epsilon he p hc parent.organism hp
  have hcarrier:=native_carrier i m noise epsilon he p hc parent.organism hp
  have hparent:=RegisterFaultNativeOrganization.native_parent_reconstructed i noise m epsilon he p parent.organism
  have hf:=hfreq.and (hcarrier.and hparent)
  rw [RegisterFaultInfiniteRecord.recordPathLaw] at hf
  have hw:=ae_of_ae_map (RegisterFaultInfiniteRecord.measurable_recordStream i m (astPolicy p)
    ⟨0,parent.organism.physical,parent.organism⟩).aemeasurable hf
  filter_upwards [hw,RegisterFaultDynamicProbeClocked.actual_native_clock i noise m epsilon he p parent] with words hw ht
  have hepath : (fun t=>RegisterTimestampedBirthSource.eraseRecord
      (nativeRecords i m price width d u o h (z,words) t))=
      (fun t=>RegisterFaultInfiniteRecord.recordAt i m (astPolicy p)
        ⟨0,parent.organism.physical,parent.organism⟩ words t) :=by
    funext t
    exact RegisterFaultDynamicProbeClocked.actual_record_erases i m p parent words t
  refine ⟨?_,fun t=>?_⟩
  · rw [hepath]
    exact hw.1
  · have hid:=RegisterFaultDynamicProbeClocked.actual_native_parent_id i m parent words t
    have hcar:=hw.2.1 t
    have hrec:=hw.2.2 t
    have he:=congrFun hepath t
    rw [←he] at hcar hrec
    exact ⟨hcar,hrec,hid.1,hid.2,(ht t).1,(ht t).2⟩

private theorem measurable_finite_base_predicate {B : ℕ} (P : Base N B×Words→Prop)
    (hP : ∀z,MeasurableSet {words | P (z,words)}) : MeasurableSet {z | P z} :=by
  have heq : {z | P z}=⋃b : Base N B,({b}×ˢ{words | P (b,words)}) :=by
    ext z
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun b=>(measurableSet_singleton b).prod (hP b)

/-- Conditional actual-source facts are joined to the FULL finite base; no
success/acceptance conditioning or discarded fault word is used. -/
theorem same_joint_native_facts (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (B : ℕ)
    (ho : o.organism.program=m.goal) :
    ∀ᵐ z ∂jointLaw (N:=N) i m price width d u o h noise epsilon he confuser B,
      ∀b : Bool,classify price width d u (sourceData m width z.1.1.1)=.repair b→
        NativeFacts i m epsilon he (currentParent i m price width d u z.1.1.1 o h z.1.1.2)
          (nativeRecords i m price width d u o h z) :=by
  apply Measure.ae_compProd_of_ae_ae
  · apply measurable_finite_base_predicate
    intro z
    have heq : {words | ∀b : Bool,classify price width d u (sourceData m width z.1.1)=.repair b→
        NativeFacts i m epsilon he (currentParent i m price width d u z.1.1 o h z.1.2)
          (nativeRecords i m price width d u o h (z,words))}=
      ⋂b : Bool,{words | classify price width d u (sourceData m width z.1.1)=.repair b→
        NativeFacts i m epsilon he (currentParent i m price width d u z.1.1 o h z.1.2)
          (nativeRecords i m price width d u o h (z,words))} :=by ext words;simp
    rw [heq]
    apply MeasurableSet.iInter
    intro b
    by_cases hs : classify price width d u (sourceData m width z.1.1)=.repair b
    · simp only [hs,true_implies]
      change MeasurableSet (RegisterFaultDynamicProbeClocked.recordAt i m
        (currentParent i m price width d u z.1.1 o h z.1.2) ⁻¹'
        {rs | NativeFacts i m epsilon he (currentParent i m price width d u z.1.1 o h z.1.2) rs})
      exact (measurable_NativeFacts i m epsilon he _).preimage
        (RegisterFaultDynamicProbeClocked.measurable_records i m _)
    · simp only [hs,false_implies,Set.ofPred_true,MeasurableSet.univ]
  · exact ae_of_all _ (fun z=>by
      apply ae_all_iff.mpr
      intro b
      by_cases hs : classify price width d u (sourceData m width z.1.1)=.repair b
      · exact (conditional_native_facts i m price width d u o h noise epsilon he z ho b hs).mono (fun _ hh _=>hh)
      · exact ae_of_all _ (fun _ hh=>False.elim (hs hh)))

/-- Actual native parents are the SAME owner as the real first-birth actor.
P8 remains tied to that actual child; a missing child is not manufactured. -/
theorem native_same_birth_parent (epsilon : NNReal) (he : epsilon≤1) {B : ℕ}
    (z : Base N B×Words)
    (hf : NativeFacts i m epsilon he (currentParent i m price width d u z.1.1.1 o h z.1.1.2)
      (nativeRecords i m price width d u o h z))
    (child : ClockedOrganism n)
    (hc : RegisterPopulationOwnerClockTransport.childAt i m.writeCost (o.clock+2*N)
      [some (RegisterFaultDynamicProbeClocked.postClocked i m z.1.1.1 o)]
      (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u z.1.1.1 o.organism h z.1.1.2)
      (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u z.1.1.1 o.organism h z.1.1.2 0)=some child) :
    let founder:=RegisterFaultDynamicProbeClocked.postClocked i m z.1.1.1 o
    let actor:={founder with clock:=o.clock+2*N+1}
    (RegisterTimestampedBirthSource.lineage i m).SameObject
      (currentParent i m price width d u z.1.1.1 o h z.1.1.2) actor ∧
    ∀t,(RegisterTimestampedBirthSource.lineage i m).SameObject
      (nativeRecords i m price width d u o h z t).parentBefore actor :=by
  have hb:=first_birth_same_founder i m price width d u z.1.1.1 o h z.1.1.2 child hc
  have hs:=(current_same_founder i m price width d u z.1.1.1 o h z.1.1.2).trans hb.2.1.symm
  exact ⟨hs,fun t=>((hf.2 t).2.2.1).trans hs⟩

/-- ONE source supplies viable resources, actual current-parent P5/P12 and
positive recurrent life for accepted repair. Its finite marginal remains the
old full experiment, including no-birth and wrong-observation outcomes. -/
theorem same_joint_current_lifecycle (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (B : ℕ)
    (r : NNReal) (cap reserve g : ℝ) (hc : (m.writeCost : ℝ)≤cap) (hg : cap≤g)
    (hr : ((2*N+3 : ℕ) : ℝ)*cap+(B : ℝ)*r≤reserve) (ho : o.organism.program=m.goal) :
    ∀ᵐ z ∂ jointLaw (N:=N) i m price width d u o h noise epsilon he confuser B,
      ResourceViable reserve (tailInflow (switchTime (N:=N) B) g) (wholeCost i m price width d u o h r z) ∧
      (∀t,wholeCost i m price width d u o h r z t≤
        cumulativeResourceBalance reserve (tailInflow (switchTime (N:=N) B) g)
          (wholeCost i m price width d u o h r z) t+tailInflow (switchTime (N:=N) B) g t) ∧
      ∀b : Bool,classify price width d u (sourceData m width z.1.1.1)=.repair b→
        NativeFacts i m epsilon he (currentParent i m price width d u z.1.1.1 o h z.1.1.2)
          (nativeRecords i m price width d u o h z) ∧ epsilon<1 ∧
        ∀K : ℕ,∃t≥K,Legitimate i
          (RegisterTimestampedBirthSource.eraseRecord (nativeRecords i m price width d u o h z t)).transaction.parentAfter :=by
  have hb:=same_source_repair_non_total_ae (N:=N) m price width d u noise epsilon he confuser B
  rw [←finite_marginal (N:=N) i m price width d u o h noise epsilon he confuser B] at hb
  have hn:=ae_of_ae_map measurable_fst.aemeasurable hb
  filter_upwards [same_joint_p6 (N:=N) i m price width d u o h noise epsilon he confuser B r cap reserve g hc hg hr,
    same_joint_native_facts (N:=N) i m price width d u o h noise epsilon he confuser B ho,hn] with z hw hf hn
  refine ⟨hw.1,hw.2,fun b hs=>?_⟩
  have hl:=hf b hs
  exact ⟨hl,hn b hs,RegisterFaultDynamicProbeNativeHomeostasis.frequency_returns i epsilon (hn b hs) _ hl.1⟩

/-- The actual h1 episode is exactly the original frozen old-cohort protocol,
not the repeated-root h0 schedule. No cohort-success condition is assumed. -/
theorem actual_h1_episode :
    RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism true w=
      RegisterFaultDynamicProbeHistoryPrice.requests i m price width d u omega o.organism w :=by
  rw [RegisterFaultDynamicProbeHistoryPrice.requests_actual_ast]
  rfl

open UEOT.V3.EvolutionPrice
open RegisterPopulationOwnerClockTransport

/-- The SAME p/q retain their original synthesis at the actual current seed;
only the declared retained-parent evaluation origin advances to that state. -/
theorem current_returned_pair (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1) (ho : o.organism.program=m.goal)
    (hgood : omega∈Good noise m epsilon he N width (u : ℝ))
    (ha : classify price width d u (sourceData m width omega)≠.unknown) :
    let parent:=(currentParent i m price width d u omega o h w).organism
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    let q:=returnedProgram i p
    let M:=RegisterFaultControlModel.model i noise m (priceValue price hp) epsilon he (d : ℝ) (by exact_mod_cast hd)
    synthesize i p=some q ∧ IsBellmanGODSelector M (interpret p) ∧
      actualValue i noise m epsilon he (priceValue price hp) (d : ℝ) parent p=M.optimalValue parent.physical ∧
      actualValue (0 : Fin 1) noise m epsilon he (priceValue price hp) (d : ℝ)
        (projectOrganism i parent) q=M.optimalValue parent.physical :=by
  dsimp only
  have hs:=RegisterFaultDynamicProbeInfinite.returned_synthesis i (classify price width d u (sourceData m width omega))
  have hg:=(RegisterFaultDynamicProbeInfinite.actual_good_returned_program i noise m epsilon he price width d u
    hp hw hd omega o.organism ho hgood ha).2.1
  have hparent:=(current_parent_source i m price width d u omega o h w).1.trans ho
  have hv:=RegisterInstructionGODScale.actual_god_value i noise m (priceValue price hp) epsilon he (d : ℝ)
    (by exact_mod_cast hd) _ hparent _ hg
  exact ⟨hs,hg,hv,(actual_value_transport i noise m epsilon he (priceValue price hp) (d : ℝ) _ _ _ hs).symm.trans hv⟩

private theorem writeCost_after {k : ℕ} (rs : List (Option (ClockedRecord n))) (hk : rs.length≤k) :
    RegisterPopulationFiniteEpisodeResource.costStream rs k=0 :=by
  simp only [RegisterPopulationFiniteEpisodeResource.costStream,RegisterPopulationFundedProtocol.recordAt,
    List.getElem?_eq_none hk,Option.join_none,RegisterPopulationFundedProtocol.fee]

theorem finite_records_length {B : ℕ} (z : Base N B) :
    (finiteRecords i m price width d u o h z).length=2*N+3 :=by
  simp only [finiteRecords,RegisterPopulationFiniteEpisodeResource.wholeTrace_length,
    RegisterFaultDynamicProbeParentDiscovery.plan,List.length_cons,List.length_nil]

theorem finite_bill_after {B : ℕ} (r : NNReal) (z : Base N B) (t : ℕ)
    (ht : switchTime (N:=N) B≤t) : finiteBill i m price width d u o h r z t=0 :=by
  have hlen:=finite_records_length i m price width d u o h z
  have hwrite : (finiteRecords i m price width d u o h z).length≤t:=by
    rw [hlen]
    unfold switchTime at ht
    omega
  unfold finiteBill fullCost
  rw [writeCost_after _ hwrite,zero_add]
  simp only [readCost,hlen]
  have hh : ¬(2*N+3≤t ∧ t<2*N+3+B):=by unfold switchTime at ht;omega
  exact if_neg hh

theorem actual_tail_cost {B : ℕ} (r : NNReal) (z : Base N B×Words) (t : ℕ) :
    wholeCost i m price width d u o h r z (switchTime (N:=N) B+t)=
      (nativeRecords i m price width d u o h z t).expenditure :=by
  unfold wholeCost
  rw [finite_bill_after i m price width d u o h r z.1 _ (Nat.le_add_right _ _),zero_add]
  simp only [tailFee,Nat.le_add_right,ite_true,Nat.add_sub_cancel_left]

/-- The amount carried into native execution is R minus the literal complete
write bill and ALL marked reads, not R minus a worst-case bound or a reset. -/
theorem actual_remaining_bill {B : ℕ} (reserve : ℝ) (r : NNReal) (z : Base N B) :
    remaining i m price width d u o h reserve r z=
      reserve-((finiteRecords i m price width d u o h z).map RegisterPopulationFundedProtocol.fee).sum-
        RegisterFaultDynamicProbeParentDiscovery.readCharge r B :=by
  have hlen:=finite_records_length i m price width d u o h z
  have hsum : (∑k∈Finset.range ((finiteRecords i m price width d u o h z).length+B),
      RegisterPopulationFiniteEpisodeResource.costStream (finiteRecords i m price width d u o h z) k)=
      ((finiteRecords i m price width d u o h z).map RegisterPopulationFundedProtocol.fee).sum :=by
    rw [Finset.sum_range_add]
    have hz : (∑k∈Finset.range B,RegisterPopulationFiniteEpisodeResource.costStream
        (finiteRecords i m price width d u o h z) ((finiteRecords i m price width d u o h z).length+k))=0 :=by
      apply Finset.sum_eq_zero
      intro k _
      exact writeCost_after _ (Nat.le_add_right _ _)
    rw [hz,add_zero,RegisterPopulationFiniteEpisodeResource.costStream_total]
  unfold remaining cumulativeResourceBalance finiteBill fullCost
  rw [show switchTime (N:=N) B=(finiteRecords i m price width d u o h z).length+B by rw [hlen];rfl]
  simp only [Finset.sum_const_zero,add_zero,Finset.sum_add_distrib]
  rw [hsum,read_total_exact,RegisterFaultDynamicProbeParentDiscovery.readCharge_exact]
  ring

/- The following minimal actual-cohort proofs reuse root's checked
/tmp/ueot-common-actual-price-role.lean; root is an author contributor. -/
theorem actual_cohort_serial :
    RegisterPopulationOwnerClockTransport.SerialStore
      (RegisterFaultDynamicProbeHistoryPrice.afterFirst i m price width d u omega o.organism w) :=by
  let s:=RegisterFaultDynamicProbePopulation.registeredParent i m omega o.organism
  let p:=returnedAST i (classify price width d u (sourceData m width omega))
  change RegisterPopulationOwnerClockTransport.SerialStore
    (RegisterOwnProgramPopulation.run i m.writeCost s [RegisterFaultDynamicProbePopulation.astRequest p s 0 (w 0).1 (w 0).2])
  exact RegisterPopulationOwnerClockTransport.serial_own_run i m.writeCost s
    (RegisterPopulationOwnerClockTransport.serial_single_founder _) _

/-- Actual owner-depth Price at this SAME episode, conditional only on the
actual old-cohort birth count; first birth is excluded from that count. -/
theorem actual_episode_price
    (hB : 0<RegisterPopulationTypePrice.birthCount i m
      (RegisterFaultDynamicProbeHistoryPrice.afterFirst i m price width d u omega o.organism w)
      (RegisterFaultDynamicProbePopulation.cohortActions (returnedAST i (classify price width d u (sourceData m width omega)))
        (RegisterFaultDynamicProbeHistoryPrice.afterFirst i m price width d u omega o.organism w))
      (RegisterFaultDynamicProbeHistoryPrice.modes w) (RegisterFaultDynamicProbeHistoryPrice.labels w)) :
    let s:=RegisterFaultDynamicProbeHistoryPrice.afterFirst i m price width d u omega o.organism w
    let a:=RegisterFaultDynamicProbePopulation.cohortActions (returnedAST i (classify price width d u (sourceData m width omega))) s
    let modes:=RegisterFaultDynamicProbeHistoryPrice.modes w
    let labels:=RegisterFaultDynamicProbeHistoryPrice.labels w
    RegisterPopulationOwnerClockTransport.actualViewedMean i m o.identity (o.clock+2*N) s a modes labels-
      weightedMean (RegisterPopulationTypePrice.frequency s)
        (RegisterPopulationOwnerClockTransport.viewedParentDepth o.identity (o.clock+2*N) s)=
      weightedCov (RegisterPopulationTypePrice.frequency s)
        (RegisterPopulationTypePrice.fertility i m s a modes labels)
        (RegisterPopulationOwnerClockTransport.viewedParentDepth o.identity (o.clock+2*N) s)/
        weightedMean (RegisterPopulationTypePrice.frequency s)
          (RegisterPopulationTypePrice.fertility i m s a modes labels)+1 :=by
  dsimp only
  rw [RegisterPopulationOwnerClockTransport.actual_registered_price i m o.identity (o.clock+2*N) _
    (actual_cohort_serial i m price width d u omega o w) _ _ _ hB,
    RegisterPopulationOwnerClockTransport.actual_transmission_one i m o.identity (o.clock+2*N) _
      (actual_cohort_serial i m price width d u omega o w) _ _ _ hB]


/-- Actual old-cohort Price on the data-returned h1 episode. B0 has no
normalization witness and remains an empty-generation outcome. -/
def ActualCohortPrice (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : ClockedOrganism n) (w : Fin 3→Bool×Bool) : Prop :=
    let s:=RegisterFaultDynamicProbeHistoryPrice.afterFirst i m price width d u omega o.organism w
    let a:=RegisterFaultDynamicProbePopulation.cohortActions (returnedAST i (classify price width d u (sourceData m width omega))) s
    let modes:=RegisterFaultDynamicProbeHistoryPrice.modes w
    let labels:=RegisterFaultDynamicProbeHistoryPrice.labels w
    ∀_hB : 0<RegisterPopulationTypePrice.birthCount i m s a modes labels,
    RegisterPopulationOwnerClockTransport.actualViewedMean i m o.identity (o.clock+2*N) s a modes labels-
      weightedMean (RegisterPopulationTypePrice.frequency s)
        (RegisterPopulationOwnerClockTransport.viewedParentDepth o.identity (o.clock+2*N) s)=
      weightedCov (RegisterPopulationTypePrice.frequency s)
        (RegisterPopulationTypePrice.fertility i m s a modes labels)
        (RegisterPopulationOwnerClockTransport.viewedParentDepth o.identity (o.clock+2*N) s)/
        weightedMean (RegisterPopulationTypePrice.frequency s)
          (RegisterPopulationTypePrice.fertility i m s a modes labels)+1

theorem actual_cohort_price : ActualCohortPrice i m price width d u omega o w :=by
  intro hB
  exact actual_episode_price i m price width d u omega o w hB

/-- The finite h1 Price role and actual current-root continuation/resource
roles are consumed on ONE joint source. No unrelated cohort is substituted. -/
theorem same_joint_p6_native_price (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (B : ℕ)
    (r : NNReal) (cap reserve g : ℝ) (hc : (m.writeCost : ℝ)≤cap) (hg : cap≤g)
    (hr : ((2*N+3 : ℕ) : ℝ)*cap+(B : ℝ)*r≤reserve) (ho : o.organism.program=m.goal) :
    ∀ᵐ z ∂ jointLaw (N:=N) i m price width d u o true noise epsilon he confuser B,
      ResourceViable reserve (tailInflow (switchTime (N:=N) B) g)
        (wholeCost i m price width d u o true r z) ∧
      (∀t,wholeCost i m price width d u o true r z t≤
        cumulativeResourceBalance reserve (tailInflow (switchTime (N:=N) B) g)
          (wholeCost i m price width d u o true r z) t+tailInflow (switchTime (N:=N) B) g t) ∧
      (∀b : Bool,classify price width d u (sourceData m width z.1.1.1)=.repair b→
        NativeFacts i m epsilon he (currentParent i m price width d u z.1.1.1 o true z.1.1.2)
          (nativeRecords i m price width d u o true z) ∧ epsilon<1 ∧
        ∀K : ℕ,∃t≥K,Legitimate i
          (RegisterTimestampedBirthSource.eraseRecord (nativeRecords i m price width d u o true z t)).transaction.parentAfter) ∧
      ActualCohortPrice i m price width d u z.1.1.1 o z.1.1.2 :=by
  filter_upwards [same_joint_current_lifecycle (N:=N) i m price width d u o true noise epsilon he confuser B
    r cap reserve g hc hg hr ho] with z hz
  exact ⟨hz.1,hz.2.1,hz.2.2,actual_cohort_price i m price width d u z.1.1.1 o z.1.1.2⟩

/-- Native continuation adds no new calibration/read error budget: the base
marginal is EXACT. This remains an unconditional two-event bound, not a birth
success probability and not a conditional-on-acceptance guarantee. -/
theorem full_source_two_event_bound (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (B : ℕ)
    (hN : 0<N) (hu : 0≤(u : ℝ)) (e : Fin 3) :
    let bad : Set (Base N B):={z |
      z.1.1∉Good noise m epsilon he N width (u : ℝ) ∨
      RegisterFaultDynamicProbeParentDiscovery.estimate
        (RegisterFaultDynamicProbeParentDiscovery.targetSensed i m price width d u z.1.1 o.organism h z.1.2 e z.2)≠
      RegisterPopulationOwnerClockTransport.actualParent i m.writeCost (o.clock+2*N)
        [some (RegisterFaultDynamicProbeClocked.postClocked i m z.1.1 o)]
        (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u z.1.1 o.organism h z.1.2)
        (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u z.1.1 o.organism h z.1.2 e)}
    (jointLaw (N:=N) i m price width d u o h noise epsilon he confuser B).real (Prod.fst ⁻¹' bad)≤
      min 1 (4*Real.exp (-2*(N : ℝ)*(u : ℝ)^2))+Real.exp (-(B : ℝ)/8) :=by
  dsimp only
  rw [Measure.real,←Measure.fst_apply ((Set.toFinite _).measurableSet),finite_marginal]
  exact same_source_two_event_bound i m price width d u o h e noise epsilon he confuser hN hu B

/-- The returned q executes on the SAME fresh native word source at the
actual current parent's coarse initial configuration. This is the original
full p/q law, without choosing a different policy or resetting the seed. -/
theorem conditional_returned_word_source (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    {B : ℕ} (z : Base N B) :
    let parent:=(currentParent i m price width d u z.1.1 o h z.1.2).organism
    let p:=returnedAST i (classify price width d u (sourceData m width z.1.1))
    let q:=returnedProgram i p
    continuationKernel (N:=N) i m price width d u o h noise epsilon he B z=
      RegisterFaultInfiniteRecord.wordPathLaw (0 : Fin 1) noise m epsilon he (astPolicy q)
        (projectASTConfig i p q ⟨0,parent.physical,parent⟩) :=by
  dsimp only
  exact actual_wordPathLaw i noise m epsilon he _ _
    (RegisterFaultDynamicProbeInfinite.returned_synthesis i (classify price width d u (sourceData m width z.1.1))) _

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationCurrentParentContinuation
