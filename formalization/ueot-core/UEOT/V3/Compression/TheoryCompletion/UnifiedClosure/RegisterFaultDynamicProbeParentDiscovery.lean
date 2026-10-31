import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeHistoryPrice
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterOwnProgramJointJournal

/-!
Original promise: THIS finite population episode has source-derived discoverable birth parents.
Existing theorems: actual AST/serial births, actual child-journal functionality, and fixed-budget marked-read majority.
Reduced premise: derive the hidden target class from THIS third actual child and dispatch; never supply htruth or let the estimator call actualParent.
Registered family: same Batch/AST/single founder; plan [0,0,h] with hidden h=0/1; NEW independent noisy marked-owner-journal reads, eta=1/4, arbitrary confuser, all failures retained.
Consumers: original P12 and finite wrong-mark risk, actual episode ParentBridge, and explicit per-read budget. Mark permissions are not old Batch observations.

The source sensor can read a successful birth's owner edge in the actual serial
journal. This is an ADDITIONAL registered capability, not a derivation of owner
from a child ID or bare physical data. The estimator sees only the fixed three
mark classes and N noisy readings. It sees neither h nor the actual parent,
child, journal edge, raw flags, hazard or Good. None means NO BIRTH, not the
attempted actor. Read fees are an explicit external observation account; no
physical sensor or funding mechanism is invented. Consistency as N tends to infinity requires increasing read budget when per-read cost is positive. No reset, program change,
extra founder, successful-outcome conditioning or replacement sample occurs.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeParentDiscovery
open Set MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite RegisterFaultDynamicProbe
open RegisterFaultDynamicProbePopulation RegisterPopulationJournalLearning
open RegisterPopulationHistorySource (Store Request)
noncomputable section
local instance : MeasurableSpace RegisterPopulationJournalLearning.Observation := ⊤
local instance : MeasurableSingletonClass RegisterPopulationJournalLearning.Observation := ⟨fun _=>trivial⟩

abbrev Class := Fin 3
/-- The only executable output labels. No source-dependent directory is called. -/
def mark (j : Class) : RegisterPopulationJournalLearning.Observation := if j=0 then none else if j=1 then some 0 else some 1
/-- Hidden-source dispatch choice; never an input of estimate. -/
def address (h : Bool) : ℕ := if h then 1 else 0

def plan (h : Bool) (w : Fin 3→Bool×Bool) : List (ℕ×Bool×Bool) :=
  [(0,(w 0).1,(w 0).2),(0,(w 1).1,(w 1).2),(address h,(w 2).1,(w 2).2)]

def episode {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) : List Request :=
  astEpisode (returnedAST i (classify price width d u (sourceData m width omega))) i m.writeCost
    (registeredParent i m omega o) (plan h w)

@[simp] theorem episode_length {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) :
    (episode i m price width d u omega o h w).length=3 := by simp [episode,plan]

/-- Event index is the actual third transaction, including missing-slot ticks. -/
def third {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) :
    Fin (episode i m price width d u omega o h w).length := ⟨2,by simp⟩

theorem third_dispatch {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) :
    (RegisterPopulationHistorySource.requestAt (episode i m price width d u omega o h w)
      (third i m price width d u omega o h w)).parent=address h := by
  simp [episode,plan,astEpisode,third,RegisterPopulationHistorySource.requestAt,astRequest]

/-- Actual third birth object is computed by the original full serial source. -/
def actualChild {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) :=
  RegisterOwnProgramPopulation.childAt i m.writeCost (registeredParent i m omega o)
    (episode i m price width d u omega o h w) (third i m price width d u omega o h w)

def actualParent {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) : RegisterPopulationJournalLearning.Observation :=
  RegisterOwnProgramPopulation.actualParent i m.writeCost (registeredParent i m omega o)
    (episode i m price width d u omega o h w) (third i m price width d u omega o h w)

/-- The second possible owner is EXACTLY the original first newborn. The
second dispatch0 cannot install an unrelated object at old slot1. -/
theorem candidate_one_is_first_birth {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) :
    let s:=registeredParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    RegisterPopulationHistorySource.lookup
      (RegisterOwnProgramPopulation.storeBefore i m.writeCost s
        (episode i m price width d u omega o h w) 2) 1=
      RegisterOwnProgramPopulation.child i m.writeCost s (astRequest p s 0 (w 0).1 (w 0).2) := by
  dsimp only
  let s:=registeredParent i m omega o
  let p:=returnedAST i (classify price width d u (sourceData m width omega))
  let q0:=astRequest p s 0 (w 0).1 (w 0).2
  let s1:=RegisterOwnProgramPopulation.next i m.writeCost s q0
  let q1:=astRequest p s1 0 (w 1).1 (w 1).2
  have hl : 1<s1.length := by simp [s1,s]
  have hn:=RegisterOwnProgramPopulation.next_other_slot i m.writeCost s1 q1 1 hl (by change (0 : ℕ)≠1;decide)
  have hb:=RegisterOwnProgramPopulation.next_new_slot i m.writeCost s q0
  simp only [s,registered_length] at hb
  change RegisterPopulationHistorySource.lookup
    (RegisterOwnProgramPopulation.next i m.writeCost s1 q1) 1=_
  exact hn.trans hb

/-- Successful third ownership comes from an actual lookup and actual birth,
not merely the hidden address or the sensor class. -/
theorem actual_third_birth_source {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool)
    (child : RegisterTimestampedBirthSource.ClockedOrganism n)
    (hc : actualChild i m price width d u omega o h w=some child) :
    let s:=RegisterOwnProgramPopulation.storeBefore i m.writeCost (registeredParent i m omega o)
      (episode i m price width d u omega o h w) 2
    let q:=RegisterPopulationHistorySource.requestAt (episode i m price width d u omega o h w)
      (third i m price width d u omega o h w)
    ∃parent, RegisterPopulationHistorySource.lookup s (address h)=some parent ∧
      (RegisterFaultJointRecord.modeRecordStep i ⟨parent.organism.program,m.writeCost⟩
        parent.organism q.action q.mode q.label).transaction.child=some child.organism ∧
      child.organism.program=parent.organism.program := by
  obtain ⟨parent,hp,hstep,hcode,_⟩:=RegisterOwnProgramPopulation.actual_child_source i m.writeCost _ _ child hc
  refine ⟨parent,?_,hstep,hcode⟩
  have hd:=third_dispatch i m price width d u omega o h w
  change (RegisterPopulationHistorySource.requestAt (episode i m price width d u omega o h w) 2).parent=address h at hd
  simp only [third] at hp
  rw [hd] at hp
  exact hp

/-- Source interpreter target: no-birth class0, otherwise the actual dispatch.
It is computed by the sensor and never supplied to the estimator. -/
def truth {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) : Class :=
  match actualChild i m price width d u omega o h w with
  | none=>0 | some _=>if h then 2 else 1

/-- No external htruth: the real birth and real third dispatch determine mark. -/
theorem truth_is_actual_parent {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) :
    mark (truth i m price width d u omega o h w)=actualParent i m price width d u omega o h w := by
  unfold actualParent RegisterOwnProgramPopulation.actualParent
  rw [third_dispatch]
  change mark (truth i m price width d u omega o h w)=
    (actualChild i m price width d u omega o h w).map (fun _=>address h)
  cases hc : actualChild i m price width d u omega o h w with
  | none=>simp [truth,hc,mark]
  | some child=>cases h <;> simp [truth,hc,mark,address]

/-- Reuse the original source-proved child-ID/parent bridge for THIS full episode. -/
theorem actual_episode_parent_bridge {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) :
    ObjectClassParentBridge
      (RegisterOwnProgramJournalLearning.childJournalClass i m.writeCost (registeredParent i m omega o)
        (episode i m price width d u omega o h w))
      (RegisterOwnProgramPopulation.actualParent i m.writeCost (registeredParent i m omega o)
        (episode i m price width d u omega o h w)) :=
  RegisterOwnProgramJournalLearning.child_journal_parent_bridge _ _ _ _

/-- Fixed public table + all read data. Does NOT call actualParent. -/
def estimate {B : ℕ} (data : Data B) : RegisterPopulationJournalLearning.Observation :=
  mark (select (List.finRange 3) mark 0 data)

def sensed {n N B : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool)
    (reads : Raw Class B) : Data B := readout mark (truth i m price width d u omega o h w) reads

/-- Exact complete fixed-budget readout law of THIS actual birth journal.
The apparent truth parameter is computed from the real episode, not assumed. -/
theorem actual_readout_product {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool)
    (eta : NNReal) (he : eta≤1) (confuser : PMF Class) (B : ℕ) :
    (rawLaw eta he confuser B).map (sensed i m price width d u omega o h w)=
      VariableRegisteredSamples.productRowLaw
        (fun _ : Unit=>sensorLaw eta he confuser mark (truth i m price width d u omega o h w))
        (fun _=>B) :=
  observedLaw_product eta he confuser mark (truth i m price width d u omega o h w) B

@[simp] theorem estimate_zero (data : Data 0) : estimate data=none := by simp [estimate,mark]

/-- Failure and false-positive errors are in the same event; no conditioning. -/
theorem good_estimate_actual {n N B : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool)
    (reads : Raw Class B) (hg : reads∈Good (J:=Class) B) :
    estimate (sensed i m price width d u omega o h w reads)=actualParent i m price width d u omega o h w := by
  exact (good_selected_class (List.finRange 3) mark 0 _ (List.mem_finRange _) reads hg).trans
    (truth_is_actual_parent i m price width d u omega o h w)

private theorem quarter_le_one : (1/4 : NNReal)≤1 := by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)

abbrev EpisodeRaw (N : ℕ) := (Coordinate N→Bool×Bool)×(Fin 3→Bool×Bool)
abbrev Sample (N B : ℕ) := EpisodeRaw N × Raw Class B

/-- ALL original training and future outcomes times ALL registered reads.
The source hypotheses h=0/1 share this full primitive input law. -/
def jointLaw (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF Class) (N B : ℕ) : Measure (Sample N B) :=
  (RegisterFaultDynamicProbeHistoryPrice.experimentLaw noise epsilon he N).prod
    (rawLaw (1/4) quarter_le_one confuser B)
instance jointLaw_probability (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF Class) (N B : ℕ) : IsProbabilityMeasure (jointLaw noise epsilon he confuser N B) := by
  unfold jointLaw;infer_instance

theorem jointLaw_episode_marginal (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF Class) (N B : ℕ) :
    (jointLaw noise epsilon he confuser N B).fst=
      RegisterFaultDynamicProbeHistoryPrice.experimentLaw noise epsilon he N := Measure.fst_prod

theorem actual_joint_parent_risk_le {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n)
    (h : Bool) (confuser : PMF Class) (B : ℕ) :
    (jointLaw noise epsilon he confuser N B).real {z |
      estimate (sensed i m price width d u z.1.1 o h z.1.2 z.2)≠
        actualParent i m price width d u z.1.1 o h z.1.2}≤Real.exp (-(B : ℝ)/8) := by
  have hset : {z : Sample N B | z.2∉Good (J:=Class) B}=
      Set.univ×ˢ(Good (J:=Class) B)ᶜ := by ext z;simp
  calc
    _≤(jointLaw noise epsilon he confuser N B).real {z | z.2∉Good (J:=Class) B} := by
      apply measureReal_mono
      · intro z herr hg
        exact herr (good_estimate_actual i m price width d u z.1.1 o h z.1.2 z.2 hg)
      · exact measure_ne_top _ _
    _=(rawLaw (1/4) quarter_le_one confuser B).real (Good (J:=Class) B)ᶜ := by
      rw [Measure.real,jointLaw,hset,Measure.prod_prod,measure_univ,one_mul];rfl
    _≤Real.exp (-2*(B : ℝ)*gap (1/4)^2) :=
      bad_good_probability_le (1/4) quarter_le_one (by norm_num) confuser B
    _=_ := by congr 1;norm_num [gap];ring

/-- Uniform joint consistency includes every training/future outcome, even
when no offspring is born. It does not imply birth probability tends to one. -/
theorem actual_joint_parent_risk_tendsto_zero {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n)
    (h : Bool) (confuser : PMF Class) :
    Tendsto (fun B=>(jointLaw noise epsilon he confuser N B).real {z |
      estimate (sensed i m price width d u z.1.1 o h z.1.2 z.2)≠
        actualParent i m price width d u z.1.1 o h z.1.2}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _=>measureReal_nonneg)
    (actual_joint_parent_risk_le i noise m epsilon he price width d u o h confuser)
  have hlim:=(learningSchedule (1/4) (by norm_num)).failure_tendsto_zero
  convert hlim using 1
  ext B
  change Real.exp (-(B : ℝ)/8)=Real.exp (-2*(B : ℝ)*gap (1/4)^2)
  congr 1;norm_num [gap];ring

/-- The SAME executable mark estimator consumes original P12. The target
identity premise is proved by actual execution, not an htruth argument. -/
theorem actual_episode_p12 {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool)
    (confuser : PMF Class) :
    Tendsto (fun B=>(rawLaw (1/4) quarter_le_one confuser B).real {reads |
      estimate (sensed i m price width d u omega o h w reads)≠actualParent i m price width d u omega o h w})
      atTop (𝓝 0) := by
  let C:=eventContract (1/4) quarter_le_one (by norm_num) confuser
  let cls:=Setoid.ker mark
  let t:=truth i m price width d u omega o h w
  let choose:=fun B (reads : Raw Class B)=>select (List.finRange 3) mark 0 (readout mark t reads)
  let D:=objectClassDiscoveryContract_of_goodEvent C (fun _=>True) cls t choose trivial
    (fun _ _=>trivial) (fun _ reads hg=>good_selected_class (List.finRange 3) mark 0 t (List.mem_finRange t) reads hg)
  have bridge : ObjectClassParentBridge cls mark := ⟨fun _ _ hh=>hh⟩
  exact p12_discovered_parent_tendsto_lifecycleParent D mark bridge _
    (truth_is_actual_parent i m price width d u omega o h w)

/-- A target event is registered before the reads. This index does not reveal
its actual born parent; events0/1 have known actor0 but may have NO child. -/
def eventIndex {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3) :
    Fin (episode i m price width d u omega o h w).length := ⟨e,by rw [episode_length];exact e.isLt⟩

def targetChild {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3) :=
  RegisterOwnProgramPopulation.childAt i m.writeCost (registeredParent i m omega o)
    (episode i m price width d u omega o h w) (eventIndex i m price width d u omega o h w e)

def targetParent {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3) :=
  RegisterOwnProgramPopulation.actualParent i m.writeCost (registeredParent i m omega o)
    (episode i m price width d u omega o h w) (eventIndex i m price width d u omega o h w e)

theorem target_dispatch {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3) :
    (RegisterPopulationHistorySource.requestAt (episode i m price width d u omega o h w)
      (eventIndex i m price width d u omega o h w e)).parent=(if e.val<2 then 0 else address h) := by
  fin_cases e <;> simp [episode,plan,astEpisode,eventIndex,RegisterPopulationHistorySource.requestAt,astRequest]

def targetTruth {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3) : Class :=
  match targetChild i m price width d u omega o h w e with
  | none=>0 | some _=>if e.val<2 then 1 else if h then 2 else 1

/-- Every actual chosen event is covered, without a cohort-nonempty premise. -/
theorem target_truth_is_actual_parent {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3) :
    mark (targetTruth i m price width d u omega o h w e)=targetParent i m price width d u omega o h w e := by
  unfold targetParent RegisterOwnProgramPopulation.actualParent
  rw [target_dispatch]
  change mark (targetTruth i m price width d u omega o h w e)=
    (targetChild i m price width d u omega o h w e).map (fun _=>if e.val<2 then 0 else address h)
  cases hc : targetChild i m price width d u omega o h w e with
  | none=>simp [targetTruth,hc,mark]
  | some child=>by_cases he : e.val<2 <;> cases h <;> simp [targetTruth,hc,mark,address,he]

def targetSensed {n N B : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3)
    (reads : Raw Class B) : Data B := readout mark (targetTruth i m price width d u omega o h w e) reads

theorem good_target_estimate_actual {n N B : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3)
    (reads : Raw Class B) (hg : reads∈Good (J:=Class) B) :
    estimate (targetSensed i m price width d u omega o h w e reads)=targetParent i m price width d u omega o h w e :=
  (good_selected_class (List.finRange 3) mark 0 _ (List.mem_finRange _) reads hg).trans
    (target_truth_is_actual_parent i m price width d u omega o h w e)

/-- Single-target finite risk for ANY pre-registered event. Simultaneous reads
for several targets require their own budget/source registration. -/
theorem target_joint_parent_risk_le {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n)
    (h : Bool) (e : Fin 3) (confuser : PMF Class) (B : ℕ) :
    (jointLaw noise epsilon he confuser N B).real {z |
      estimate (targetSensed i m price width d u z.1.1 o h z.1.2 e z.2)≠
        targetParent i m price width d u z.1.1 o h z.1.2 e}≤Real.exp (-(B : ℝ)/8) := by
  have hset : {z : Sample N B | z.2∉Good (J:=Class) B}=
      Set.univ×ˢ(Good (J:=Class) B)ᶜ := by ext z;simp
  calc
    _≤(jointLaw noise epsilon he confuser N B).real {z | z.2∉Good (J:=Class) B} := by
      apply measureReal_mono
      · intro z herr hg
        exact herr (good_target_estimate_actual i m price width d u z.1.1 o h z.1.2 e z.2 hg)
      · exact measure_ne_top _ _
    _=(rawLaw (1/4) quarter_le_one confuser B).real (Good (J:=Class) B)ᶜ := by
      rw [Measure.real,jointLaw,hset,Measure.prod_prod,measure_univ,one_mul];rfl
    _≤Real.exp (-2*(B : ℝ)*gap (1/4)^2) :=
      bad_good_probability_le (1/4) quarter_le_one (by norm_num) confuser B
    _=_ := by congr 1;norm_num [gap];ring

/-- Original P12 with source-derived truth for any actual selected event. -/
theorem target_episode_p12 {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3)
    (confuser : PMF Class) :
    Tendsto (fun B=>(rawLaw (1/4) quarter_le_one confuser B).real {reads |
      estimate (targetSensed i m price width d u omega o h w e reads)≠targetParent i m price width d u omega o h w e})
      atTop (𝓝 0) := by
  let C:=eventContract (1/4) quarter_le_one (by norm_num) confuser
  let cls:=Setoid.ker mark
  let t:=targetTruth i m price width d u omega o h w e
  let choose:=fun B (reads : Raw Class B)=>select (List.finRange 3) mark 0 (readout mark t reads)
  let D:=objectClassDiscoveryContract_of_goodEvent C (fun _=>True) cls t choose trivial
    (fun _ _=>trivial) (fun _ reads hg=>good_selected_class (List.finRange 3) mark 0 t (List.mem_finRange t) reads hg)
  have bridge : ObjectClassParentBridge cls mark := ⟨fun _ _ hh=>hh⟩
  exact p12_discovered_parent_tendsto_lifecycleParent D mark bridge _
    (target_truth_is_actual_parent i m price width d u omega o h w e)

/-- Declared read account, separate from all original transaction fees. Every
fixed-budget read is charged, including failed/no-child observations. -/
def readCharge (r : NNReal) (B : ℕ) : ℝ := ∑ _j : Fin B, (r : ℝ)
@[simp] theorem readCharge_exact (r : NNReal) (B : ℕ) : readCharge r B=(B : ℝ)*r := by simp [readCharge]
theorem fixed_read_budget (r : NNReal) (B : ℕ) (budget : ℝ) (hf : (B : ℝ)*r≤budget) :
    readCharge r B≤budget := by simpa using hf

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeParentDiscovery
