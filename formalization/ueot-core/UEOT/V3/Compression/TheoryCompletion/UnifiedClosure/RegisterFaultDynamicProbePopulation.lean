import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeLifecycle
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterActuatorPopulationScale
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingBodyReturns

/-!
Original promise: THIS data-returned program must execute actual births with real provenance and census inputs.
Existing source: same Batch/postProbeParent/AST, and separate serial population allocator/own-code interpreter/TypePrice.
Reduced premise: derive actual lookup execution equality with the original compiler and actual fresh-child identities from THIS AST, rather than substituting another program.
Family: original finite registers/Option Bool/fault/fees, explicit serial registration of the unchanged post-probe parent at slot0, fixed dispatch plan[0,1]; failures/invalid slots remain None.
Consumers: original own-program population, actual fresh IDs/parent pairs/inherited code, own P5 and source-derived first-cohort TypePrice; idle on a damaged parent is a strict birth boundary.

This is an explicitly registered FINITE population continuation protocol, not
an assertion that its second dispatch (to the child) is the old fixed-parent
native infinite deployment. Physical state, original Bool history/protected
program and all previous2N probe records/fees are retained. Existing serial
founder-ID registration is an additional metadata permission, not learned from
Batch or a reset of those physical/program coordinates. New source IDs and
old Bool journals are distinct coordinates; their equality is not assumed.
The external AST is not installed or copied: births copy original Bool code;
its compiled execution is proved equal to THIS selected repair AST.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbePopulation
open Set MeasureTheory ProbabilityTheory
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultJointRecord RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite
open RegisterFaultDynamicProbe RegisterFaultDynamicProbeLifecycle
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open RegisterPopulationHistorySource (Store Request)
noncomputable section
local instance {n : ℕ} : MeasurableSpace (List (Option (ClockedRecord n))) := ⊤

/-- Existing founder registration around the ACTUAL terminal training parent.
No physical write or new protected program is executed by this map. -/
def registeredParent {n N : ℕ} (i : Fin n) (m : Mechanism)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) : Store n:=
  RegisterPopulationHistorySource.founders [postProbeParent i m omega o]

/-- THIS literal AST reads only the actually addressed parent's physical state.
Fresh fault/label values are stored in the source request, not read by action. -/
def astRequest {n : ℕ} (p : Instruction n) (s : Store n) (j : ℕ) (mode label : Bool) : Request:=
  ⟨j,match RegisterPopulationHistorySource.lookup s j with
    | none=>none | some node=>interpret p node.organism.physical,mode,label⟩

/-- Real interpreter on real stores. Every request reuses original own-code
transaction/allocator, and an invalid address still appends the original None. -/
def astEpisode {n : ℕ} (p : Instruction n) (i : Fin n) (fee : NNReal) :
    Store n→List (ℕ×Bool×Bool)→List Request
  | _,[]=>[]
  | s,(j,mode,label)::es=>
    let q:=astRequest p s j mode label
    q::astEpisode p i fee (RegisterOwnProgramPopulation.next i fee s q) es

def plan (w : Fin 2→Bool×Bool) : List (ℕ×Bool×Bool):=
  [(0,(w 0).1,(w 0).2),(1,(w 1).1,(w 1).2)]

def episode {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (w : Fin 2→Bool×Bool) : List Request:=
  astEpisode (returnedAST i (classify price width d u (sourceData m width omega))) i m.writeCost
    (registeredParent i m omega o) (plan w)

/-- No outcome is filtered, including missing-child dispatch at the second tick. -/
def trace {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (w : Fin 2→Bool×Bool) : List (Option (ClockedRecord n)):=
  RegisterActuatorPopulationScale.transactionTrace i m.writeCost (registeredParent i m omega o)
    (episode i m price width d u omega o w)

@[simp] theorem astEpisode_length {n : ℕ} (p : Instruction n) (i : Fin n) (fee : NNReal)
    (s : Store n) (es : List (ℕ×Bool×Bool)) : (astEpisode p i fee s es).length=es.length :=by
  induction es generalizing s with
  | nil=>rfl
  | cons e es ih=>rcases e with ⟨j,mode,label⟩;simp only [astEpisode,List.length_cons,ih]

@[simp] theorem episode_length {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (w : Fin 2→Bool×Bool) :
    (episode i m price width d u omega o w).length=2 :=by simp [episode,plan]

/-- Derive old own-Bool execution from THIS selected AST at an actual lookup.
No external desired execution/repair implementation certificate is supplied. -/
theorem selected_request_eq_compiled {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (b : Bool)
    (hs : classify price width d u (sourceData m width omega)=.repair b)
    (s : Store n) (j : ℕ) (mode label : Bool)
    (hcode : ∀node,RegisterPopulationHistorySource.lookup s j=some node→node.organism.program=m.goal) :
    astRequest (returnedAST i (classify price width d u (sourceData m width omega))) s j mode label=
      RegisterOwnProgramPopulation.compiledRequest i s j mode label :=by
  have hb:=accepted_repair_bit m price width d u omega b hs
  cases hp : RegisterPopulationHistorySource.lookup s j with
  | none=>simp [astRequest,RegisterOwnProgramPopulation.compiledRequest,hp]
  | some node=>simp only [astRequest,RegisterOwnProgramPopulation.compiledRequest,hp,hs,returnedAST,hb,hcode node hp];rfl

@[simp] theorem registered_length {n N : ℕ} (i : Fin n) (m : Mechanism)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) : (registeredParent i m omega o).length=1 :=by
  simp [registeredParent]

@[simp] theorem registered_lookup {n N : ℕ} (i : Fin n) (m : Mechanism)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) :
    RegisterPopulationHistorySource.lookup (registeredParent i m omega o) 0=
      some ⟨postProbeParent i m omega o,[(0,false)],0⟩ :=rfl

/-- First actual population transaction erases to the SAME old literal step
from the actual post-parent, with the ACTUAL computed AST, for ALL outputs. -/
theorem actual_first_erasure {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal) (mode label : Bool) :
    let parent:=postProbeParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    let s:=registeredParent i m omega o
    (RegisterOwnProgramPopulation.transaction i m.writeCost s (astRequest p s 0 mode label)).map
      RegisterTimestampedBirthSource.eraseRecord=
        some (modeRecordStep i m parent (interpret p parent.physical) mode label) :=by
  dsimp only
  have h:=RegisterOwnProgramPopulation.transaction_erasure i m.writeCost
    (registeredParent i m omega o)
    (astRequest (returnedAST i (classify price width d u (sourceData m width omega))) (registeredParent i m omega o) 0 mode label)
    ⟨postProbeParent i m omega o,[(0,false)],0⟩ (registered_lookup i m omega o)
  simpa only [astRequest,registered_lookup,postProbeParent_program,ho] using h

/-- Source entry: a real first child supplies its fresh ID, true parent slot,
and the copied Bool's compiler is literally THIS returned AST. -/
theorem actual_first_child_source {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal)
    (b : Bool) (hs : classify price width d u (sourceData m width omega)=.repair b)
    (mode label : Bool) (child : ClockedOrganism n)
    (hd : RegisterOwnProgramPopulation.child i m.writeCost (registeredParent i m omega o)
      (astRequest (returnedAST i (classify price width d u (sourceData m width omega))) (registeredParent i m omega o) 0 mode label)=some child) :
    RegisterOwnProgramPopulation.childID i m.writeCost (registeredParent i m omega o)
      (astRequest (returnedAST i (classify price width d u (sourceData m width omega))) (registeredParent i m omega o) 0 mode label)=some 1 ∧
    RegisterOwnProgramPopulation.parentID i m.writeCost (registeredParent i m omega o)
      (astRequest (returnedAST i (classify price width d u (sourceData m width omega))) (registeredParent i m omega o) 0 mode label)=some 0 ∧
    child.organism.program=m.goal ∧
    compile i child.organism.program=returnedAST i (classify price width d u (sourceData m width omega)) :=by
  have hsrc:=RegisterOwnProgramPopulation.actual_child_source i m.writeCost _ _ child hd
  obtain ⟨parent,hlookup,hstep,hprogram,hlt⟩:=hsrc
  have heq : parent=⟨postProbeParent i m omega o,[(0,false)],0⟩:=by simpa only [astRequest,registered_lookup,Option.some.injEq] using hlookup.symm
  have hc : child.organism.program=m.goal:=by rw [hprogram,heq];exact (postProbeParent_program i m omega o).trans ho
  have hID:=(RegisterOwnProgramPopulation.actual_child_fresh i m.writeCost _ _ child hd).1
  refine ⟨?_,?_,hc,?_⟩
  · simpa only [registered_length] using hID
  · simp only [RegisterOwnProgramPopulation.parentID,RegisterPopulationHistorySource.parentID]
    change (RegisterOwnProgramPopulation.child i m.writeCost _ _).map (fun _=>(0 : ℕ))=some 0
    rw [hd];rfl
  · rw [hc,hs,returnedAST,accepted_repair_bit m price width d u omega b hs]

/-- An actually available matching-code parent really produces a child under
repair mode of THIS computed repair AST, from any physical damage. -/
theorem actual_selected_normal_birth {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (b : Bool)
    (hs : classify price width d u (sourceData m width omega)=.repair b)
    (s : Store n) (j : ℕ) (node : ClockedOrganism n)
    (hp : RegisterPopulationHistorySource.lookup s j=some node) (hc : node.organism.program=m.goal) (label : Bool) :
    ∃child,RegisterOwnProgramPopulation.child i m.writeCost s
      (astRequest (returnedAST i (classify price width d u (sourceData m width omega))) s j true label)=some child :=by
  have hcheck:=accepted_repair_restores i m price width d u omega b hs
  have hx : update i node.organism.physical
      (interpret (returnedAST i (classify price width d u (sourceData m width omega))) node.organism.physical) i=node.organism.program :=by
    rw [hc]
    exact (RegisterInstructionRecoveryScale.restorationCheck_iff _ _ _).mp hcheck _
  cases hd : RegisterOwnProgramPopulation.child i m.writeCost s
      (astRequest (returnedAST i (classify price width d u (sourceData m width omega))) s j true label) with
  | none=>simp [RegisterOwnProgramPopulation.child,RegisterPopulationHistorySource.child,
      RegisterPopulationHistorySource.transaction,astRequest,hp,RegisterTimestampedBirthSource.step,
      modeRecordStep,RegisterJointRecord.recordStep,hx] at hd
  | some child=>exact ⟨child,rfl⟩

/-- Matching-code fact at the second actual lookup comes from the real first
birth (or lookup is None); it is not another input code/parent certificate. -/
theorem actual_second_lookup_code {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal)
    (b : Bool) (hs : classify price width d u (sourceData m width omega)=.repair b)
    (mode label : Bool) (node : ClockedOrganism n) :
    let s:=registeredParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    RegisterPopulationHistorySource.lookup
      (RegisterOwnProgramPopulation.next i m.writeCost s (astRequest p s 0 mode label)) 1=some node →
      node.organism.program=m.goal :=by
  dsimp only
  intro hlookup
  have heq:=RegisterOwnProgramPopulation.next_new_slot i m.writeCost (registeredParent i m omega o)
    (astRequest (returnedAST i (classify price width d u (sourceData m width omega))) (registeredParent i m omega o) 0 mode label)
  simp only [registered_length] at heq
  have hd:=heq.symm.trans hlookup
  exact (actual_first_child_source i m price width d u omega o ho b hs mode label node hd).2.2.1

/-- The TWO real AST dispatches are literally the existing own-code compiled
episode, after deriving each successful lookup's code from actual source.
Faults, failed births and a missing child dispatch are included in this equality. -/
theorem actual_episode_eq_compiled {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal)
    (b : Bool) (hs : classify price width d u (sourceData m width omega)=.repair b)
    (w : Fin 2→Bool×Bool) : episode i m price width d u omega o w=
      RegisterActuatorPopulationScale.compiledEpisode i m.writeCost (registeredParent i m omega o) (plan w) :=by
  have hcode0 : ∀node,RegisterPopulationHistorySource.lookup (registeredParent i m omega o) 0=some node→node.organism.program=m.goal :=by
    intro node hp
    have heq : node=⟨postProbeParent i m omega o,[(0,false)],0⟩:=by simpa only [registered_lookup,Option.some.injEq] using hp.symm
    rw [heq]
    exact (postProbeParent_program i m omega o).trans ho
  have h0:=selected_request_eq_compiled i m price width d u omega b hs (registeredParent i m omega o) 0 (w 0).1 (w 0).2 hcode0
  have h1:=selected_request_eq_compiled i m price width d u omega b hs
    (RegisterOwnProgramPopulation.next i m.writeCost (registeredParent i m omega o)
      (astRequest (returnedAST i (classify price width d u (sourceData m width omega))) (registeredParent i m omega o) 0 (w 0).1 (w 0).2))
    1 (w 1).1 (w 1).2 (actual_second_lookup_code i m price width d u omega o ho b hs _ _)
  simp only [episode,plan,astEpisode,RegisterActuatorPopulationScale.compiledEpisode]
  simp only [h0] at h1 ⊢
  rw [h1]

/-- A real successful source word yields a genuinely born parent then its
own child. All fresh IDs/parent pairs are computed by the old allocator. -/
theorem actual_two_generation_births {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal)
    (b : Bool) (hs : classify price width d u (sourceData m width omega)=.repair b)
    (label0 label1 : Bool) :
    let s:=registeredParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    let q0:=astRequest p s 0 true label0
    let s1:=RegisterOwnProgramPopulation.next i m.writeCost s q0
    let q1:=astRequest p s1 1 true label1
    ∃c1 c2,RegisterOwnProgramPopulation.child i m.writeCost s q0=some c1 ∧
      RegisterPopulationHistorySource.lookup s1 1=some c1 ∧
      RegisterOwnProgramPopulation.child i m.writeCost s1 q1=some c2 ∧
      RegisterOwnProgramPopulation.childID i m.writeCost s q0=some 1 ∧
      RegisterOwnProgramPopulation.parentID i m.writeCost s q0=some 0 ∧
      RegisterOwnProgramPopulation.childID i m.writeCost s1 q1=some 2 ∧
      RegisterOwnProgramPopulation.parentID i m.writeCost s1 q1=some 1 ∧
      compile i c1.organism.program=p ∧ compile i c2.organism.program=p :=by
  dsimp only
  let s:=registeredParent i m omega o
  let p:=returnedAST i (classify price width d u (sourceData m width omega))
  let q0:=astRequest p s 0 true label0
  let s1:=RegisterOwnProgramPopulation.next i m.writeCost s q0
  let q1:=astRequest p s1 1 true label1
  obtain ⟨c1,hc1⟩:=actual_selected_normal_birth i m price width d u omega b hs s 0
    ⟨postProbeParent i m omega o,[(0,false)],0⟩ (registered_lookup i m omega o)
    ((postProbeParent_program i m omega o).trans ho) label0
  have hfirst:=actual_first_child_source i m price width d u omega o ho b hs true label0 c1 hc1
  have hlookup : RegisterPopulationHistorySource.lookup s1 1=some c1 :=by
    have h:=RegisterOwnProgramPopulation.next_new_slot i m.writeCost s q0
    simpa only [s,registered_length] using h.trans hc1
  obtain ⟨c2,hc2⟩:=actual_selected_normal_birth i m price width d u omega b hs s1 1 c1 hlookup hfirst.2.2.1 label1
  obtain ⟨node,hn,hstep,hprogram,hlt⟩:=RegisterOwnProgramPopulation.actual_child_source i m.writeCost s1 q1 c2 hc2
  have heq : node=c1:=by simpa only [q1,astRequest,hlookup,Option.some.injEq] using hn.symm
  have hc2program : c2.organism.program=m.goal:=hprogram.trans (heq ▸ hfirst.2.2.1)
  have hID2:=(RegisterOwnProgramPopulation.actual_child_fresh i m.writeCost s1 q1 c2 hc2).1
  have hlen : s1.length=2:=by simp only [s1,RegisterOwnProgramPopulation.next_length,s,registered_length]
  refine ⟨c1,c2,hc1,hlookup,hc2,hfirst.1,hfirst.2.1,?_,?_,hfirst.2.2.2,?_⟩
  · simpa only [hlen] using hID2
  · simp only [RegisterOwnProgramPopulation.parentID,RegisterPopulationHistorySource.parentID]
    change (RegisterOwnProgramPopulation.child i m.writeCost s1 q1).map (fun _=>(1 : ℕ))=some 1
    rw [hc2];rfl
  · rw [hc2program,hs,returnedAST,accepted_repair_bit m price width d u omega b hs]

/-- Full original calibration batch and two independent original primitive
future draws. This is a NEW explicitly fixed finite dispatch protocol, with
unchanged training marginal; neither success nor acceptance is selected out. -/
def inputLaw (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) :
    Measure ((Coordinate N→Bool×Bool)×(Fin 2→Bool×Bool)):=
  (rawLaw noise epsilon he N).prod (RegisterRotatingBodySource.roundLaw 2 noise epsilon he)
instance inputLaw_probability (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) :
    IsProbabilityMeasure (inputLaw noise epsilon he N):=by unfold inputLaw;infer_instance

theorem inputLaw_training_marginal (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) :
    (inputLaw noise epsilon he N).fst=rawLaw noise epsilon he N:=Measure.fst_prod

/-- Complete measurable population record law. The old Batch remains the
only input of the selector; source fault/label values feed actual transactions. -/
def recordLaw {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) :
    Measure (List (Option (ClockedRecord n))):=
  (inputLaw noise epsilon he N).map (fun z=>trace i m price width d u z.1 o z.2)

instance recordLaw_probability {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) :
    IsProbabilityMeasure (recordLaw (N:=N) i noise m epsilon he price width d u o):=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- Both real child events in the specified [0,1] dispatch protocol. -/
def TwoBorn {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (w : Fin 2→Bool×Bool) : Prop:=
  let s:=registeredParent i m omega o
  let p:=returnedAST i (classify price width d u (sourceData m width omega))
  let q0:=astRequest p s 0 (w 0).1 (w 0).2
  let s1:=RegisterOwnProgramPopulation.next i m.writeCost s q0
  let q1:=astRequest p s1 1 (w 1).1 (w 1).2
  (RegisterOwnProgramPopulation.child i m.writeCost s q0).isSome ∧
    (RegisterOwnProgramPopulation.child i m.writeCost s1 q1).isSome

/-- Positive genuine source mass, not a chosen infinite success word. Every
all-repair two-draw outcome (ALL labels) produces the actual two generations. -/
theorem actual_two_generation_mass_lower {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal)
    (b : Bool) (hs : classify price width d u (sourceData m width omega)=.repair b) :
    RegisterRotatingBodyReturns.successMass 2 epsilon≤
      RegisterRotatingBodySource.roundLaw 2 noise epsilon he {w | TwoBorn i m price width d u omega o w} :=by
  rw [←RegisterRotatingBodyReturns.good_mass 2 noise epsilon he]
  apply measure_mono
  intro w hw
  have h:=actual_two_generation_births i m price width d u omega o ho b hs (w 0).2 (w 1).2
  obtain ⟨c1,c2,hc1,hlookup,hc2,_⟩:=h
  dsimp [TwoBorn]
  rw [hw 0,hw 1,hc1,hc2]
  exact ⟨rfl,rfl⟩

/-- Actual data-returned actions for a FROZEN old-address cohort, not source
truth or a substituted compiler program. For the first registered single
parent it is exactly the first real dispatch of the population experiment. -/
def cohortActions {n : ℕ} (p : Instruction n) (s : Store n) (j : ℕ) : Action:=
  (astRequest p s j true false).action

/-- A real repair-mode birth makes the first actual cohort nonempty. This
source fact supplies Price's normalization permission, rather than hB input. -/
theorem actual_first_cohort_count {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal)
    (b : Bool) (hs : classify price width d u (sourceData m width omega)=.repair b) :
    RegisterPopulationTypePrice.birthCount i m (registeredParent i m omega o)
      (cohortActions (returnedAST i (classify price width d u (sourceData m width omega))) (registeredParent i m omega o))
      (fun _=>true) (fun _=>false)=1 :=by
  let s:=registeredParent i m omega o
  let p:=returnedAST i (classify price width d u (sourceData m width omega))
  let q:=astRequest p s 0 true false
  obtain ⟨child,hchild⟩:=actual_selected_normal_birth i m price width d u omega b hs s 0
    ⟨postProbeParent i m omega o,[(0,false)],0⟩ (registered_lookup i m omega o)
    ((postProbeParent_program i m omega o).trans ho) false
  have hmechanism : RegisterOwnProgramPopulation.mechanism m.writeCost s q=m :=by
    have h:=RegisterOwnProgramPopulation.mechanism_eq m.writeCost s q
      ⟨postProbeParent i m omega o,[(0,false)],0⟩ (registered_lookup i m omega o)
    simpa only [postProbeParent_program,ho] using h
  have hfixed : RegisterPopulationHistorySource.child i m s q=some child :=by
    change RegisterOwnProgramPopulation.child i m.writeCost s q=some child at hchild
    unfold RegisterOwnProgramPopulation.child at hchild
    rw [hmechanism] at hchild
    exact hchild
  have hborn : ∀j : Fin s.length,RegisterPopulationTypePrice.born i m s (cohortActions p s) (fun _=>true) (fun _=>false) j :=by
    intro j
    have hj : (j : ℕ)=0:=by have hh:=j.isLt;change j.val<1 at hh;omega
    change (RegisterPopulationTypePrice.offspring i m s (cohortActions p s) (fun _=>true) (fun _=>false) j).isSome=true
    simpa only [RegisterPopulationTypePrice.offspring,RegisterPopulationTypePrice.before,hj,
      List.take_zero,RegisterPopulationHistorySource.run,List.foldl_nil,RegisterPopulationTypePrice.request,cohortActions,q,astRequest,Option.isSome_some] using
        congrArg Option.isSome hfixed
  change Fintype.card {j : Fin s.length // RegisterPopulationTypePrice.born i m s
    (cohortActions p s) (fun _=>true) (fun _=>false) j}=1
  rw [Fintype.card_subtype]
  simp only [hborn,Finset.filter_true,Finset.card_univ,Fintype.card_fin]
  exact registered_length i m omega o

/-- ORIGINAL Core Price consumes actual p-driven first-cohort fertility and
actual inherited children. Constant one-parent trait gives no adaptation
claim; this is the minimal source entry, not a mixed-type selection theorem. -/
theorem actual_first_cohort_price {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal)
    (b : Bool) (hs : classify price width d u (sourceData m width omega)=.repair b) (z : Bool→ℝ) :
    let s:=registeredParent i m omega o
    let actions:=cohortActions (returnedAST i (classify price width d u (sourceData m width omega))) s
    RegisterPopulationTypePrice.empiricalOffspringMean i m s actions (fun _=>true) (fun _=>false) z-
      UEOT.V3.EvolutionPrice.weightedMean (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.parentTrait s z)=
    UEOT.V3.EvolutionPrice.weightedCov (RegisterPopulationTypePrice.frequency s)
      (RegisterPopulationTypePrice.fertility i m s actions (fun _=>true) (fun _=>false)) (RegisterPopulationTypePrice.parentTrait s z) /
    UEOT.V3.EvolutionPrice.weightedMean (RegisterPopulationTypePrice.frequency s)
      (RegisterPopulationTypePrice.fertility i m s actions (fun _=>true) (fun _=>false)) :=by
  apply RegisterPopulationTypePrice.actual_program_type_price
  rw [actual_first_cohort_count i m price width d u omega o ho b hs]
  norm_num

/-- First fault really gives no newborn; the planned child address is absent.
All classifier verdicts are included, rather than retrying a successful birth. -/
theorem actual_first_fault_none {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (label : Bool) :
    let s:=registeredParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    let q:=astRequest p s 0 false label
    RegisterOwnProgramPopulation.child i m.writeCost s q=none ∧
      RegisterPopulationHistorySource.lookup (RegisterOwnProgramPopulation.next i m.writeCost s q) 1=none :=by
  dsimp only
  have hchild : RegisterOwnProgramPopulation.child i m.writeCost (registeredParent i m omega o)
      (astRequest (returnedAST i (classify price width d u (sourceData m width omega))) (registeredParent i m omega o) 0 false label)=none :=by
    simp [RegisterOwnProgramPopulation.child,RegisterPopulationHistorySource.child,
      RegisterPopulationHistorySource.transaction,astRequest,registered_lookup,RegisterTimestampedBirthSource.step,modeRecordStep]
  refine ⟨hchild,?_⟩
  have h:=RegisterOwnProgramPopulation.next_new_slot i m.writeCost (registeredParent i m omega o)
    (astRequest (returnedAST i (classify price width d u (sourceData m width omega))) (registeredParent i m omega o) 0 false label)
  simpa only [registered_length] using h.trans hchild

/-- Strict selected-idle boundary on the actual damaged post-parent. Being an
optimal idle output cannot be used as a successful-birth/repair certificate. -/
theorem actual_idle_first_none {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal)
    (b : Bool) (hs : classify price width d u (sourceData m width omega)=.idle b)
    (hbad : (postProbeParent i m omega o).physical i≠m.goal) (mode label : Bool) :
    let s:=registeredParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    let q:=astRequest p s 0 mode label
    RegisterOwnProgramPopulation.child i m.writeCost s q=none ∧
      RegisterPopulationHistorySource.lookup (RegisterOwnProgramPopulation.next i m.writeCost s q) 1=none :=by
  dsimp only
  have hchild : RegisterOwnProgramPopulation.child i m.writeCost (registeredParent i m omega o)
      (astRequest (returnedAST i (classify price width d u (sourceData m width omega))) (registeredParent i m omega o) 0 mode label)=none :=by
    cases mode <;>
      simp [RegisterOwnProgramPopulation.child,RegisterPopulationHistorySource.child,
        RegisterPopulationHistorySource.transaction,astRequest,registered_lookup,hs,returnedAST,interpret,
        RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,update,
        postProbeParent_program,ho,hbad]
  refine ⟨hchild,?_⟩
  have h:=RegisterOwnProgramPopulation.next_new_slot i m.writeCost (registeredParent i m omega o)
    (astRequest (returnedAST i (classify price width d u (sourceData m width omega))) (registeredParent i m omega o) 0 mode label)
  simpa only [registered_length] using h.trans hchild

/-- Every source outcome has both chronological entries, including None. -/
theorem actual_trace_length {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (w : Fin 2→Bool×Bool) :
    (trace i m price width d u omega o w).length=2 :=by
  have h (s : Store n) (es : List Request) :
      (RegisterActuatorPopulationScale.transactionTrace i m.writeCost s es).length=es.length :=by
    induction es generalizing s with
    | nil=>rfl
    | cons q es ih=>simp only [RegisterActuatorPopulationScale.transactionTrace,List.length_cons,ih]
  exact (h _ _).trans (episode_length i m price width d u omega o w)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbePopulation
