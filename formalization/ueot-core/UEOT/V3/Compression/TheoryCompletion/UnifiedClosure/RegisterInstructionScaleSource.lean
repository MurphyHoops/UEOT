import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterActuatorScaleSource

/-!
Original promise: C4/P9 program/semantic transport must follow actual mechanism execution.
Existing premises: actuator projection handles compiled Bool programs; arbitrary literal controllers still require an external coarse factor.
Reduced premise: an executable syntax check returns the SAME coarse Instruction; successful checking derives interpretation, validity and complete transaction transport.
Family: all emits and nested branches testing only the retained actuator; hidden-address tests give a strict same-source failure of exact factorization.
Consumers: original RepairProgramValid, P9 transport_object_property, and actual fault/birth/fee records under every finite primitive word/law.

This is a conservative static access check, not a complete semantic decision
procedure: even an unreachable hidden-register branch is rejected. Instruction
is the existing external controller syntax choosing the old Option Bool action;
checking does not install/reset the retained Bool repair program, add an action,
or permit hidden observations. Cost remains the original write cost, and faults,
failures, parent histories and inherited child Bool programs are retained.
The carrier is the registered active-bit target b. Preservation validity is not
full return/recovery, all six P9 predicates, merging owners or Wilsonian RG.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionScaleSource
open MeasureTheory
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultJointRecord RegisterActuatorScaleSource

/-- A literal computable projection rejects every hidden-register test. -/
def check {n : ℕ} (i : Fin n) : Instruction n → Option (Instruction 1)
  | .emit a => some (.emit a)
  | .test j b yes no =>
    if j=i then do
      let yes' ← check i yes
      let no' ← check i no
      pure (.test 0 b yes' no')
    else none

/-- The graph of the actual checker, not a desired execution certificate. -/
abbrev Checked {n : ℕ} (i : Fin n) :=
  {pq : Instruction n × Instruction 1 // check i pq.1=some pq.2}

def certify {n : ℕ} (i : Fin n) (p : Instruction n) : Option (Checked i) :=
  match h : check i p with
  | none => none
  | some q => some ⟨(p,q),h⟩

/-- Checking is sound for the exact returned program on EVERY physical state. -/
theorem check_interpret {n : ℕ} (i : Fin n) (p : Instruction n) (q : Instruction 1)
    (hc : check i p=some q) (x : State n) :
    interpret q (projectState i x)=interpret p x := by
  induction p generalizing q with
  | emit a =>
    simp only [check,Option.some.injEq] at hc
    subst q
    rfl
  | test j b yes no hy hn =>
    by_cases hj : j=i
    · subst j
      cases hyes : check i yes with
      | none => simp [check,hyes] at hc
      | some y =>
        cases hno : check i no with
        | none => simp [check,hyes,hno] at hc
        | some z =>
          simp [check,hyes,hno] at hc
          subst q
          by_cases hxb : x i=b <;> simp [interpret,projectState,hxb,hy _ hyes,hn _ hno]
    · simp [check,hj] at hc

/-- The actual returned checked pair contains exactly the submitted fine AST. -/
theorem certify_actual_input {n : ℕ} (i : Fin n) (p : Instruction n) (pq : Checked i)
    (h : certify i p=some pq) : pq.val.1=p := by
  unfold certify at h
  split at h
  · contradiction
  · have he := Option.some.inj h
    exact (congrArg (fun z : Checked i => z.val.1) he).symm


def instructionSubstrate (n : ℕ) : TrustedRepairSubstrate (Instruction n) (State n) Action :=
  ⟨interpret⟩

noncomputable section

/-- The original semantic property of the actual literal controller. -/
def ValidProgram {n : ℕ} (i : Fin n) (b : Bool) (p : Instruction n) : Prop :=
  RepairProgramValid (instructionSubstrate n) (physical i) (target i b) p

private theorem valid_iff_update {n : ℕ} (i : Fin n) (b : Bool) (p : Instruction n) :
    ValidProgram i b p ↔ ∀ x : State n, x i=b → update i x (interpret p x) i=b := by
  simp [ValidProgram,RepairProgramValid,PreservingController,UEOT.V3.ViabilityKernel.StaysIn,
    instructionSubstrate,physical,PMF.support_pure,Set.singleton_subset_iff,target]

/-- Construct a representative using the registered active observation. The
passive false fill is a proof device, never an executed reset/preparation. -/
def representative {n : ℕ} (i : Fin n) (y : State 1) : State n :=
  fun j => if j=i then y 0 else false

@[simp] theorem representative_project {n : ℕ} (i : Fin n) (y : State 1) :
    projectState i (representative i y)=y := by
  funext j
  have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
  subst j
  simp [projectState,representative]

/-- Validity is both preserved and reflected for SAME checked programs and
SAME registered target. No independent property/factor hypothesis is supplied. -/
theorem checked_valid_iff {n : ℕ} (i : Fin n) (b : Bool) (p : Instruction n) (q : Instruction 1)
    (hc : check i p=some q) : ValidProgram i b p ↔ ValidProgram (0 : Fin 1) b q := by
  rw [valid_iff_update,valid_iff_update]
  constructor
  · intro h y hy
    have hrep : representative i y i=b := by simp [representative,hy]
    have hp := h (representative i y) hrep
    have he := active_update i (representative i y) (interpret p (representative i y))
    have ha : interpret q y=interpret p (representative i y) := by
      simpa using check_interpret i p q hc (representative i y)
    rw [← ha] at hp
    rw [representative_project,← ha] at he
    exact he.trans hp
  · intro h x hx
    have hp := h (projectState i x) hx
    rw [check_interpret i p q hc x,active_update] at hp
    exact hp

/-- Typed P9 map on programs actually accepted by the syntax checker. -/
def programScale {n : ℕ} (i : Fin n) :
    ObjectScaleMap (State n) (State 1) (Checked i) (Instruction 1) :=
  ⟨projectState i,fun pq => pq.val.2⟩

theorem derived_valid_preservation {n : ℕ} (i : Fin n) (b : Bool) :
    PreservesObjectPredicate (programScale i)
      (fun pq => ValidProgram i b pq.val.1) (ValidProgram (0 : Fin 1) b) := by
  intro pq hp
  exact (checked_valid_iff i b pq.val.1 pq.val.2 pq.property).mp hp

/-- ORIGINAL P9 consumes the actually derived property preservation. -/
theorem p9_checked_program {n : ℕ} (i : Fin n) (b : Bool) (pq : Checked i)
    (hp : ValidProgram i b pq.val.1) : ValidProgram (0 : Fin 1) b pq.val.2 :=
  transport_object_property (programScale i) (fun pq => ValidProgram i b pq.val.1)
    (ValidProgram (0 : Fin 1) b) rfl (derived_valid_preservation i b) hp

/-- Conversely an actual checked coarse validity result certifies this actual
fine controller, rather than a newly chosen implementation. -/
theorem coarse_valid_certifies_actual_fine {n : ℕ} (i : Fin n) (b : Bool)
    (p : Instruction n) (q : Instruction 1) (hc : check i p=some q)
    (hq : ValidProgram (0 : Fin 1) b q) : ValidProgram i b p :=
  (checked_valid_iff i b p q hc).mpr hq

/-- Same action from SAME actual instructions; the old source then supplies
birth/failure, inherited code, physical seed, fee and parent provenance. -/
theorem checked_actual_transaction {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : Instruction n) (q : Instruction 1) (hc : check i p=some q)
    (o : Organism n) (mode label : Bool) :
    projectModeRecord i (modeRecordStep i m o (interpret p o.physical) mode label)=
      modeRecordStep (0 : Fin 1) m (projectOrganism i o)
        (interpret q (projectOrganism i o).physical) mode label := by
  rw [mode_step_transport]
  congr 1
  exact (check_interpret i p q hc o.physical).symm

def programRecords {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) : List (Bool × Bool) → List (ModeRecord n)
  | [] => []
  | (mode,label)::w =>
    let r := modeRecordStep i m o (interpret p o.physical) mode label
    r::programRecords i m p r.transaction.parentAfter w

/-- Every finite actual primitive word, including all failed/fault records.
The action is recomputed on the SAME retained parent's next physical state. -/
theorem checked_complete_records {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : Instruction n) (q : Instruction 1) (hc : check i p=some q)
    (o : Organism n) (w : List (Bool × Bool)) :
    (programRecords i m p o w).map (projectModeRecord i)=
      programRecords (0 : Fin 1) m q (projectOrganism i o) w := by
  induction w generalizing o with
  | nil => rfl
  | cons z w ih =>
    obtain ⟨mode,label⟩ := z
    simp only [programRecords,List.map_cons]
    rw [checked_actual_transaction i m p q hc]
    congr 1
    rw [ih]
    congr 1
    exact (congrArg (fun r : ModeRecord 1 => r.transaction.parentAfter)
      (checked_actual_transaction i m p q hc o mode label))

/-- Thus ANY complete primitive-word law, including correlated words, gives
exactly the actual coarse record law. No independent desired law is supplied. -/
theorem checked_record_law {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : Instruction n) (q : Instruction 1) (hc : check i p=some q)
    (o : Organism n) (mu : PMF (List (Bool × Bool))) :
    mu.map (fun w => (programRecords i m p o w).map (projectModeRecord i))=
      mu.map (fun w => programRecords (0 : Fin 1) m q (projectOrganism i o) w) := by
  congr 1
  funext w
  exact checked_complete_records i m p q hc o w

/-- Nontrivial nested AST: the last false emission is unreachable on Bool,
but both literal branches and all emits belong to the admitted family. -/
def nestedRepair {n : ℕ} (i : Fin n) : Instruction n :=
  .test i true (.emit none) (.test i false (.emit (some true)) (.emit (some false)))

@[simp] theorem check_nested {n : ℕ} (i : Fin n) :
    check i (nestedRepair i)=some (nestedRepair (0 : Fin 1)) := by
  simp [nestedRepair,check]

theorem nested_valid {n : ℕ} (i : Fin n) : ValidProgram i true (nestedRepair i) := by
  rw [valid_iff_update]
  intro x hx
  simp [nestedRepair,interpret,hx,update]

/-- Syntax checking is not an oracle for target validity: a literal wrong
write is admitted syntactically and really violates the registered target. -/
theorem checked_wrong_write_not_valid {n : ℕ} (i : Fin n) :
    check i (.emit (some false))=some (.emit (some false)) ∧
      ¬ ValidProgram i true (.emit (some false)) := by
  refine ⟨rfl,?_⟩
  rw [valid_iff_update]
  intro h
  have hf := h (fun _ => true) rfl
  simp [interpret,update] at hf

/-- The output of the actual executable checker is consumed by the original
P9 endpoint, and conversely certifies the submitted fine program. -/
theorem actual_checked_nested_consumer {n : ℕ} (i : Fin n) :
    ∃ pq : Checked i, certify i (nestedRepair i)=some pq ∧
      pq.val.1=nestedRepair i ∧ pq.val.2=nestedRepair (0 : Fin 1) ∧
      ValidProgram (0 : Fin 1) true pq.val.2 ∧ ValidProgram i true pq.val.1 := by
  let pq : Checked i := ⟨(nestedRepair i,nestedRepair 0),check_nested i⟩
  have hc : certify i (nestedRepair i)=some pq := by
    unfold certify
    split
    · rename_i h
      rw [check_nested i] at h
      contradiction
    · rename_i q h
      have he : q=nestedRepair 0 := Option.some.inj (h.symm.trans (check_nested i))
      subst q
      rfl
  refine ⟨pq,hc,certify_actual_input i _ pq hc,rfl,?_,?_⟩
  · exact p9_checked_program i true pq (nested_valid i)
  · exact coarse_valid_certifies_actual_fine i true _ _ pq.property
      (p9_checked_program i true pq (nested_valid i))

/-- A complete registered word with a real failed fault between two paid
repairs. No failed record, fee or retained parent is filtered out. -/
def actualWord : List (Bool × Bool) := [(true,true),(false,false),(true,false)]

theorem actual_nested_failed_paid_records (hidden : Bool) :
    let rs := programRecords (0 : Fin 2) ⟨true,1⟩ (nestedRepair 0)
      (passiveInitial hidden) actualWord
    rs.map (fun r => r.transaction.expenditure)=[1,0,1] ∧
    rs.map (fun r => r.transaction.child.isSome)=[true,false,true] ∧
    rs.map (fun r => r.transaction.action)=[some true,none,some true] ∧
    rs.map (projectModeRecord (0 : Fin 2))=
      programRecords (0 : Fin 1) ⟨true,1⟩ (nestedRepair 0)
        (projectOrganism 0 (passiveInitial hidden)) actualWord := by
  refine ⟨?_,?_,?_,checked_complete_records 0 ⟨true,1⟩ _ _ (check_nested 0) _ _⟩ <;>
    norm_num [programRecords,actualWord,nestedRepair,interpret,passiveInitial,modeRecordStep,
      RegisterJointRecord.recordStep,update,cost,Function.update_apply]

/-- An actual hidden-address query, outside the checked observation rights. -/
def hiddenTest : Instruction 2 := .test 1 true (.emit (some true)) (.emit none)

theorem hidden_test_rejected : check (0 : Fin 2) hiddenTest=none := by
  norm_num [hiddenTest,check,Fin.ext_iff]

/-- SAME fine controller and source: hiding its tested register prevents
exact action factorization. This does not rule out every OTHER controller. -/
theorem hidden_test_no_interpreter_factor :
    ¬ ∃ f : State 1 → Action, ∀ x : State 2,
      f (projectState (0 : Fin 2) x)=interpret hiddenTest x := by
  rintro ⟨f,hf⟩
  have h0 := hf ![false,false]
  have h1 := hf ![false,true]
  have hp : projectState (0 : Fin 2) ![false,false]=projectState (0 : Fin 2) ![false,true] := rfl
  rw [hp] at h0
  rw [h0] at h1
  norm_num [hiddenTest,interpret] at h1
  cases h1

def observedBirthFee (o : Organism 2) : Bool × ℝ :=
  let r := modeRecordStep (0 : Fin 2) ⟨true,1⟩ o (interpret hiddenTest o.physical) true true
  (r.transaction.child.isSome,r.transaction.expenditure)

/-- The loss is visible in ACTUAL birth and expenditure, not merely a code
label discrepancy. Both source states retain the same program and history. -/
theorem hidden_test_actual_birth_fee :
    projectOrganism (0 : Fin 2) (passiveInitial false)=
      projectOrganism (0 : Fin 2) (passiveInitial true) ∧
    observedBirthFee (passiveInitial false)=(false,0) ∧
    observedBirthFee (passiveInitial true)=(true,1) := by
  refine ⟨rfl,?_,?_⟩ <;>
    norm_num [observedBirthFee,passiveInitial,hiddenTest,interpret,modeRecordStep,
      RegisterJointRecord.recordStep,update,cost,Function.update_apply]

theorem hidden_test_no_actual_birth_fee_factor :
    ¬ ∃ f : Organism 1 → Bool × ℝ, ∀ o : Organism 2,
      f (projectOrganism (0 : Fin 2) o)=observedBirthFee o := by
  rintro ⟨f,hf⟩
  obtain ⟨hp,h0,h1⟩ := hidden_test_actual_birth_fee
  have he := hf (passiveInitial false)
  rw [hp,h0,hf (passiveInitial true),h1] at he
  exact Bool.false_ne_true (congrArg Prod.fst he.symm)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionScaleSource
