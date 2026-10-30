import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionScaleSource
import UEOT.V3.Compression.QuotientDescent

/-!
Original promise: determine whether THIS actual literal controller executes exactly through the actuator projection.
Existing result: syntax check is sound but rejects harmless hidden tests; FiberCompatible characterizes set-level descent, without an actual returned Instruction.
Reduced premise: evaluate the complete finite interpret truth table, check its actual fibers, and return an original-language two-branch Instruction with a proved exact implementation.
Family: SAME finite Bool register bank, retained actuator, Option Bool actions and original primitive records; harmless hidden tests pass, genuinely different hidden actions fail.
Consumers: existing FiberCompatible, static checked-program source, complete finite record laws, original RepairProgramValid and P9.

No source/fiber consistency is an input certificate. The finite check itself
computes it. Complete enumeration costs exponentially in register count; this
claims exact finite decidability, not efficient synthesis. Canonical passive
representatives are interpreter evaluation inputs for the checker, never actual
resets/preparations. The resulting controller reads only the original actuator;
protected inherited Bool repair code, original permitted actions/observations,
fault/birth/cost semantics and all failed records are unchanged. No general
kernel identification, arbitrary partial/reachable-domain completeness, merge,
all six P9 semantics or full World is claimed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterSemanticInstructionScale
open MeasureTheory Function
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.QuotientDescent
open UEOT.V3.Compression.Objecthood UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultJointRecord RegisterActuatorScaleSource RegisterInstructionScaleSource

def finiteCheck {n : ℕ} (i : Fin n) (p : Instruction n) : Bool :=
  decide (∀ x : State n, interpret p x=interpret p (representative i (projectState i x)))

/-- Two actual interpreter readings produce a literal allowed coarse AST. -/
def returnedProgram {n : ℕ} (i : Fin n) (p : Instruction n) : Instruction 1 :=
  .test 0 true (.emit (interpret p (representative i (fun _ => true))))
    (.emit (interpret p (representative i (fun _ => false))))

/-- Same finite table, reified at the original actuator for static-source reuse. -/
def fineTable {n : ℕ} (i : Fin n) (p : Instruction n) : Instruction n :=
  .test i true (.emit (interpret p (representative i (fun _ => true))))
    (.emit (interpret p (representative i (fun _ => false))))

def synthesize {n : ℕ} (i : Fin n) (p : Instruction n) : Option (Instruction 1) :=
  if finiteCheck i p then some (returnedProgram i p) else none

@[simp] theorem check_fineTable {n : ℕ} (i : Fin n) (p : Instruction n) :
    check i (fineTable i p)=some (returnedProgram i p) := by
  simp [fineTable,returnedProgram,check]

private theorem returnedProgram_interpret {n : ℕ} (i : Fin n) (p : Instruction n) (y : State 1) :
    interpret (returnedProgram i p) y=interpret p (representative i y) := by
  have he : y=(fun _ => y 0) := by funext j; congr 1; exact Subsingleton.elim _ _
  cases hb : y 0 <;> rw [he] <;> simp [returnedProgram,interpret,hb]

/-- The executable check is exactly the original actual-action fiber condition. -/
theorem finiteCheck_iff_actual_fibers {n : ℕ} (i : Fin n) (p : Instruction n) :
    finiteCheck i p=true ↔ FiberCompatible (projectState i) (interpret p) := by
  simp only [finiteCheck,decide_eq_true_eq]
  constructor
  · intro h x y hxy
    rw [h x,h y,hxy]
  · intro h x
    exact h (by simp)

/-- Success binds the actually returned AST and proves its full-state action
factor, rather than selecting another implementation with choice. -/
theorem synthesize_actual {n : ℕ} (i : Fin n) (p : Instruction n) (q : Instruction 1)
    (hs : synthesize i p=some q) :
    q=returnedProgram i p ∧ ∀ x : State n, interpret q (projectState i x)=interpret p x := by
  have ht : finiteCheck i p=true ∧ q=returnedProgram i p := by
    unfold synthesize at hs
    split at hs
    · exact ⟨by assumption,(Option.some.inj hs).symm⟩
    · contradiction
  refine ⟨ht.2,?_⟩
  rw [ht.2]
  intro x
  rw [returnedProgram_interpret]
  exact ((finiteCheck_iff_actual_fibers i p).mp ht.1 (by simp)).symm

/-- Any proposed coarse implementation forces this concrete finite check to
pass; no surjective decoder or desired factor input is needed in the algorithm. -/
theorem any_implementation_forces_check {n : ℕ} (i : Fin n) (p : Instruction n)
    (f : State 1 → Action) (hf : ∀ x : State n, f (projectState i x)=interpret p x) :
    finiteCheck i p=true := by
  apply (finiteCheck_iff_actual_fibers i p).mpr
  exact fiberCompatible_of_comp_eq (projectState i) (interpret p) f (funext hf)

/-- Exact necessary/sufficient implementation theorem in the ORIGINAL allowed
Instruction language, not an abstract unimplemented decoder. -/
theorem synthesis_complete {n : ℕ} (i : Fin n) (p : Instruction n) :
    (∃ q : Instruction 1, synthesize i p=some q) ↔
      ∃ q : Instruction 1, ∀ x : State n, interpret q (projectState i x)=interpret p x := by
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨q,(synthesize_actual i p q hq).2⟩
  · rintro ⟨q,hq⟩
    have ht := any_implementation_forces_check i p (interpret q) hq
    exact ⟨returnedProgram i p,by simp [synthesize,ht]⟩

/-- Rejection is a proved obstruction to ANY coarse action function, hence
also to every coarse Instruction, in this exact full-state/action contract. -/
theorem rejection_no_action_factor {n : ℕ} (i : Fin n) (p : Instruction n)
    (hn : synthesize i p=none) :
    ¬ ∃ f : State 1 → Action, ∀ x : State n, f (projectState i x)=interpret p x := by
  rintro ⟨f,hf⟩
  have ht := any_implementation_forces_check i p f hf
  simp [synthesize,ht] at hn

noncomputable section

private theorem same_actual_as_fineTable {n : ℕ} (i : Fin n) (p : Instruction n) (q : Instruction 1)
    (hs : synthesize i p=some q) : ∀ x, interpret p x=interpret (fineTable i p) x := by
  intro x
  have h := (synthesize_actual i p q hs).2 x
  rw [(synthesize_actual i p q hs).1] at h
  exact h.symm.trans (check_interpret i _ _ (check_fineTable i p) x)

/-- Existing static-source P9 validity theorem is reused through the computed
literal fine table, whose actual actions are proved equal to THIS input AST. -/
theorem actual_valid_iff {n : ℕ} (i : Fin n) (b : Bool) (p : Instruction n) (q : Instruction 1)
    (hs : synthesize i p=some q) : ValidProgram i b p ↔ ValidProgram (0 : Fin 1) b q := by
  have he : interpret p=interpret (fineTable i p) := funext (same_actual_as_fineTable i p q hs)
  change RepairProgramValid (instructionSubstrate n) (physical i) (target i b) p ↔ _
  unfold RepairProgramValid
  change PreservingController (physical i) (target i b) (interpret p) ↔ _
  rw [he]
  exact checked_valid_iff i b (fineTable i p) q
    (by rw [(synthesize_actual i p q hs).1]; exact check_fineTable i p)

abbrev Accepted {n : ℕ} (i : Fin n) :=
  {pq : Instruction n × Instruction 1 // synthesize i pq.1=some pq.2}

def programScale {n : ℕ} (i : Fin n) :
    ObjectScaleMap (State n) (State 1) (Accepted i) (Instruction 1) :=
  ⟨projectState i,fun pq => pq.val.2⟩

theorem actual_preserves_validity {n : ℕ} (i : Fin n) (b : Bool) :
    PreservesObjectPredicate (programScale i) (fun pq => ValidProgram i b pq.val.1)
      (ValidProgram (0 : Fin 1) b) := by
  intro pq hp
  exact (actual_valid_iff i b _ _ pq.property).mp hp

theorem p9_actual_returned_program {n : ℕ} (i : Fin n) (b : Bool) (pq : Accepted i)
    (hp : ValidProgram i b pq.val.1) : ValidProgram (0 : Fin 1) b pq.val.2 :=
  transport_object_property (programScale i) (fun pq => ValidProgram i b pq.val.1)
    (ValidProgram (0 : Fin 1) b) rfl (actual_preserves_validity i b) hp

private theorem records_same_actions {n : ℕ} (i : Fin n) (m : Mechanism)
    (p p' : Instruction n) (he : ∀ x, interpret p x=interpret p' x)
    (o : Organism n) (w : List (Bool × Bool)) :
    programRecords i m p o w=programRecords i m p' o w := by
  induction w generalizing o with
  | nil => rfl
  | cons z w ih =>
    obtain ⟨mode,label⟩ := z
    simp only [programRecords,he,ih]

/-- Full primitive word execution of SAME input AST equals the actual returned
program after projection; static transport is reused without modifying it. -/
theorem actual_complete_records {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : Instruction n) (q : Instruction 1) (hs : synthesize i p=some q)
    (o : Organism n) (w : List (Bool × Bool)) :
    (programRecords i m p o w).map (projectModeRecord i)=
      programRecords (0 : Fin 1) m q (projectOrganism i o) w := by
  rw [records_same_actions i m p (fineTable i p) (same_actual_as_fineTable i p q hs)]
  exact checked_complete_records i m _ _
    (by rw [(synthesize_actual i p q hs).1]; exact check_fineTable i p) o w

/-- Every complete word and arbitrary actual word law, including faults and
failed births, is retained. No independent desired coarse law is a premise. -/
theorem actual_complete_record_law {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : Instruction n) (q : Instruction 1) (hs : synthesize i p=some q)
    (o : Organism n) (mu : PMF (List (Bool × Bool))) :
    mu.map (fun w => (programRecords i m p o w).map (projectModeRecord i))=
      mu.map (fun w => programRecords (0 : Fin 1) m q (projectOrganism i o) w) := by
  congr 1
  funext w
  exact actual_complete_records i m p q hs o w

/-- The static check rejects even this harmless hidden branch: both branches
execute the same real nested repair controller. -/
def benignHidden : Instruction 2 :=
  .test 1 true (nestedRepair 0) (nestedRepair 0)

private theorem benign_interpret (x : State 2) :
    interpret benignHidden x=interpret (nestedRepair (0 : Fin 2)) x := by
  simp [benignHidden,interpret]

theorem benign_static_rejects_semantic_accepts :
    check (0 : Fin 2) benignHidden=none ∧
      synthesize (0 : Fin 2) benignHidden=some (compile (0 : Fin 1) true) := by
  constructor
  · norm_num [check,benignHidden,Fin.ext_iff]
  · have ht : finiteCheck (0 : Fin 2) benignHidden=true := by
      rw [finiteCheck_iff_actual_fibers]
      intro x y hxy
      have hb : x 0=y 0 := congrFun hxy 0
      rw [benign_interpret,benign_interpret]
      simp only [nestedRepair,interpret,hb]
    have he : returnedProgram (0 : Fin 2) benignHidden=compile (0 : Fin 1) true := by
      norm_num [returnedProgram,benignHidden,nestedRepair,compile,interpret,representative]
    simp [synthesize,ht,he]

theorem benign_actual_valid : ValidProgram (0 : Fin 2) true benignHidden := by
  have he : interpret benignHidden=interpret (nestedRepair (0 : Fin 2)) := funext benign_interpret
  change PreservingController (physical (0 : Fin 2)) (target 0 true) (interpret benignHidden)
  rw [he]
  exact nested_valid 0

/-- The actual synthesized program, including every failed/fault record, is
consumed by the original semantic property endpoint on THIS rejected-by-syntax
fine AST. No replacement AST is substituted for the physical execution. -/
theorem benign_actual_p9_and_records (hidden : Bool) :
    ValidProgram (0 : Fin 1) true (compile 0 true) ∧
    (programRecords (0 : Fin 2) ⟨true,1⟩ benignHidden (passiveInitial hidden) actualWord).map
      (projectModeRecord (0 : Fin 2))=
      programRecords (0 : Fin 1) ⟨true,1⟩ (compile 0 true)
        (projectOrganism 0 (passiveInitial hidden)) actualWord := by
  have hs := benign_static_rejects_semantic_accepts.2
  let pq : Accepted (0 : Fin 2) := ⟨(benignHidden,compile 0 true),hs⟩
  exact ⟨p9_actual_returned_program 0 true pq benign_actual_valid,
    actual_complete_records 0 ⟨true,1⟩ _ _ hs _ _⟩

theorem benign_actual_failed_paid :
    let rs := programRecords (0 : Fin 2) ⟨true,1⟩ benignHidden (passiveInitial true) actualWord
    rs.map (fun r => r.transaction.expenditure)=[1,0,1] ∧
      rs.map (fun r => r.transaction.child.isSome)=[true,false,true] := by
  rw [records_same_actions (0 : Fin 2) ⟨true,1⟩ _ _ benign_interpret]
  exact ⟨(actual_nested_failed_paid_records true).1,(actual_nested_failed_paid_records true).2.1⟩

/-- Existing SAME-source hidden-action obstruction now forces actual semantic
rejection, distinguishing a semantic impossibility from static incompleteness. -/
theorem hidden_actual_obstruction_rejected : synthesize (0 : Fin 2) hiddenTest=none := by
  cases hs : synthesize (0 : Fin 2) hiddenTest with
  | none => rfl
  | some q =>
    exact False.elim (hidden_test_no_interpreter_factor ⟨interpret q,(synthesize_actual 0 _ q hs).2⟩)

/-- The no-go concerns the SAME exact action-factor contract. The already
proved actual birth/fee distinction remains a downstream observable witness. -/
theorem hidden_birth_fee_obstruction_preserved :
    synthesize (0 : Fin 2) hiddenTest=none ∧
      ¬ ∃ f : Organism 1 → Bool × ℝ, ∀ o : Organism 2,
        f (projectOrganism (0 : Fin 2) o)=observedBirthFee o :=
  ⟨hidden_actual_obstruction_rejected,hidden_test_no_actual_birth_fee_factor⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterSemanticInstructionScale
