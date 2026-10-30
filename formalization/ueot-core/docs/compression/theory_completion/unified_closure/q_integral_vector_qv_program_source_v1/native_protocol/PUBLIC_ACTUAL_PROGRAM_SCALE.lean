import UEOT
namespace UEOTInstructionScaleIndependent
open MeasureTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.TheoryCompletion
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterActuatorScaleSource RegisterInstructionScaleSource RegisterSemanticInstructionScale
-- A new4-register actual literal program tests two hidden addresses, yet
-- both paths are the same idle action. Static access is only sufficient.
def hiddenIdle : Instruction 4 := .test 3 false (.emit none) (.test 0 true (.emit none) (.emit none))
def returnedIdle : Instruction 1 := .test 0 true (.emit none) (.emit none)
theorem hiddenIdle_interpret (x : State 4) : interpret hiddenIdle x=none := by simp [hiddenIdle,interpret]
theorem static_rejects_actual_semantic_passes :
    check (2 : Fin 4) hiddenIdle=none ∧ synthesize (2 : Fin 4) hiddenIdle=some returnedIdle := by
  constructor
  · norm_num [check,hiddenIdle,Fin.ext_iff]
  · have h : finiteCheck (2 : Fin 4) hiddenIdle=true := by
      rw [finiteCheck_iff_actual_fibers]
      intro x y _
      rw [hiddenIdle_interpret,hiddenIdle_interpret]
    have he : returnedProgram (2 : Fin 4) hiddenIdle=returnedIdle := by simp [returnedProgram,hiddenIdle_interpret,returnedIdle]
    simp [synthesize,h,he]
-- The proof consumes the ACTUAL returned program, and any entire original
-- primitive word/law, not another chosen implementation or a repaired trace.
example (m : Mechanism) (o : Organism 4) (w : List (Bool × Bool)) :=
  actual_complete_records (2 : Fin 4) m hiddenIdle returnedIdle static_rejects_actual_semantic_passes.2 o w
example (m : Mechanism) (o : Organism 4) (mu : PMF (List (Bool × Bool))) :=
  actual_complete_record_law (2 : Fin 4) m hiddenIdle returnedIdle static_rejects_actual_semantic_passes.2 o mu
example := actual_checked_nested_consumer (1 : Fin 3)
example := checked_wrong_write_not_valid (1 : Fin 3)
example (b : Bool) : ValidProgram (2 : Fin 4) b hiddenIdle ↔ ValidProgram (0 : Fin 1) b returnedIdle :=
  actual_valid_iff (2 : Fin 4) b hiddenIdle returnedIdle static_rejects_actual_semantic_passes.2
example := hidden_birth_fee_obstruction_preserved
-- Reverse quantifier is precise: exact FULL-state action factor by any
-- coarse current-state function, not all history-dependent policies.
example {n : ℕ} (i : Fin n) (p : Instruction n) (hn : synthesize i p=none) :=
  rejection_no_action_factor i p hn
#print axioms check_interpret
#print axioms checked_valid_iff
#print axioms synthesis_complete
#print axioms actual_complete_records
#print axioms actual_preserves_validity
#print axioms hidden_test_no_actual_birth_fee_factor
end UEOTInstructionScaleIndependent

open UEOTInstructionScaleIndependent
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterActuatorScaleSource RegisterInstructionScaleSource RegisterSemanticInstructionScale
#eval (check (2 : Fin 4) hiddenIdle).isSome
#eval (synthesize (2 : Fin 4) hiddenIdle).isSome
#eval List.ofFn (fun k : Fin 16 =>
  let x : State 4 := fun j => decide (((k : ℕ)/2^(j : ℕ))%2=1)
  (interpret hiddenIdle x,(synthesize (2 : Fin 4) hiddenIdle).map (fun q => interpret q (projectState 2 x))))
