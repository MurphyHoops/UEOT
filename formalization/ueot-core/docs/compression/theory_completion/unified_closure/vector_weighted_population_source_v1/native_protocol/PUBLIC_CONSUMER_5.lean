import UEOT
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterTimestampedBirthSource (ClockedOrganism)
namespace OwnProgramConsumer
noncomputable section
set_option linter.defProp false
local instance : MeasurableSpace (State 1) := ⊤
local instance : MeasurableSingletonClass (State 1) := ⟨fun _ => trivial⟩
local notation "S0" => RegisterOwnProgramPopulation.witnessInitial
local notation "acts" => RegisterOwnProgramPopulation.witnessActions
local notation "modes" => RegisterOwnProgramPopulation.witnessModes
private theorem actual_birth (j : Fin 3) (hj : (j : ℕ) ≠ 1) :
    (RegisterOwnProgramPopulation.offspring (0 : Fin 1) 1 S0 acts modes (fun _ => true) j).isSome := by
  fin_cases j <;>
    norm_num [RegisterOwnProgramPopulation.offspring,RegisterOwnProgramPopulation.before,
      RegisterOwnProgramPopulation.run,RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.child,RegisterOwnProgramPopulation.mechanism,
      RegisterPopulationTypePrice.cohortRequests,RegisterPopulationTypePrice.request,
      RegisterOwnProgramPopulation.witnessInitial,RegisterOwnProgramPopulation.witnessFounders,
      RegisterOwnProgramPopulation.witnessActions,RegisterOwnProgramPopulation.witnessModes,
      RegisterOwnProgramPopulation.compiledRequest,
      RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.next,
      RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.lookup,RegisterPopulationHistorySource.child,
      RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
      birthEvent,repairEvent,execute_compiled,update,List.range_succ] at *
def realFalseChild : ClockedOrganism 1 :=
  (RegisterOwnProgramPopulation.offspring (0 : Fin 1) 1 S0 acts modes (fun _ => true) (0 : Fin 3)).get
    (actual_birth 0 (by decide))
def realTrueChild : ClockedOrganism 1 :=
  (RegisterOwnProgramPopulation.offspring (0 : Fin 1) 1 S0 acts modes (fun _ => true) (2 : Fin 3)).get
    (actual_birth 2 (by decide))
private theorem real_false_birth : RegisterOwnProgramPopulation.child (0 : Fin 1) 1
    (RegisterOwnProgramPopulation.before (0 : Fin 1) 1 S0 acts modes (fun _ => true) 0)
    (RegisterPopulationTypePrice.request acts modes (fun _ => true) 0) = some realFalseChild :=
  (Option.some_get (actual_birth 0 (by decide))).symm
private theorem real_true_birth : RegisterOwnProgramPopulation.child (0 : Fin 1) 1
    (RegisterOwnProgramPopulation.before (0 : Fin 1) 1 S0 acts modes (fun _ => true) 2)
    (RegisterPopulationTypePrice.request acts modes (fun _ => true) 2) = some realTrueChild :=
  (Option.some_get (actual_birth 2 (by decide))).symm
/-- Both SAME actual children enter their OWN original P5, even at total fault. -/
def both_P5 := And.intro
  (RegisterOwnProgramPopulation.actual_child_enters_own_maintenance (0 : Fin 1) 1 _ _ realFalseChild real_false_birth 1 (by norm_num))
  (RegisterOwnProgramPopulation.actual_child_enters_own_maintenance (0 : Fin 1) 1 _ _ realTrueChild real_true_birth 1 (by norm_num))
/-- Newborn's first actual compiled step consumes the local funding source. -/
def real_false_first_step_funded :=
  RegisterOwnProgramPopulation.actual_child_first_step_funded (0 : Fin 1) 1 _ _ realFalseChild real_false_birth
    1 (by norm_num) false true
/-- Old fixed true-goal fault semantics leave the middle false parent false;
NEW own-program semantics damage it true in the exact source witness. -/
example :
    (RegisterPopulationHistorySource.lookup
      (RegisterPopulationHistorySource.run (0 : Fin 1) ⟨true,1⟩ S0 RegisterOwnProgramPopulation.witnessEpisode) 1).map
      (fun p => p.organism.physical 0) = some false := by
  norm_num [RegisterOwnProgramPopulation.witnessEpisode,RegisterPopulationTypePrice.cohortRequests,
    RegisterPopulationTypePrice.request,RegisterOwnProgramPopulation.witnessInitial,
    RegisterOwnProgramPopulation.witnessFounders,RegisterOwnProgramPopulation.witnessActions,
    RegisterOwnProgramPopulation.witnessModes,RegisterOwnProgramPopulation.compiledRequest,
    RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.run,RegisterPopulationHistorySource.next,
    RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.lookup,RegisterPopulationHistorySource.child,
    RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
    birthEvent,repairEvent,execute_compiled,update,List.range_succ]
/-- No whole-store equality is claimed: the old/new retained faulted parent differs. -/
example :
    (RegisterPopulationHistorySource.lookup RegisterOwnProgramPopulation.witnessAfterCohort 1).map
      (fun p => p.organism.physical 0) = some true :=
  RegisterOwnProgramPopulation.two_type_paid_repair_witness.2.2.2.2.2.1
#print axioms both_P5
#print axioms real_false_first_step_funded
end
end OwnProgramConsumer

namespace IndependentOwnPopulation
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open MeasureTheory ProbabilityTheory
noncomputable section
-- The actual offspring projection includes whole child objects, not type only.
example {n : ℕ} (i : Fin n) (c : NNReal) (s : RegisterPopulationHistorySource.Store n)
    (a : ℕ → RegisterRepairSource.Action) (m l : ℕ → Bool) (j : Fin s.length) (b : Bool) :
    RegisterOwnProgramPopulation.offspring i c s a m l j =
      RegisterPopulationTypePrice.offspring i ⟨b,c⟩ s a m l j :=
  RegisterOwnProgramPopulation.offspring_eq_old i c s a m l b j
example : (0 : ℝ) < RegisterOwnProgramPopulation.fourDrawLaw.real {RegisterOwnProgramPopulation.witnessRaw} := by
  rw [RegisterOwnProgramPopulation.witness_source_mass]
  norm_num
#print axioms RegisterOwnProgramPopulation.own_program_type_price
#print axioms RegisterOwnProgramPopulation.parent_eq_of_childID
#print axioms RegisterOwnProgramPopulation.actual_child_enters_own_maintenance
end
end IndependentOwnPopulation
