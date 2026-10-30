import UEOT
namespace IndependentInstructionRecovery
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.TheoryCompletion
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterActuatorScaleSource RegisterInstructionScaleSource RegisterSemanticInstructionScale
open RegisterInstructionRecoveryScale RegisterSemanticInstructionInfinite
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _ => trivial⟩
def fine : Instruction 4 := .test 3 true (.emit (some false))
  (.test 0 false (.emit (some false)) (.emit (some false)))
def coarse : Instruction 1 := .test 0 true (.emit (some false)) (.emit (some false))
theorem fine_action (x : State 4) : interpret fine x=some false := by simp [fine,interpret]
theorem physical_check : restorationCheck (1 : Fin 4) false fine=true := by
  rw [restorationCheck_iff]
  intro x
  simp [fine_action,update]
theorem actual_returned : synthesize (1 : Fin 4) fine=some coarse := by
  have h : finiteCheck (1 : Fin 4) fine=true := by
    rw [finiteCheck_iff_actual_fibers]
    intro x y _
    rw [fine_action,fine_action]
  have he : returnedProgram (1 : Fin 4) fine=coarse := by simp [returnedProgram,fine_action,coarse]
  simp [synthesize,h,he]
example : check (1 : Fin 4) fine=none := by norm_num [check,fine,Fin.ext_iff]
example := actual_dynamics_implements (1 : Fin 4) false fine physical_check
example (x : State 4) := actual_recoverable (1 : Fin 4) false fine physical_check x
example (x : State 4) := actual_eventually_always (1 : Fin 4) false fine physical_check x
example : restorationCheck (0 : Fin 1) false coarse=true :=
  (returned_restoration_iff (1 : Fin 4) false fine coarse actual_returned).mp physical_check
def actualPair : RecoveringPair (1 : Fin 4) false := ⟨⟨(fine,coarse),actual_returned⟩,physical_check⟩
example : RecoversEverywhere (0 : Fin 1) false coarse :=
  p9_actual_returned_recovery (1 : Fin 4) false actualPair
example (o : Organism 4) (w : Stream) (t : ℕ) (hp : o.program=false) :
    Legitimate 1 (parentAt 1 ⟨false,3⟩ fine o w (t+1)) ↔ (w t).1=true :=
  actual_stream_legitimacy 1 false 3 fine physical_check o hp w t
example (o : Organism 4) (μ : Measure Stream) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (recordPathLaw (1 : Fin 4) ⟨false,3⟩ fine o μ) := inferInstance
example (o : Organism 4) (μ : Measure Stream) :
    (recordPathLaw (1 : Fin 4) ⟨false,3⟩ fine o μ).map (projectPath 1)=
      recordPathLaw (0 : Fin 1) ⟨false,3⟩ coarse (projectOrganism 1 o) μ :=
  actual_countable_path_law 1 ⟨false,3⟩ fine coarse actual_returned o μ
-- All-time native recovery uses a no-fault source. The actual complete-record
-- fault law above keeps every repeated failure instead of discarding paths.
example (w : Stream) (hw : ∀ t,(w t).1=true) := idle_actual_never_recovers (1 : Fin 4) 3 w hw
example := idle_valid_not_restoring (1 : Fin 4) false
example : let o : Organism 4 := ⟨[],fun _=>false,false⟩
    (modeRecordStep 1 ⟨false,3⟩ o (interpret fine o.physical) true true).transaction.expenditure=3 ∧
    (modeRecordStep 1 ⟨false,3⟩ o (interpret (compile 1 false) o.physical) true true).transaction.expenditure=0 := by
  norm_num [modeRecordStep,RegisterJointRecord.recordStep,fine_action,interpret,compile,cost]
#print axioms actual_dynamics_implements
#print axioms actual_recoverable
#print axioms actual_eventually_always
#print axioms returned_restoration_iff
#print axioms p9_actual_returned_recovery
#print axioms actual_stream_legitimacy
end
end IndependentInstructionRecovery
