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

open ProbabilityTheory Set RegisterFaultControlModel RegisterSemanticInstructionInfinite
open scoped NNReal ENNReal
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _ => trivial⟩
def tape (b : Bool) : Stream := fun t => if b then (decide (t%2=0),true) else (false,false)
def coin : PMF Bool := modeLaw (1/3) (by norm_num [div_le_iff₀])
def raw : Measure Stream := coin.toMeasure.map tape
instance : IsProbabilityMeasure raw := Measure.isProbabilityMeasure_map (measurable_of_finite tape).aemeasurable
def actual (o : Organism 4) := recordPathLaw (2 : Fin 4) ⟨true,2⟩ hiddenIdle o raw
example (o : Organism 4) : IsProbabilityMeasure (actual o) := inferInstanceAs (IsProbabilityMeasure (recordPathLaw _ _ _ _ raw))
example (o : Organism 4) : (actual o).map (projectPath (2 : Fin 4))=
    recordPathLaw (0 : Fin 1) ⟨true,2⟩ returnedIdle (projectOrganism 2 o) raw :=
  actual_countable_path_law 2 ⟨true,2⟩ _ _ static_rejects_actual_semantic_passes.2 o raw
example (o : Organism 4) (N : ℕ) : (actual o).map (fun rs (j : Fin N) => rs j)=
    (raw.map (finiteRaw N)).map (finiteRecords (2 : Fin 4) ⟨true,2⟩ hiddenIdle o N) :=
  actual_prefix_law 2 ⟨true,2⟩ hiddenIdle o raw N
def firstMode : Set (ℕ→ModeRecord 4) := {rs | (rs 0).repairMode=true}
theorem measurable_firstMode : MeasurableSet firstMode := by
  change MeasurableSet ((fun rs : ℕ→ModeRecord 4 => rs 0) ⁻¹' {r : ModeRecord 4 | r.repairMode=true})
  exact (measurable_pi_apply 0) trivial
example (o : Organism 4) : actual o firstMode=ENNReal.ofReal (2/3 : ℝ) := by
  rw [actual,recordPathLaw,Measure.map_apply (measurable_recordPath _ _ _ _) measurable_firstMode,
    raw,Measure.map_apply (measurable_of_finite tape) ((measurable_recordPath _ _ _ _) measurable_firstMode)]
  have hp : tape ⁻¹' (recordAt (2 : Fin 4) ⟨true,2⟩ hiddenIdle o) ⁻¹' firstMode={true} := by
    ext b
    cases b <;> simp [tape,firstMode,recordAt,parentAt,modeRecordStep]
  rw [hp,PMF.toMeasure_apply_singleton coin true (measurableSet_singleton true)]
  norm_num [coin,modeLaw,UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow,modeProbability,repairChance]
example (o : Organism 4) (w : Stream) (N : ℕ) := actual_finite_prefix 2 ⟨true,2⟩ hiddenIdle o w N
example (o : Organism 4) (w : Stream) (t : ℕ) := actual_protected_program 2 ⟨true,2⟩ hiddenIdle o w t
example (o : Organism 4) : (recordAt 2 ⟨true,2⟩ hiddenIdle o (tape true) 10).repairMode=true := by
  norm_num [recordAt,parentAt,tape,modeRecordStep]
example (o : Organism 4) (S : Set (ℕ→ModeRecord 1)) (hS : MeasurableSet S) :=
  actual_event_probability 2 ⟨true,2⟩ hiddenIdle returnedIdle static_rejects_actual_semantic_passes.2 o raw S hS
#print axioms actual_finite_prefix
#print axioms measurable_recordPath
#print axioms recordPathLaw_probability
#print axioms actual_countable_path_law
#print axioms actual_p9_countable_consumer
end
end UEOTInstructionScaleIndependent
