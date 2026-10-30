import UEOT
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterActuatorScaleSource RegisterFaultInfiniteRecord
namespace ActualRegisterScaleConsumer
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _ => trivial⟩
def actualParent : Organism 3 := ⟨[false],![true,false,true],true⟩
def coarseMemory : witnessPolicy.Memory 0 := (fun _ => false : State 1)
def fineConfig : Config (liftPolicy (1 : Fin 3) witnessPolicy) :=
  ⟨0,(actualParent.physical,coarseMemory),actualParent⟩
def actualWord : Tape 2 := (some true,true,true,none,false,true,())
private theorem he : (1/4 : NNReal) ≤ 1 := by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)
/-- Nonzero active port1, real two-step word: repair/birth/paid fee, then
fault during requested idle. All fields/failure stages remain in the record. -/
theorem actual_two_step_record :
    let rs := records (1 : Fin 3) ⟨true,1⟩ (liftPolicy (1 : Fin 3) witnessPolicy) 2 (t:=0)
      (actualParent.physical,coarseMemory) actualParent actualWord
    rs.length=2 ∧
    (rs[0]?).map (fun r => r.transaction.expenditure)=some 1 ∧
    (rs[0]?).map (fun r => r.transaction.child.isSome)=some true ∧
    (rs[1]?).map (fun r => r.repairMode)=some false ∧
    (rs[1]?).map (fun r => r.transaction.child.isSome)=some false ∧
    (rs[1]?).map (fun r => r.transaction.expenditure)=some 0 := by
  norm_num [actualWord,actualParent,records,liftPolicy,witnessPolicy,selectorPolicy_advance,
    modeRecordStep,RegisterJointRecord.recordStep,update,RegisterMechanismPurpose.cost]
/-- Literal finite law, not an existence theorem for another policy. -/
example (k : ℕ) :
    (recordLaw (1 : Fin 3) (PMF.pure true) ⟨true,1⟩ (1/4) he (liftPolicy (1 : Fin 3) witnessPolicy) k (t:=0)
      (actualParent.physical,coarseMemory) actualParent).map (List.map (projectModeRecord (1 : Fin 3)))=
    recordLaw (0 : Fin 1) (PMF.pure true) ⟨true,1⟩ (1/4) he witnessPolicy k coarseMemory (projectOrganism (1 : Fin 3) actualParent) :=
  recordLaw_transport (1 : Fin 3) ⟨true,1⟩ witnessPolicy (PMF.pure true) (1/4) he k coarseMemory actualParent.physical actualParent
/-- Actual countable path law uses the SAME literal primitive process. -/
example :
    (recordPathLaw (1 : Fin 3) (PMF.pure true) ⟨true,1⟩ (1/4) he (liftPolicy (1 : Fin 3) witnessPolicy) fineConfig).map
      (fun rs k => projectModeRecord (1 : Fin 3) (rs k))=
    recordPathLaw (0 : Fin 1) (PMF.pure true) ⟨true,1⟩ (1/4) he witnessPolicy
      (projectConfig (1 : Fin 3) witnessPolicy fineConfig) :=
  recordPathLaw_transport (1 : Fin 3) ⟨true,1⟩ witnessPolicy (PMF.pure true) (1/4) he fineConfig
/-- Same source resource-sensitive purpose expectation. -/
example (k : ℕ) :
    actualExpectation (1 : Fin 3) (PMF.pure true) ⟨true,1⟩ (1/4) he
      (liftPolicy (1 : Fin 3) witnessPolicy) 1 (1/2) k (t:=0) (actualParent.physical,coarseMemory) actualParent=
    actualExpectation (0 : Fin 1) (PMF.pure true) ⟨true,1⟩ (1/4) he witnessPolicy 1 (1/2) k
      coarseMemory (projectOrganism (1 : Fin 3) actualParent) :=
  actualExpectation_transport (1 : Fin 3) (PMF.pure true) ⟨true,1⟩ (1/4) he witnessPolicy 1 (1/2) k
    coarseMemory actualParent.physical actualParent
/-- Original P9 repaired-target consumer at this nonzero port. -/
example : Legitimate (0 : Fin 1) (projectOrganism (1 : Fin 3) (repairEvent (1 : Fin 3) actualParent)) :=
  p9_actual_repaired_object (1 : Fin 3) actualParent
/-- Actual C4 and positive-support birth witness. -/
example : birthFormation (0 : Fin 1) 1 (some true) true true
    (projectOrganism (0 : Fin 2) (passiveInitial true)) (projectOrganism (0 : Fin 2) (actualBorn true)) :=
  (witness_c4_actual_consumer true).1
example : weight (0 : Fin 2) (PMF.pure true) ⟨true,1⟩ (1/4) he (liftPolicy (0 : Fin 2) witnessPolicy) 1 (t:=0)
    ((passiveInitial true).physical,witnessMemory) (passiveInitial true) (some true,true,true,())=(3/4 : ℝ) :=
  witness_actual_birth_weight true
#print axioms actual_two_step_record
end
end ActualRegisterScaleConsumer

namespace IndependentActiveObservationBoundary
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterActuatorScaleSource
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRepairHistory
-- This is exact recovery/reflection of an actual target property. We do NOT
-- infer failure of every one-way P9 predicate or every allowed coarse policy.
theorem hiding_active_cannot_reflect_actual_target :
    ¬ ∃ Q : Organism 1 → Prop, ∀ o : Organism 2,
      Q (projectOrganism (1 : Fin 2) o) ↔ Legitimate (0 : Fin 2) o := by
  rintro ⟨Q,hQ⟩
  have ht : Legitimate (0 : Fin 2) (activeInitial true) := rfl
  have hp := (hQ (activeInitial true)).mpr ht
  rw [hiding_active_birth_fee_obstruction.1] at hp
  have hf := (hQ (activeInitial false)).mp hp
  norm_num [Legitimate,activeInitial] at hf
#print axioms hiding_active_cannot_reflect_actual_target
#print axioms recordPathLaw_transport
#print axioms c4_actual_birth_next_binding
#print axioms p9_actual_repaired_object
end IndependentActiveObservationBoundary
