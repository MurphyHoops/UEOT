import UEOT
open MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterFaultJointRecord
open RegisterPopulationJournalLearning RegisterOwnProgramJointJournal
open scoped ENNReal
namespace ActualOwnJointConsumer
noncomputable section
set_option linter.defProp false
local instance : MeasurableSpace (State 1) := ⊤
local instance : MeasurableSingletonClass (State 1) := ⟨fun _ => trivial⟩
private theorem quarter_le_one : (1/4 : NNReal) ≤ 1 := by
  exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)
def omega : Reads 3 := fun j => (decide ((j.2 : ℕ) < 2),1)
private theorem hg : omega ∈ Good (J:=Event) 3 := by
  change 3 < 2 * (Finset.univ.filter (fun k : Fin 3 => (omega ⟨(),k⟩).1 = true)).card
  decide
private theorem hb : (actualChild RegisterOwnProgramPopulation.witnessRaw 0).isSome := by
  norm_num [actualChild,RegisterOwnProgramPopulation.fourStepRequests,List.ofFn_succ,
    RegisterOwnProgramPopulation.childAt,RegisterOwnProgramPopulation.storeBefore,RegisterOwnProgramPopulation.run,
    RegisterOwnProgramPopulation.child,RegisterOwnProgramPopulation.mechanism,
    RegisterOwnProgramPopulation.witnessRaw,RegisterOwnProgramPopulation.witnessModes,
    RegisterOwnProgramPopulation.witnessActions,RegisterOwnProgramPopulation.compiledRequest,
    RegisterOwnProgramPopulation.witnessInitial,RegisterOwnProgramPopulation.witnessFounders,
    RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.child,
    RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.lookup,RegisterPopulationHistorySource.requestAt,
    RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
    birthEvent,repairEvent,execute_compiled,update]
def realChild := (actualChild RegisterOwnProgramPopulation.witnessRaw 0).get hb
private theorem actual_born : actualChild RegisterOwnProgramPopulation.witnessRaw 0 = some realChild := (Option.some_get hb).symm
/-- Full-joint positive source witness: real population word, complete readout,
returned SAME actual child and same original own P5, all at hazard 1/4. -/
def joint_actual_selected_p5 := selected_actual_child_own_p5 0 1
  (RegisterOwnProgramPopulation.witnessRaw,omega) realChild actual_born hg
/-- All population source outcomes, arbitrary confuser, every N (including0). -/
example (confuser : PMF Event) (truth fallback : Event) (N : ℕ) :
    (jointLaw confuser N).real {z | parent z.1 (returnedEvent truth fallback z) ≠ parent z.1 truth} ≤
      Real.exp (-(N : ℝ)/8) := joint_parent_risk_le confuser truth fallback N
example (confuser : PMF Event) (truth fallback : Event) :
    Tendsto (fun N => (jointLaw confuser N).real {z | parent z.1 (returnedEvent truth fallback z) ≠ parent z.1 truth})
      atTop (𝓝 0) := joint_parent_risk_tendsto_zero confuser truth fallback
/-- Positive-mass all-failure population retained in the joint marginal. -/
example (confuser : PMF Event) (N : ℕ) :
    ((jointLaw confuser N).map Prod.fst).real {allFaultRaw} = 1/4096 := by
  rw [jointLaw_population_marginal]
  exact all_fault_positive_mass
example (truth : Event) : actualChild allFaultRaw truth = none := all_fault_target_not_born truth
/-- Complete fixed read batch has nonzero mass; its incorrect confuser read is
retained and addresses the actual failed event1. -/
theorem read_mass : (rawLaw (1/4) quarter_le_one (PMF.pure (1 : Event)) 3).real {omega} = 9/64 := by
  rw [Measure.real,rawLaw,VariableRegisteredSamples.productRowLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [Fintype.prod_sigma,Fintype.prod_unique,Fin.prod_univ_succ,omega,primitive_apply,ENNReal.toReal_mul,
    RegisterFaultControlModel.modeLaw,UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow_apply_toReal,
    RegisterFaultControlModel.modeProbability,RegisterFaultControlModel.repairChance,PMF.pure_apply]
/-- Literal unconditioned complete joint source gives this witness mass; it is
not a replacement measure for the uniform all-outcome risk result above. -/
theorem joint_word_mass :
    (jointLaw (PMF.pure (1 : Event)) 3).real ({RegisterOwnProgramPopulation.witnessRaw} ×ˢ {omega}) = 243/262144 := by
  rw [Measure.real,jointLaw,Measure.prod_prod,ENNReal.toReal_mul]
  change RegisterOwnProgramPopulation.fourDrawLaw.real {RegisterOwnProgramPopulation.witnessRaw} *
    (rawLaw (1/4) quarter_le_one (PMF.pure (1 : Event)) 3).real {omega} = _
  rw [RegisterOwnProgramPopulation.witness_source_mass,read_mass]
  norm_num
#print axioms joint_actual_selected_p5
#print axioms joint_word_mass
end
end ActualOwnJointConsumer

namespace IndependentOwnJointFailures
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterOwnProgramJointJournal
example (confuser : PMF Event) (N : ℕ) :
    (jointLaw confuser N).real ({allFaultRaw} ×ˢ Set.univ) = 1/4096 := by
  rw [Measure.real,jointLaw,Measure.prod_prod,measure_univ,mul_one]
  exact all_fault_positive_mass
#print axioms joint_parent_risk_le
#print axioms good_returned_actual_child
#print axioms selected_actual_child_own_p5
end IndependentOwnJointFailures
