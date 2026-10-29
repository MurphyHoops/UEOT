import UEOT
open MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterFaultJointRecord
open RegisterPopulationJournalLearning
namespace ActualOwnJournalConsumer
noncomputable section
set_option linter.defProp false
local instance : MeasurableSpace (State 1) := ⊤
local instance : MeasurableSingletonClass (State 1) := ⟨fun _ => trivial⟩
local notation "S0" => RegisterOwnProgramPopulation.witnessInitial
local notation "ES" => RegisterOwnProgramJournalLearning.witnessEpisode
abbrev E := RegisterOwnProgramJournalLearning.WitnessEvent
private theorem born_at (j : E) (hj : (j : ℕ) = 0 ∨ (j : ℕ) = 2) :
    (RegisterOwnProgramPopulation.childAt (0 : Fin 1) 1 S0 ES j).isSome := by
  obtain hj0 | hj2 := hj
  · have heq : j = (0 : E) := Fin.ext hj0
    subst j
    norm_num [RegisterOwnProgramPopulation.childAt,RegisterOwnProgramPopulation.storeBefore,
      RegisterOwnProgramPopulation.run,RegisterOwnProgramPopulation.child,RegisterOwnProgramPopulation.mechanism,
      RegisterOwnProgramJournalLearning.witnessEpisode,RegisterOwnProgramPopulation.witnessEpisode,
      RegisterOwnProgramPopulation.witnessInitial,RegisterOwnProgramPopulation.witnessFounders,
      RegisterOwnProgramPopulation.witnessActions,RegisterOwnProgramPopulation.witnessModes,RegisterOwnProgramPopulation.compiledRequest,
      RegisterPopulationTypePrice.cohortRequests,RegisterPopulationTypePrice.request,
      RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.requestAt,
      RegisterPopulationHistorySource.child,RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.lookup,
      RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
      birthEvent,repairEvent,execute_compiled,update,List.range_succ]
  · have heq : j = (2 : E) := Fin.ext hj2
    subst j
    norm_num [RegisterOwnProgramPopulation.childAt,RegisterOwnProgramPopulation.storeBefore,
      RegisterOwnProgramPopulation.run,RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.child,RegisterOwnProgramPopulation.mechanism,
      RegisterOwnProgramJournalLearning.witnessEpisode,RegisterOwnProgramPopulation.witnessEpisode,
      RegisterOwnProgramPopulation.witnessInitial,RegisterOwnProgramPopulation.witnessFounders,
      RegisterOwnProgramPopulation.witnessActions,RegisterOwnProgramPopulation.witnessModes,RegisterOwnProgramPopulation.compiledRequest,
      RegisterPopulationTypePrice.cohortRequests,RegisterPopulationTypePrice.request,
      RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.requestAt,
      RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.child,RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.lookup,
      RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
      birthEvent,repairEvent,execute_compiled,update,List.range_succ]
def falseChild := (RegisterOwnProgramPopulation.childAt (0 : Fin 1) 1 S0 ES (0 : E)).get (born_at 0 (Or.inl rfl))
def trueChild := (RegisterOwnProgramPopulation.childAt (0 : Fin 1) 1 S0 ES (2 : E)).get (born_at 2 (Or.inr rfl))
private theorem hfalse : RegisterOwnProgramPopulation.childAt (0 : Fin 1) 1 S0 ES (0 : E) = some falseChild :=
  (Option.some_get (born_at 0 (Or.inl rfl))).symm
private theorem htrue : RegisterOwnProgramPopulation.childAt (0 : Fin 1) 1 S0 ES (2 : E) = some trueChild :=
  (Option.some_get (born_at 2 (Or.inr rfl))).symm
/-- All three registered primitive reads are kept; exactly two correct flags.
The third retained confuser draw refers to the failed journal event. -/
def omega : Raw E 3 := fun j => (decide ((j.2 : ℕ) < 2),1)
private theorem hgood : omega ∈ Good (J:=E) 3 := by
  change 3 < 2 * (Finset.univ.filter (fun k : Fin 3 => (omega ⟨(),k⟩).1 = true)).card
  decide
/-- Same actual protected false/true children are returned and receive OWN P5.
No global target/code equality is supplied. epsilon=1/4 matches the registered birth word. -/
def actual_both_selected_children_own_P5 := And.intro
  (RegisterOwnProgramJournalLearning.selected_actual_child_own_p5 (0 : Fin 1) 1 S0 ES
    (List.finRange (ES).length) 1 0 (List.mem_finRange _) falseChild hfalse omega hgood (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)))
  (RegisterOwnProgramJournalLearning.selected_actual_child_own_p5 (0 : Fin 1) 1 S0 ES
    (List.finRange (ES).length) 1 2 (List.mem_finRange _) trueChild htrue omega hgood (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)))
/-- Original Price is consumed on SAME episode's initial three-parent census. -/
def same_cohort_price := RegisterOwnProgramPopulation.witness_price (fun b => if b then 1 else 0)
/-- Original P12 is consumed uniformly over arbitrary confusers on this journal. -/
def same_episode_p12 (confuser : PMF E) :=
  RegisterOwnProgramJournalLearning.two_type_p12_consumer confuser (0 : E) 1
/-- Exact N=0 executable fallback, including the retained failed-event class. -/
example (data : Data 0) : select (List.finRange (ES).length) RegisterOwnProgramJournalLearning.witnessKey (1 : E) data = 1 := rfl
/-- Positive complete execution witness was derived from the original primitive law. -/
example : RegisterOwnProgramPopulation.fourDrawLaw.real {RegisterOwnProgramPopulation.witnessRaw} = 27/4096 :=
  RegisterOwnProgramPopulation.witness_source_mass
#print axioms actual_both_selected_children_own_P5
#print axioms same_cohort_price
#print axioms same_episode_p12
end
end ActualOwnJournalConsumer

namespace IndependentOwnJournal
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterPopulationJournalLearning
example (est : ∀ N, Data N → Observation) :
    ¬ (Tendsto (fun N => (observedLaw (1/2) (by norm_num) (PMF.pure (2 : RegisterOwnProgramJournalLearning.WitnessEvent)) RegisterOwnProgramJournalLearning.witnessKey 0 N).real
      {data | est N data ≠ RegisterOwnProgramJournalLearning.witnessParent 0}) atTop (𝓝 0) ∧
      Tendsto (fun N => (observedLaw (1/2) (by norm_num) (PMF.pure (0 : RegisterOwnProgramJournalLearning.WitnessEvent)) RegisterOwnProgramJournalLearning.witnessKey 2 N).real
      {data | est N data ≠ RegisterOwnProgramJournalLearning.witnessParent 2}) atTop (𝓝 0)) :=
  half_noise_no_joint_consistency RegisterOwnProgramJournalLearning.witnessKey 0 2 _ _
    (RegisterOwnProgramJournalLearning.two_type_half_noise_obstruction 0 (fun _ => none)).2.1 est
#print axioms RegisterOwnProgramJournalLearning.selected_actual_child_own_p5
#print axioms RegisterOwnProgramJournalLearning.actual_journal_discovery_consumes_p12
end IndependentOwnJournal
