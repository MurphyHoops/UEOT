import UEOT
namespace IdentityReusedPopulationAuthorConsumer
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord RegisterFaultInfiniteRecord
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open RegisterPopulationHistorySource (Store Request)
open RegisterActuatorScaleSource RegisterActuatorPopulationScale

-- Actual inherited TWO program types, retained failure and paid repair, BOTH passive bit settings.
example (hidden : Bool) := witness_two_types_failure_and_fee hidden
example (hidden : Bool) (z : Bool → ℝ) := witness_actual_price hidden z
example (hidden : Bool) := witness_complete_journal_law hidden
example (hidden : Bool) (w : Fin 4 → Bool × Bool) := witness_full_population_source hidden w
-- No independent proof of a factor is supplied; actual prefix lookup/compiled interpreter determines SAME action.
example (hidden : Bool) (past : List Request) (j : ℕ) (mode label : Bool) :=
  witness_actual_requests hidden past j mode label
-- Actual missing-address transaction remains None and tick is retained in complete trace.
example (hidden : Bool) : transactionTrace (1 : Fin 3) 1 (witnessStore hidden) [⟨99,some true,true,false⟩]=[none] := by
  norm_num [transactionTrace,RegisterOwnProgramPopulation.transaction,RegisterOwnProgramPopulation.mechanism,
    RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.lookup,witnessStore,
    RegisterOwnProgramPopulation.witnessInitial,RegisterOwnProgramPopulation.witnessFounders,
    RegisterPopulationHistorySource.founders]
-- Full chronological records, not merely successful children/final store.
example (hidden : Bool) (es : List Request) :
    (transactionTrace (1 : Fin 3) 1 (witnessStore hidden) es).map (Option.map (projectClockedRecord (1 : Fin 3)))=
      transactionTrace (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial es := by
  rw [transaction_trace_transport,project_witnessStore]
-- Child legitimacy is read from the actual source, no global-goal equality premise is needed.
example (hidden : Bool) (q : Request) (d : ClockedOrganism 3)
    (hd : RegisterOwnProgramPopulation.child (1 : Fin 3) 1 (witnessStore hidden) q=some d) :
    d.organism.physical 1=d.organism.program :=
  RegisterOwnProgramPopulation.child_legitimate (1 : Fin 3) 1 _ q d hd

local instance {d : ℕ} : MeasurableSpace (ModeRecord d) := ⊤
local instance {d : ℕ} : MeasurableSingletonClass (ModeRecord d) := ⟨fun _ => trivial⟩
-- The actual post-episode retained parent is the continuation seed; no replacement/preparation.
example (hidden : Bool) (p : ClockedOrganism 3)
    (_hp : RegisterPopulationHistorySource.lookup
      (RegisterOwnProgramPopulation.run (1 : Fin 3) 1 (witnessStore hidden)
        (RegisterOwnProgramPopulation.fourStepRequests RegisterOwnProgramPopulation.witnessRaw)) 1=some p) :
    let m : Mechanism := ⟨p.organism.program,1⟩
    let pi := selectorPolicy ((substrate (0 : Fin 1)).execute m.goal)
    ∀ᵐ rs ∂recordPathLaw (1 : Fin 3) (PMF.pure true) m (1/4) (by change (1/4 : ℝ) ≤ 1; norm_num) (liftPolicy (1 : Fin 3) pi)
      ⟨0,(p.organism.physical,projectState (1 : Fin 3) p.organism.physical),p.organism⟩,
      ResourceViable 1 (fun t => RegisterFaultFeedbackResource.idleInflow 1 (rs t))
        (fun t => (rs t).transaction.expenditure) := by
  exact lifted_actual_resource_viable (1 : Fin 3) (PMF.pure true) ⟨p.organism.program,1⟩
    (1/4) (by change (1/4 : ℝ) ≤ 1; norm_num) 1 1 (by norm_num) (by norm_num) p.organism

#print axioms timestamp_transport
#print axioms own_run_transport
#print axioms transaction_trace_transport
#print axioms compiled_episode_transport
#print axioms actual_journal_transport
#print axioms nonempty_cohort_transport
#print axioms witness_actual_price
#print axioms witness_complete_journal_law
#print axioms lifted_actual_resource_viable
#print axioms witness_two_types_failure_and_fee
end IdentityReusedPopulationAuthorConsumer

namespace IndependentActualPostEpisodeParent
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord RegisterFaultInfiniteRecord
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open RegisterPopulationHistorySource (Store Request)
open RegisterActuatorScaleSource RegisterActuatorPopulationScale
noncomputable section

example : Fintype.card (Fin 4 → Bool × Bool)=256 := by norm_num [Fintype.card_fun]
example : RegisterOwnProgramPopulation.fourDrawLaw.real {RegisterOwnProgramPopulation.witnessRaw}=27/4096 :=
  RegisterOwnProgramPopulation.witness_source_mass

-- Compute the retained parent from the ACTUAL four-step store, without an external hp.
def postStore (hidden : Bool) : Store 3 :=
  RegisterOwnProgramPopulation.run (1 : Fin 3) 1 (witnessStore hidden)
    (RegisterOwnProgramPopulation.fourStepRequests RegisterOwnProgramPopulation.witnessRaw)
def postParent (hidden : Bool) : ClockedOrganism 3 :=
  (RegisterPopulationHistorySource.lookup (postStore hidden) 1).getD ⟨⟨[],fun _ => false,false⟩,[],0⟩

theorem coarse_post_physical :
    (RegisterPopulationHistorySource.lookup
      (RegisterOwnProgramPopulation.run (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial
        (RegisterOwnProgramPopulation.fourStepRequests RegisterOwnProgramPopulation.witnessRaw)) 1).map
      (fun p => p.organism.physical 0)=some false := by
  rw [RegisterOwnProgramPopulation.witness_same_actual_episode]
  simpa only [RegisterOwnProgramPopulation.run,List.foldl_append,List.foldl_cons,List.foldl_nil,
    RegisterOwnProgramPopulation.witnessAfterCohort] using
    RegisterOwnProgramPopulation.two_type_paid_repair_witness.2.2.2.2.2.2.2.2.1

theorem post_lookup_physical (hidden : Bool) :
    (RegisterPopulationHistorySource.lookup (postStore hidden) 1).map (fun p => p.organism.physical 1)=some false := by
  have hp := witness_full_population_source hidden RegisterOwnProgramPopulation.witnessRaw
  have h := congrArg (fun s => (RegisterPopulationHistorySource.lookup s 1).map (fun p => p.organism.physical 0)) hp
  simp only [lookup_transport,Option.map_map] at h
  exact h.trans coarse_post_physical

theorem post_lookup (hidden : Bool) :
    RegisterPopulationHistorySource.lookup (postStore hidden) 1=some (postParent hidden) := by
  have h := post_lookup_physical hidden
  cases he : RegisterPopulationHistorySource.lookup (postStore hidden) 1 with
  | none => simp [he] at h
  | some p => simp [postParent,he]

local instance {d : ℕ} : MeasurableSpace (ModeRecord d) := ⊤
local instance {d : ℕ} : MeasurableSingletonClass (ModeRecord d) := ⟨fun _ => trivial⟩

-- SAME actual post-episode parent: neither an assumed existence nor a new physical seed.
theorem actual_post_parent_resource (hidden : Bool) :
    RegisterPopulationHistorySource.lookup (postStore hidden) 1=some (postParent hidden) ∧
    let o := (postParent hidden).organism
    let m : Mechanism := ⟨o.program,1⟩
    let pi := selectorPolicy ((substrate (0 : Fin 1)).execute m.goal)
    ∀ᵐ rs ∂recordPathLaw (1 : Fin 3) (PMF.pure true) m (1/4)
      (by change (1/4 : ℝ) ≤ 1; norm_num) (liftPolicy (1 : Fin 3) pi)
      ⟨0,(o.physical,projectState (1 : Fin 3) o.physical),o⟩,
      ResourceViable 1 (fun t => RegisterFaultFeedbackResource.idleInflow 1 (rs t))
        (fun t => (rs t).transaction.expenditure) := by
  refine ⟨post_lookup hidden,?_⟩
  exact lifted_actual_resource_viable (1 : Fin 3) (PMF.pure true)
    ⟨(postParent hidden).organism.program,1⟩ (1/4) (by change (1/4 : ℝ) ≤ 1; norm_num)
    1 1 (by norm_num) (by norm_num) (postParent hidden).organism

-- Actual invalid address keeps a failed allocation tick, not a borrowed actor.
example (hidden : Bool) :
    (RegisterOwnProgramPopulation.run (1 : Fin 3) 1 (witnessStore hidden)
      [⟨99,some true,true,false⟩]).length=(witnessStore hidden).length+1 := by
  rw [RegisterOwnProgramPopulation.run_length]
  rfl
#print axioms actual_post_parent_resource
end
end IndependentActualPostEpisodeParent
