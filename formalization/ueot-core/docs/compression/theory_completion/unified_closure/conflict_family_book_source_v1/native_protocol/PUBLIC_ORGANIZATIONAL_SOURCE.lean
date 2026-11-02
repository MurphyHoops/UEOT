import UEOT
namespace IndependentConflictOrganizational
open UEOT.V3.FiniteDiscountedControl UEOT.V3.FiniteStablePartition
open UEOT.V3.Compression.RecursiveSufficientState
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.ViabilityKernel UEOT.V3.PathError
open SupportViabilityClosure SourcePolicyPathBridgeCheck
noncomputable section
abbrev C:=ConflictOrganizationalSource.State

theorem terminal_this_nonzero_reward (x y : C) :
    (terminalSetoid ConflictOrganizationalSource.registeredModel).r x y ↔ x.1=y.1 :=
  ConflictOrganizationalSource.terminal_relation x y

theorem different_from_old_zero_reward :
    ConflictOrganizationalSource.registeredModel.reward≠registeredSurvivalModel.reward :=by
  intro h
  have hh:=congrArg (fun r=>r (true,false) false) h
  change (1:ℝ)=0 at hh
  norm_num at hh

theorem protected_same_reward_prevents_hidden_merge :
    ConflictOrganizationalSource.protectedModel.reward (true,true) false=1 ∧
    ¬(terminalSetoid ConflictOrganizationalSource.protectedModel).r (true,true) (true,false) :=by
  refine ⟨rfl,?_⟩
  rw [ConflictOrganizationalSource.protected_terminal_relation]
  decide

theorem actual_macro_subtype (x : C) :
    ConflictOrganizationalSource.reachableBoolEquiv (conflictRewardControl.f x)=x.1 :=
  ConflictOrganizationalSource.actual_macro_read x

def controller (x : C):Bool:=x.2
abbrev replica : Fin 3:=2
def damaged : C:=(false,false)

theorem source_supports :
    (ConflictOrganizationalSource.P damaged true).support=ConflictOrganizationalSource.K ∧
    (ConflictOrganizationalSource.P damaged false).support=ConflictOrganizationalSource.Kᶜ :=
  ⟨ConflictOrganizationalSource.true_action_support damaged,ConflictOrganizationalSource.false_action_support damaged⟩

theorem first_tick_is_program_only :
    (ConflictOrganizationalSource.jointStep (ConflictOrganizationalSource.corrupt damaged controller replica false)).map JointRepairState.physical=PMF.pure damaged :=
  ConflictOrganizationalSource.first_tick_physical_unchanged damaged controller replica false

theorem one_tick_not_physical_recovery :
    ¬StaysIn ((ConflictOrganizationalSource.jointStep (ConflictOrganizationalSource.corrupt damaged controller replica false)).map JointRepairState.physical) ConflictOrganizationalSource.K :=
  ConflictOrganizationalSource.damaged_not_safe_after_restore false controller replica false

theorem two_tick_same_actual_P :
    ((ConflictOrganizationalSource.jointStep (ConflictOrganizationalSource.corrupt damaged controller replica false)).bind ConflictOrganizationalSource.jointStep).map JointRepairState.physical=
    ConflictOrganizationalSource.M.transitionPMF damaged true :=
  ConflictOrganizationalSource.two_tick_physical_source damaged controller replica false

theorem second_tick_really_recovers :
    StaysIn ((ConflictOrganizationalSource.jointStep (ConflictOrganizationalSource.corrupt damaged controller replica false)).bind ConflictOrganizationalSource.jointStep)
      (RecoveredJointTarget ConflictOrganizationalSource.substrate ConflictOrganizationalSource.K true) :=
  ConflictOrganizationalSource.two_tick_recovered damaged controller replica false

theorem restored_program_not_resampled_bit :
    ConflictOrganizationalSource.substrate.execute true (true,false)=true ∧
    ConflictOrganizationalSource.substrate.execute true (true,true)=true ∧
    ((ConflictOrganizationalSource.jointStep (ConflictOrganizationalSource.corrupt damaged controller replica false)).bind ConflictOrganizationalSource.jointStep).map JointRepairState.physical (true,false)≠0 :=by
  refine ⟨rfl,rfl,?_⟩
  rw [ConflictOrganizationalSource.two_tick_physical_source]
  exact (PMF.mem_support_iff _ _).mp ((ConflictOrganizationalSource.transition_support damaged (true,false) true).mpr rfl)

def firstObservation : ∀n,CausalHistory Bool (Bool×Bool) n→Bool
  | 0 => fun y => y
  | n+1 => fun h => firstObservation n h.1

def policy (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) : ConflictOrganizationalSource.Posterior.ObservedPolicy:=
  fun n h=>if n=0 then ConflictParametricSource.actionLaw theta h0 h1 else PMF.pure (firstObservation n h)
abbrev theta : ℝ:=3/7
theorem h0 : 0≤theta:=by norm_num
theorem h1 : theta≤1:=by norm_num
abbrev pi:=policy theta h0 h1

theorem initial_history_positive :
    true∈(coarseLaw ConflictOrganizationalSource.Posterior.initial Prod.fst ConflictOrganizationalSource.Posterior.source pi 0).support :=by
  rw [mem_coarseLaw_zero_support_iff]
  exact ⟨(true,false),by simp [initialSupport,ConflictOrganizationalSource.Posterior.initial]⟩

theorem initial_false_is_empty :
    traceSupport ConflictOrganizationalSource.Posterior.initial Prod.fst ConflictOrganizationalSource.Posterior.source 0 false=∅ :=by
  ext x; rcases x with ⟨b,u⟩
  cases b <;> cases u <;> simp [traceSupport,initialSupport,ConflictOrganizationalSource.Posterior.initial]

theorem first_false_history_positive :
    (true,(false,false))∈(coarseLaw ConflictOrganizationalSource.Posterior.initial Prod.fst ConflictOrganizationalSource.Posterior.source pi 1).support :=by
  apply (mem_coarseLaw_succ_support_iff ConflictOrganizationalSource.Posterior.initial Prod.fst ConflictOrganizationalSource.Posterior.source pi 0 true false false).mpr
  refine ⟨initial_history_positive,?_,?_⟩
  · apply (PMF.mem_support_iff _ _).mpr
    intro hz
    have hr:=congrArg ENNReal.toReal hz
    change (ConflictParametricSource.actionLaw theta h0 h1 false).toReal=0 at hr
    rw [ConflictParametricSource.actionLaw_real] at hr
    norm_num [ConflictParametricSource.actionWeight,theta] at hr
  · refine ⟨(false,true),rfl,(true,false),?_,?_⟩
    · simp [traceSupport,initialSupport,ConflictOrganizationalSource.Posterior.initial]
    · exact (ConflictOrganizationalSource.transition_support (true,false) (false,true) false).mpr rfl

theorem actual_positive_posterior_fiber :
    (PosteriorSupportCoverageCheck.fiberTerminalPosterior
      (microLaw ConflictOrganizationalSource.Posterior.initial Prod.fst ConflictOrganizationalSource.Posterior.source pi 1)
      (projectHistory Prod.fst 1) (riskLastState 1) (true,(false,false)) first_false_history_positive).support=
      {x : C|x.1=false} :=
  ConflictOrganizationalSource.Posterior.actual_posterior_support pi 0 true false false first_false_history_positive

theorem zero_action_not_positive_history :
    (true,(false,false))∉(coarseLaw ConflictOrganizationalSource.Posterior.initial Prod.fst ConflictOrganizationalSource.Posterior.source
      (policy 0 (by norm_num) (by norm_num)) 1).support :=by
  intro hz
  have ha:=((mem_coarseLaw_succ_support_iff ConflictOrganizationalSource.Posterior.initial Prod.fst ConflictOrganizationalSource.Posterior.source
      (policy 0 (by norm_num) (by norm_num)) 0 true false false).mp hz).2.1
  apply (PMF.mem_support_iff _ _).mp ha
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) ENNReal.zero_ne_top).mp
  rw [ENNReal.toReal_zero]
  change (ConflictParametricSource.actionLaw 0 (by norm_num) (by norm_num) false).toReal=0
  rw [ConflictParametricSource.actionLaw_real];rfl

end
end IndependentConflictOrganizational
#print axioms IndependentConflictOrganizational.terminal_this_nonzero_reward
#print axioms IndependentConflictOrganizational.different_from_old_zero_reward
#print axioms IndependentConflictOrganizational.protected_same_reward_prevents_hidden_merge
#print axioms IndependentConflictOrganizational.actual_macro_subtype
#print axioms IndependentConflictOrganizational.source_supports
#print axioms IndependentConflictOrganizational.first_tick_is_program_only
#print axioms IndependentConflictOrganizational.one_tick_not_physical_recovery
#print axioms IndependentConflictOrganizational.two_tick_same_actual_P
#print axioms IndependentConflictOrganizational.second_tick_really_recovers
#print axioms IndependentConflictOrganizational.restored_program_not_resampled_bit
#print axioms IndependentConflictOrganizational.initial_history_positive
#print axioms IndependentConflictOrganizational.initial_false_is_empty
#print axioms IndependentConflictOrganizational.first_false_history_positive
#print axioms IndependentConflictOrganizational.actual_positive_posterior_fiber
#print axioms IndependentConflictOrganizational.zero_action_not_positive_history
