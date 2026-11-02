import UEOT
namespace IndependentConflictParametric
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly UEOT.V3.PathError
open SourcePolicyPathBridgeCheck
open scoped BigOperators
noncomputable section
abbrev C:=ConflictParametricSource.State
abbrev theta:ℝ:=3/7
theorem t0 : 0≤theta:=by norm_num
theorem t1 : theta≤1:=by norm_num

theorem actual_primitive (x y : C) (a : Bool) :
    (ConflictParametricSource.M.transitionPMF x a y).toReal=(if y.1=a then (1/2:ℝ) else 0) :=
  ConflictParametricSource.transition_real x a y

theorem three_sevenths_row (x y : C) :
    (ConflictParametricSource.closedRow theta t0 t1 x y).toReal=
      if y.1 then (2/7:ℝ) else 3/14 :=by
  rw [ConflictParametricSource.closedRow_real]
  cases hy : y.1 <;> norm_num [ConflictParametricSource.closedMatrix,theta,hy]

theorem same_original_closedrow (x : C) :
    policyTransitionPMF ConflictParametricSource.M (ConflictParametricSource.policy theta t0 t1) x=
      ConflictParametricSource.mu theta t0 t1 :=by
  rw [ConflictParametricSource.policyTransitionPMF_eq,ConflictParametricSource.closedRow_eq_mu]

theorem actual_safe_killed (u v : Bool) :
    ConflictParametricSource.killed theta u v=(2/7:ℝ) ∧
    ConflictParametricSource.killed theta u v=
      (ConflictParametricSource.closedRow theta t0 t1 (true,u) (true,v)).toReal :=by
  constructor
  · norm_num [ConflictParametricSource.killed_eq,theta]
  · exact ConflictParametricSource.killed_actual theta t0 t1 u v

-- The book policy is visible-history based. Full memory representation gains
-- NO information because every action law is constant even on zero histories.
def visiblePolicy (t : ℕ) (_ : CausalHistory Bool (Bool×Bool) t) : PMF Bool:=ConflictParametricSource.actionLaw theta t0 t1

theorem action_factors_any_visible_history {t : ℕ}
    (h : (ConflictParametricSource.causalPolicy theta t0 t1).Memory t)
    (v : CausalHistory Bool (Bool×Bool) t) (a : Bool) :
    (ConflictParametricSource.causalPolicy theta t0 t1).actionProb h a=(visiblePolicy t v a).toReal :=rfl

theorem actual_timezero_choice :
    (ConflictParametricSource.causalPolicy theta t0 t1).actionProb (t:=0) (true,false) false=3/7 ∧
    (visiblePolicy 0 true true).toReal=4/7 :=by
  constructor
  · change (ConflictParametricSource.actionLaw theta t0 t1 false).toReal=3/7
    rw [ConflictParametricSource.actionLaw_real]
    rfl
  · change (ConflictParametricSource.actionLaw theta t0 t1 true).toReal=4/7
    rw [ConflictParametricSource.actionLaw_real]
    norm_num [ConflictParametricSource.actionWeight,theta]

theorem endpoints_all_histories {t : ℕ}
    (h0 : (ConflictParametricSource.causalPolicy 0 (by norm_num) (by norm_num)).Memory t)
    (h1 : (ConflictParametricSource.causalPolicy 1 (by norm_num) (by norm_num)).Memory t) :
    (ConflictParametricSource.causalPolicy 0 (by norm_num) (by norm_num)).actionProb h0 false=0 ∧
    (ConflictParametricSource.causalPolicy 1 (by norm_num) (by norm_num)).actionProb h1 true=0 :=by
  constructor <;> rw [ConflictParametricSource.causalPolicy_action] <;> norm_num [ConflictParametricSource.actionWeight]

theorem endpoints_current_atoms :
    (ConflictParametricSource.mu 0 (by norm_num) (by norm_num) (true,false)).toReal=1/2 ∧
    (ConflictParametricSource.mu 0 (by norm_num) (by norm_num) (false,true)).toReal=0 ∧
    (ConflictParametricSource.mu 1 (by norm_num) (by norm_num) (true,false)).toReal=0 ∧
    (ConflictParametricSource.mu 1 (by norm_num) (by norm_num) (false,true)).toReal=1/2 :=by
  simp only [ConflictParametricSource.mu_real]
  norm_num

theorem original_reward_discount :
    ConflictParametricSource.M.reward (true,false) false=1 ∧
    ConflictParametricSource.M.reward (true,false) true=0 ∧
    ConflictParametricSource.M.discount=1/2 :=⟨rfl,rfl,rfl⟩
end
end IndependentConflictParametric
#print axioms IndependentConflictParametric.actual_primitive
#print axioms IndependentConflictParametric.three_sevenths_row
#print axioms IndependentConflictParametric.same_original_closedrow
#print axioms IndependentConflictParametric.actual_safe_killed
#print axioms IndependentConflictParametric.action_factors_any_visible_history
#print axioms IndependentConflictParametric.actual_timezero_choice
#print axioms IndependentConflictParametric.endpoints_all_histories
#print axioms IndependentConflictParametric.endpoints_current_atoms
#print axioms IndependentConflictParametric.original_reward_discount
