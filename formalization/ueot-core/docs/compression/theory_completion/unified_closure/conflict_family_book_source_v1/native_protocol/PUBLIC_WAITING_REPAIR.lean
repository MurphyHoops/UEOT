import UEOT
namespace IndependentWaitingRepair
open UEOT.V3.FiniteDiscountedControl UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.RecursiveSufficientState
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open WaitingRepairControl
noncomputable section

theorem actual_wait_hidden_fair :
 (M.transitionPMF (true,true) false (true,false)).toReal=3/8 ∧
 (M.transitionPMF (true,true) false (false,true)).toReal=1/8 :=by
 rw [actual_pmf,actual_pmf];norm_num [mass]
theorem actual_bad_wait_absorbs :
 (M.transitionPMF (false,true) false (false,false)).toReal=1/2 ∧
 (M.transitionPMF (false,true) false (true,true)).toReal=0 :=by
 rw [actual_pmf,actual_pmf];norm_num [mass]
theorem repair_certain_health_for_any_state (x : State) :
 (M.transitionPMF x true (true,true)).toReal=1/2 ∧
 (M.transitionPMF x true (false,false)).toReal=0 :=by
 rw [actual_pmf,actual_pmf];norm_num [mass]
theorem THIS_source_not_conflict :
 M.transition (true,true) false (true,false)≠ConflictParametricSource.M.transition (true,true) false (true,false) :=by
 rw [actual_transition,ConflictParametricSource.transition_eq];norm_num [mass]
theorem original_reward_discount :
 M.reward (true,true) false=1 ∧ M.reward (false,true) true=-1 ∧ M.discount=1/2 :=by
 rw [actual_reward,actual_reward,actual_discount];norm_num
theorem actual_optimal_values :
 M.optimalValue (true,true)=(8/5:ℝ) ∧ M.optimalValue (false,true)=0 :=by
 rw [optimal_value];norm_num [value]
theorem actual_two_q_gaps :
 M.qValue M.optimalValue (true,true) false=(8/5:ℝ) ∧
 M.qValue M.optimalValue (true,true) true=(4/5:ℝ) ∧
 M.qValue M.optimalValue (false,true) false=0 ∧
 M.qValue M.optimalValue (false,true) true=(-1/5:ℝ) :=by
 rw [optimal_value];simp [actual_q]
theorem actual_original_all_causal (pi : CausalPolicy State (fun _=>Bool)) {t : ℕ} (h : pi.Memory t) :
 CausalPolicy.infiniteValue pi M h≤value (pi.current h) :=dominates_all_causal pi h
theorem actual_original_greedy_attains :
 CausalPolicy.infiniteValue (greedyPolicy M) M (t:=7) (true,true)=(8/5:ℝ) :=by
 rw [actual_greedy_attains];norm_num [value]
def outsideRepair : viableSourceAction M K (false,true) :=⟨true,by simp [K]⟩
def outsideWait : viableSourceAction M K (false,true) :=⟨false,by simp [K]⟩
theorem outside_allowed_q_are_distinct :
 R.qValue R.optimalValue (false,true) outsideRepair=-1 ∧
 R.qValue R.optimalValue (false,true) outsideWait=0 :=by
 rw [restricted_optimal_zero,restricted_q_zero,restricted_q_zero];simp [outsideRepair,outsideWait]
theorem actual_safe_all_causal (pi : CausalPolicy State (viableSourceAction M K)) {t : ℕ} (h : pi.Memory t) :
 CausalPolicy.infiniteValue pi R h≤0 :=restricted_all_causal pi h
theorem actual_restricted_greedy_attains :
 CausalPolicy.infiniteValue (greedyPolicy R) R (t:=7) (true,true)=0 :=actual_safe_attainment _
theorem healthy_wait_really_fails :
 (M.transitionPMF (true,true) false (false,false)).toReal+
 (M.transitionPMF (true,true) false (false,true)).toReal=(1/4:ℝ) :=waiting_positive_failure true
theorem actual_safety_comparison :
 ¬StaysIn (M.transitionPMF (true,true) (M.greedyAction (true,true))) K ∧
 StaysIn (M.transitionPMF (true,true) (R.greedyAction (true,true)).val) K :=
 ⟨actual_unrestricted_greedy_not_safe true,actual_restricted_greedy_safe true⟩
theorem SAME_macro_value : control.macroModel.optimalValue (control.f (true,true))=(8/5:ℝ) :=by
 rw [actual_macro_optimal];norm_num [value]
theorem SAME_macro_reward (x : State) (a : Bool) :
 M.reward x a=control.macroModel.reward (control.f x) a :=actual_reward_quotient x a
theorem SAME_macro_transition (x : State) (a : Bool) (y : ReachableState (fun x : State=>x.1)) :
 fiberMass control.f (M.transition x a) y=control.macroModel.transition (control.f x) a y :=actual_transition_quotient x a y
end
#print axioms actual_wait_hidden_fair
#print axioms actual_bad_wait_absorbs
#print axioms repair_certain_health_for_any_state
#print axioms THIS_source_not_conflict
#print axioms original_reward_discount
#print axioms actual_optimal_values
#print axioms actual_two_q_gaps
#print axioms actual_original_all_causal
#print axioms actual_original_greedy_attains
#print axioms outside_allowed_q_are_distinct
#print axioms actual_safe_all_causal
#print axioms actual_restricted_greedy_attains
#print axioms healthy_wait_really_fails
#print axioms actual_safety_comparison
#print axioms SAME_macro_value
#print axioms SAME_macro_reward
#print axioms SAME_macro_transition
end IndependentWaitingRepair
