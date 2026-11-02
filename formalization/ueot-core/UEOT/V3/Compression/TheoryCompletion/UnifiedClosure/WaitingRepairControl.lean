import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SafeRewardConflictWitness
import UEOT.V3.FiniteDiscountedGreedy

/-!
Original promise: book section35.4 waiting/repair separates safe optimality from unrestricted optimality on its OWN source.
Existing results: finite discounted Bellman uniqueness, arbitrary causal comparison, and source-derived viableRestrictedModel.
Reduced premise: construct the stated actual4-state source and prove8/5/0 values and the real admissible actions.
Family: State=(health,hidden) Bool², hidden independently fair, waiting survival3/4, repair certain health, rewardhealth-action, discount1/2.
Consumers: actual unrestricted/restricted Bellman policies, exact visible control quotient and nonzero healthy waiting failure.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.WaitingRepairControl

open UEOT.V3.FiniteDiscountedControl UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.RecursiveSufficientState
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open scoped BigOperators
noncomputable section

abbrev State := Bool × Bool

def mass (x : State) (a : Bool) (y : State) : ℝ :=
  if a then (if y.1 then 1/2 else 0)
  else if x.1 then (if y.1 then 3/8 else 1/8)
  else if y.1 then 0 else 1/2

def kernel : FiniteControlledStochasticKernel State Bool where
  mass := mass
  nonneg := by intro x a y; rcases x with ⟨s,z⟩; rcases y with ⟨b,u⟩; cases s <;> cases a <;> cases b <;> norm_num [mass]
  normalized := by intro x a; rcases x with ⟨s,z⟩; cases s <;> cases a <;> norm_num [mass,Fintype.sum_prod_type]

theorem visible_strong_lumpable : StrongLumpability kernel (fun x : State => x.1) := by
  intro x y h a c
  cases x with
  | mk s z =>
    cases y with
    | mk t u =>
      change s=t at h
      subst t
      rfl

def control : ExactControlQuotient State (ReachableState (fun x : State => x.1)) (fun _ => Bool) :=
  exactControlFromStochasticQuotient kernel (fun x : State=>x.1) visible_strong_lumpable
    (fun s a => (if s.val then (1 : ℝ) else 0)-(if a then 1 else 0))
    1 (1/2)
    (by intro s a; cases h : s.val <;> cases a <;> norm_num [h])
    (by norm_num) (by norm_num)

def M := control.micro

theorem actual_transition (x : State) (a : Bool) (y : State) : M.transition x a y=mass x a y := rfl
theorem actual_pmf (x : State) (a : Bool) (y : State) : (M.transitionPMF x a y).toReal=mass x a y := by
  rw [Model.transitionPMF_apply_toReal,actual_transition]
theorem actual_reward (x : State) (a : Bool) :
    M.reward x a=(if x.1 then (1 : ℝ) else 0)-(if a then 1 else 0) := rfl
theorem actual_discount : M.discount=(1/2 : ℝ) := rfl

def K : Set State := {x | x.1=true}
def value (x : State) : ℝ := if x.1 then 8/5 else 0

theorem actual_q (x : State) (a : Bool) : M.qValue value x a=
    if x.1 then (if a then (4/5 : ℝ) else 8/5) else (if a then -1/5 else 0) := by
  rcases x with ⟨s,z⟩
  cases s <;> cases a <;> norm_num [Model.qValue,Model.expect,actual_transition,actual_reward,actual_discount,
    value,mass,Fintype.sum_prod_type]

theorem optimal_value : M.optimalValue=value := by
  apply Eq.symm
  apply M.fixedPoint_unique
  funext x
  unfold Model.bellman
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    rw [actual_q]
    cases hb : x.1 <;> cases a <;> norm_num [value,hb]
  · have hh:=Finset.le_sup' (fun a : Bool=>M.qValue value x a) (Finset.mem_univ false)
    rw [actual_q] at hh
    have he : (if x.1 then (8/5 : ℝ) else 0)=value x := rfl
    simpa only [Bool.false_eq_true,if_false,he] using hh

theorem unique_optimal_action (x : State) (a : Bool) :
    M.qValue M.optimalValue x a=M.optimalValue x ↔ a=false := by
  rw [optimal_value,actual_q]
  cases hb : x.1 <;> cases a <;> norm_num [value,hb]

theorem greedy_waits (x : State) : M.greedyAction x=false :=
  (unique_optimal_action x (M.greedyAction x)).mp (M.greedyAction_spec x)

theorem dominates_all_causal (pi : CausalPolicy State (fun _ => Bool)) {t : ℕ} (h : pi.Memory t) :
    CausalPolicy.infiniteValue pi M h≤value (pi.current h) := by
  simpa only [optimal_value] using CausalPolicy.infiniteValue_le_optimal pi M h

theorem actual_greedy_attains {t : ℕ} (x : State) :
    CausalPolicy.infiniteValue (greedyPolicy M) M (t:=t) x=value x := by
  rw [greedy_infiniteValue_eq_optimal,optimal_value]

theorem actual_macro_optimal (x : State) :
    control.macroModel.optimalValue (control.f x)=value x :=
  (control.optimalValue_apply x).symm.trans (congrFun optimal_value x)

theorem actual_reward_quotient (x : State) (a : Bool) :
    M.reward x a=control.macroModel.reward (control.f x) a := control.reward_closed x a

theorem actual_transition_quotient (x : State) (a : Bool)
    (y : ReachableState (fun x : State=>x.1)) :
    fiberMass control.f (M.transition x a) y=control.macroModel.transition (control.f x) a y :=
  control.transition_closed x a y

theorem source_stays_iff (x : State) (a : Bool) : StaysIn (M.transitionPMF x a) K ↔ a=true := by
  change StaysIn (M.transitionPMF x a) {y | y.1=true} ↔ a=true
  rw [frozen_pmf_staysIn_iff_real_zero_outside]
  constructor
  · intro hh
    cases a with
    | false =>
      have hz:=hh (false,false) (by simp)
      rw [actual_transition] at hz
      cases hb : x.1 <;> norm_num [mass,hb] at hz
    | true => rfl
  · intro ha y hy
    subst a
    rcases y with ⟨b,u⟩
    cases b with
    | false => simp [actual_transition,mass]
    | true => exact False.elim (hy rfl)

theorem actual_viability_fixed : viabilityStep (fun x a=>M.transitionPMF x a) K=K := by
  apply Set.Subset.antisymm (viabilityStep_subset _ _)
  intro x hx
  exact ⟨hx,true,(source_stays_iff x true).2 rfl⟩

instance restrictedNonempty (x : State) : Nonempty (viableSourceAction M K x) :=
  exists_viable_source_action M K actual_viability_fixed x

def R := viableRestrictedModel M K actual_viability_fixed

theorem actual_allowed_iff (x : State) (a : Bool) :
    (x∈K → StaysIn (M.transitionPMF x a) K) ↔ (x.1=true → a=true) := by
  change (x.1=true → StaysIn (M.transitionPMF x a) K) ↔ _
  rw [source_stays_iff]

def safeSelector (x : State) : viableSourceAction M K x :=⟨x.1,fun hx=>(source_stays_iff x x.1).2 hx⟩

theorem restricted_q_zero (x : State) (a : viableSourceAction M K x) :
    R.qValue (fun _=>0) x a=(if x.1 then (1 : ℝ) else 0)-(if a.val then 1 else 0) := by
  simp [Model.qValue,Model.expect,R,viableRestrictedModel,actual_reward]

theorem restricted_optimal_zero : R.optimalValue=fun _=>0 := by
  apply Eq.symm
  apply R.fixedPoint_unique
  funext x
  unfold Model.bellman
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    rw [restricted_q_zero]
    have hs:=(actual_allowed_iff x a.val).mp a.property
    cases hb : x.1 with
    | false => cases a.val <;> norm_num
    | true => rw [hs hb];norm_num
  · have hh:=Finset.le_sup' (fun a : viableSourceAction M K x=>R.qValue (fun _=>0) x a)
      (Finset.mem_univ (safeSelector x))
    rw [restricted_q_zero] at hh
    change ((if x.1 then (1 : ℝ) else 0)-(if x.1 then 1 else 0))≤_ at hh
    simpa only [sub_self] using hh

theorem restricted_greedy (x : State) : (R.greedyAction x).val=x.1 := by
  have hh:=R.greedyAction_spec x
  rw [restricted_optimal_zero,restricted_q_zero] at hh
  cases hb : x.1 <;> cases ha : (R.greedyAction x).val <;> simp_all

theorem restricted_optimal_action_iff (x : State) (a : viableSourceAction M K x) :
    R.qValue R.optimalValue x a=R.optimalValue x ↔ a.val=x.1 := by
  rw [restricted_optimal_zero,restricted_q_zero]
  cases hb : x.1 <;> cases ha : a.val <;> norm_num [hb,ha]

theorem restricted_all_causal (pi : CausalPolicy State (viableSourceAction M K)) {t : ℕ} (h : pi.Memory t) :
    CausalPolicy.infiniteValue pi R h≤0 := by
  simpa only [restricted_optimal_zero] using CausalPolicy.infiniteValue_le_optimal pi R h

theorem actual_safe_attainment {t : ℕ} (x : State) :
    CausalPolicy.infiniteValue (greedyPolicy R) R (t:=t) x=0 := by
  rw [greedy_infiniteValue_eq_optimal,restricted_optimal_zero]

theorem waiting_positive_failure (u : Bool) :
    (M.transitionPMF (true,u) false (false,false)).toReal+
      (M.transitionPMF (true,u) false (false,true)).toReal=(1/4 : ℝ) := by
  rw [actual_pmf,actual_pmf]
  norm_num [mass]

theorem actual_unrestricted_greedy_not_safe (u : Bool) :
    ¬StaysIn (M.transitionPMF (true,u) (M.greedyAction (true,u))) K := by
  rw [greedy_waits,source_stays_iff]
  decide

theorem actual_restricted_greedy_safe (u : Bool) :
    StaysIn (M.transitionPMF (true,u) (R.greedyAction (true,u)).val) K := by
  rw [restricted_greedy,source_stays_iff]

theorem healthy_values_differ (u : Bool) : M.optimalValue (true,u)=(8/5 : ℝ) ∧ R.optimalValue (true,u)=0 := by
  rw [optimal_value,restricted_optimal_zero]
  norm_num [value]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.WaitingRepairControl
