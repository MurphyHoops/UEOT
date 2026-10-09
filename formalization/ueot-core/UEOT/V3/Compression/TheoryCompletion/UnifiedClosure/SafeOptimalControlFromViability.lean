import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CorePMFViabilityReconciliation
import UEOT.V3.FiniteDiscountedCausalInfinite
import Mathlib.Tactic

/-!
# Safety-constrained Bellman control derived from the frozen PMF viability kernel

Given one finite controlled source and its proven viability fixed point,
state-dependent admissible actions are derived from actual source support.
The restricted control model uses literally the original transition and
reward on admissible actions. Its Bellman greedy controller preserves the
kernel, while the frozen causal-policy theorem proves optimality among
ALL history-dependent randomized policies obeying the same restriction.

This is constrained optimality, not unconstrained GOA optimality or physical
autopoiesis. Outside the viable set the action restriction is vacuous.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.ViabilityKernel
open CausalPolicy

universe uX uA

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A] [Nonempty A]

/-- At a viable microstate, only actions whose original PMF stays in K
are admissible. Outside K no support restriction is imposed. -/
def viableSourceAction (M : Model X (fun _ => A)) (K : Set X) (x : X) :=
  {a : A // x ∈ K → StaysIn (M.transitionPMF x a) K}

noncomputable instance viableSourceActionFintype
    (M : Model X (fun _ => A)) (K : Set X) (x : X) :
    Fintype (viableSourceAction M K x) := by
  classical
  unfold viableSourceAction
  infer_instance

/-- A fixed source viability kernel supplies the restricted-action
nonemptiness certificate; no safe controller is assumed as input. -/
theorem exists_viable_source_action
    (M : Model X (fun _ => A)) (K : Set X)
    (hfix : viabilityStep (fun x a => M.transitionPMF x a) K = K)
    (x : X) : Nonempty (viableSourceAction M K x) := by
  classical
  by_cases hx : x ∈ K
  · have hstep : x ∈ viabilityStep (fun x a => M.transitionPMF x a) K := by
      rw [hfix]
      exact hx
    obtain ⟨_, a, ha⟩ := hstep
    exact ⟨⟨a, fun _ => ha⟩⟩
  · exact ⟨⟨Classical.choice (inferInstance : Nonempty A),
      fun h => False.elim (hx h)⟩⟩

/-- A state-dependent control model restricted to proven viable actions.
Both rewards and microscopic transitions come from the *same* source M. -/
noncomputable def viableRestrictedModel
    (M : Model X (fun _ => A)) (K : Set X)
    (hfix : viabilityStep (fun x a => M.transitionPMF x a) K = K) :
    Model X (viableSourceAction M K) := by
  letI : ∀ x, Nonempty (viableSourceAction M K x) :=
    fun x => exists_viable_source_action M K hfix x
  exact {
    transition := fun x a y => M.transition x a.1 y
    reward := fun x a => M.reward x a.1
    rewardBound := M.rewardBound
    discount := M.discount
    transition_nonneg := fun x a y => M.transition_nonneg x a.1 y
    transition_sum_one := fun x a => M.transition_sum_one x a.1
    reward_abs_le := fun x a => M.reward_abs_le x a.1
    discount_pos := M.discount_pos
    discount_lt_one := M.discount_lt_one
  }

/-- The restricted Bellman optimum is safe on K. -/
theorem viable_restricted_greedy_preserves_source_kernel
    (M : Model X (fun _ => A)) (K : Set X)
    (hfix : viabilityStep (fun x a => M.transitionPMF x a) K = K) :
    letI : ∀ x, Nonempty (viableSourceAction M K x) :=
      fun x => exists_viable_source_action M K hfix x
    let R := viableRestrictedModel M K hfix
    ∀ x ∈ K, StaysIn (M.transitionPMF x (R.greedyAction x).1) K := by
  letI : ∀ x, Nonempty (viableSourceAction M K x) :=
    fun x => exists_viable_source_action M K hfix x
  dsimp only
  intro x hx
  exact ((viableRestrictedModel M K hfix).greedyAction x).property hx

/-- The source-derived safety constraint still permits full Bellman
optimization over every causal randomized history policy of that model. -/
theorem viable_restricted_optimal_dominates_all_causal_policies
    (M : Model X (fun _ => A)) (K : Set X)
    (hfix : viabilityStep (fun x a => M.transitionPMF x a) K = K) :
    letI : ∀ x, Nonempty (viableSourceAction M K x) :=
      fun x => exists_viable_source_action M K hfix x
    let R := viableRestrictedModel M K hfix
    ∀ (π : CausalPolicy X (viableSourceAction M K)) {t : ℕ}
      (h : π.Memory t),
        infiniteValue π R h ≤ R.optimalValue (π.current h) := by
  letI : ∀ x, Nonempty (viableSourceAction M K x) :=
    fun x => exists_viable_source_action M K hfix x
  dsimp only
  intro π t h
  exact CausalPolicy.infiniteValue_le_optimal π
    (viableRestrictedModel M K hfix) h

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
