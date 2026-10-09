import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SafeOptimalControlFromViability
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViabilityNonvacuityWitness
import Mathlib.Tactic

/-!
# Nonzero reward and genuine survival conflict on one micro process

A 4-state two-action stochastic controlled source has positive reward for
the action that leaves the visible-safe region, and zero reward for the
action that preserves it. The kernel is identical to the already-proved
non-Dirac source, and the reward is a real registered objective.
The exact PMF fixed-point gives an admissible restricted Bellman model.

This witnesses competing rewards and survival; it does NOT assert a
full numerical comparison of unrestricted and restricted optimal values.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.RecursiveSufficientState

noncomputable instance (priority := 2000) conflictVisibleReachableFintype :
    Fintype (ReachableState (fun x : Bool × Bool => x.1)) := Fintype.ofFinite _

noncomputable def conflictRewardControl :
    ExactControlQuotient (Bool × Bool)
      (ReachableState (fun x : Bool × Bool => x.1))
      (fun _ => Bool) := by
  classical
  exact exactControlFromStochasticQuotient survivalMicroKernel
    (fun x : Bool × Bool => x.1)
    survivalRead_strongLumpable
    (fun _ (a : Bool) => if a then (0 : ℝ) else 1)
    1 (1/2)
    (by intro c a; cases a <;> norm_num)
    (by norm_num) (by norm_num)

def conflictSurvivalRegion : Set (Bool × Bool) :=
  {x | x.1 = true}

/-- The same real stochastic source offers the tempting high immediate
reward action false, but it has strictly positive probability of leaving
the safe region; action true stays inside and has lower reward. -/
theorem conflict_same_source_reward_and_risk :
    conflictRewardControl.micro.reward (true,false) false = 1 ∧
    conflictRewardControl.micro.reward (true,false) true = 0 ∧
    conflictRewardControl.micro.transition (true,false) false (false,false) = 1/2 ∧
    conflictRewardControl.micro.transition (true,false) true (false,false) = 0 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · change survivalMicroKernel.mass (true,false) false (false,false) = 1/2
    norm_num [survivalMicroKernel]
  · change survivalMicroKernel.mass (true,false) true (false,false) = 0
    norm_num [survivalMicroKernel]

/-- Unlike a vacuous empty-kernel case, visible true is a nonempty
source-controlled-invariant region even with the conflicting reward. -/
theorem conflict_region_is_actual_pmf_viability_fixed :
    viabilityStep
      (fun x a => conflictRewardControl.micro.transitionPMF x a)
      conflictSurvivalRegion = conflictSurvivalRegion := by
  apply Set.Subset.antisymm (viabilityStep_subset _ _)
  intro x hx
  refine ⟨hx, true, ?_⟩
  apply (frozen_pmf_staysIn_iff_real_zero_outside
    conflictRewardControl.micro conflictSurvivalRegion x true).2
  intro y hy
  change survivalMicroKernel.mass x true y = 0
  rcases x with ⟨bx, hxbit⟩
  rcases y with ⟨b, hybit⟩
  cases b with
  | false => simp [survivalMicroKernel]
  | true =>
      exfalso
      exact hy (by rfl)

/-- A nonempty safe optimum exists for the same source with nonzero,
conflicting reward; its certified Bellman selector stays in the real
source viability kernel. -/
theorem conflict_nonzero_reward_safe_bellman_preserves :
    let M := conflictRewardControl.micro
    let K := conflictSurvivalRegion
    letI : ∀ x, Nonempty (viableSourceAction M K x) :=
      fun x => exists_viable_source_action M K
        conflict_region_is_actual_pmf_viability_fixed x
    let R := viableRestrictedModel M K
      conflict_region_is_actual_pmf_viability_fixed
    ∀ h : Bool,
      StaysIn (M.transitionPMF (true,h) (R.greedyAction (true,h)).1) K := by
  letI : ∀ x, Nonempty (viableSourceAction conflictRewardControl.micro conflictSurvivalRegion x) :=
    fun x => exists_viable_source_action conflictRewardControl.micro conflictSurvivalRegion
      conflict_region_is_actual_pmf_viability_fixed x
  dsimp only
  intro h
  exact viable_restricted_greedy_preserves_source_kernel
    conflictRewardControl.micro conflictSurvivalRegion
    conflict_region_is_actual_pmf_viability_fixed (true,h) rfl

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
