import UEOT.V3.Compression.TheoryCompletion.GOD

/-!
# P2 audit boundary — state-path laws do not determine teleological action value

An adapter from control policies to teleological futures must not silently
forget action/reward information.  Equal physical state-transition rows can
still correspond to different rewards and therefore different Bellman action
values.

This no-go is why P2 does not identify policy futures with bare state-path laws.
A stronger path-grounding construction, if introduced later, must retain
state-action or reward-marked trajectory information.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open UEOT.V3.FiniteDiscountedControl

/-- A one-state model in which both actions induce exactly the same physical
state transition but carry different rewards. -/
noncomputable def statePathBlindTeleologyModel :
    Model Unit (fun _ => Bool) where
  transition := fun _ _ _ => 1
  reward := fun _ a => if a then 1 else 0
  rewardBound := 1
  discount := 1 / 2
  transition_nonneg := by
    intro _ _ _
    norm_num
  transition_sum_one := by
    intro _ _
    simp
  reward_abs_le := by
    intro _ a
    cases a <;> norm_num
  discount_pos := by
    norm_num
  discount_lt_one := by
    norm_num

/-- The two actions are physically indistinguishable at the state-transition
level. -/
theorem statePathBlindTeleologyModel_same_transition :
    ∀ y : Unit,
      statePathBlindTeleologyModel.transition () false y =
        statePathBlindTeleologyModel.transition () true y := by
  intro y
  cases y
  rfl

/-- Nevertheless the same two actions are teleologically distinguishable by
the control reward. -/
theorem statePathBlindTeleologyModel_reward_ne :
    statePathBlindTeleologyModel.reward () false ≠
      statePathBlindTeleologyModel.reward () true := by
  norm_num [statePathBlindTeleologyModel]

/-- Equal physical transition rows do not force equal Bellman action values
when action-level teleological information differs.  Thus a future-grounding
adapter that retains only the state path law is too weak in general. -/
theorem statePathBlindTeleologyModel_qValue_ne
    (v : Unit → ℝ) :
    statePathBlindTeleologyModel.qValue v () false ≠
      statePathBlindTeleologyModel.qValue v () true := by
  simp [Model.qValue, Model.expect, statePathBlindTeleologyModel]

end UEOT.V3.Compression.TheoryCompletion
