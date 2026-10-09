import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictiveViabilityTransport
import Mathlib.Tactic

/-!
# UMC: composable multi-scale finite stochastic control hierarchy

Two real P-QUO-01 exact controlled quotients X -> Y and Y -> Z compose to
a new exact controlled quotient X -> Z, PROVIDED the middle finite-control
model is literally the same (or explicitly proved equal) in both legs.

No independently asserted source-to-top transition closure or reward closure
is needed. The proof uses the EXISTING frozen expectation intertwining for
the lower leg and transition-closure for the upper leg. It is a mathematical
two-stage cross-scale tower, not merely a set-theoretic composition of maps.

This respects P9 scale typing, but does not identify an Object-RG process
with Wilsonian RG or supply biological continuity/identity semantics.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteDiscountedControl
open CausalPolicy

universe uX uY uZ uA

/-- The exact finite discounted control quotient interface is closed under
typed multi-level composition with an explicitly reconciled middle world.
The source-to-top Markov, reward and discount conditions are DERIVED. -/
noncomputable def composeExactControlQuotients
    {X : Type uX} {Y : Type uY} {Z : Type uZ} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype A] [Nonempty A]
    (lower : ExactControlQuotient X Y (fun _ => A))
    (upper : ExactControlQuotient Y Z (fun _ => A))
    (hmiddle : lower.macroModel = upper.micro) :
    ExactControlQuotient X Z (fun _ => A) := by
  classical
  refine {
    f := upper.f ∘ lower.f
    surjective := ?_
    micro := lower.micro
    macroModel := upper.macroModel
    discount_eq := ?_
    reward_closed := ?_
    transition_closed := ?_
  }
  · intro z
    obtain ⟨y, hy⟩ := upper.surjective z
    obtain ⟨x, hx⟩ := lower.surjective y
    exact ⟨x, by simp [Function.comp_apply, hx, hy]⟩
  · calc
      lower.micro.discount = lower.macroModel.discount :=
        lower.discount_eq
      _ = upper.micro.discount := by rw [hmiddle]
      _ = upper.macroModel.discount := upper.discount_eq
  · intro x a
    change lower.micro.reward x a =
      upper.macroModel.reward (upper.f (lower.f x)) a
    calc
      lower.micro.reward x a =
        lower.macroModel.reward (lower.f x) a :=
          lower.reward_closed x a
      _ = upper.micro.reward (lower.f x) a := by rw [hmiddle]
      _ = upper.macroModel.reward (upper.f (lower.f x)) a :=
        upper.reward_closed (lower.f x) a
  · intro x a z
    change fiberMass (upper.f ∘ lower.f)
      (lower.micro.transition x a) z =
        upper.macroModel.transition (upper.f (lower.f x)) a z
    let indicator : Y → ℝ :=
      fun y => if upper.f y = z then 1 else 0
    have hfirst := lower.expect_pullback x a indicator
    calc
      fiberMass (upper.f ∘ lower.f)
          (lower.micro.transition x a) z =
        lower.micro.expect x a (lower.pullback indicator) := by
          unfold fiberMass Model.expect ExactControlQuotient.pullback indicator
          apply Finset.sum_congr rfl
          intro y _
          by_cases h : upper.f (lower.f y) = z <;>
            simp [Function.comp_apply, h]
      _ = lower.macroModel.expect (lower.f x) a indicator := hfirst
      _ = upper.micro.expect (lower.f x) a indicator := by rw [hmiddle]
      _ = fiberMass upper.f
          (upper.micro.transition (lower.f x) a) z := by
          unfold fiberMass Model.expect indicator
          apply Finset.sum_congr rfl
          intro y _
          by_cases h : upper.f y = z <;> simp [h]
      _ = upper.macroModel.transition (upper.f (lower.f x)) a z :=
        upper.transition_closed (lower.f x) a z

/-- The inherited full causal-optimal control proof is true directly on the
original MICRO state and the ultimate macro state; NO separately supplied
micro-top-level quotient contract or optimality conclusion. -/
theorem composed_scale_tower_optimal_value_and_causal_control
    {X : Type uX} {Y : Type uY} {Z : Type uZ} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype A] [Nonempty A]
    (lower : ExactControlQuotient X Y (fun _ => A))
    (upper : ExactControlQuotient Y Z (fun _ => A))
    (hmiddle : lower.macroModel = upper.micro) :
    let tower := composeExactControlQuotients lower upper hmiddle
    (∀ x : X,
      tower.micro.optimalValue x =
        tower.macroModel.optimalValue (tower.f x)) ∧
    (∀ x : X, ∀ a : A,
      tower.micro.qValue tower.micro.optimalValue x a =
        tower.macroModel.qValue tower.macroModel.optimalValue
          (tower.f x) a) := by
  let tower := composeExactControlQuotients lower upper hmiddle
  exact ⟨tower.optimalValue_apply, tower.optimal_qValue_pullback⟩

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
