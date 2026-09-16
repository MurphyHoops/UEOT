import UEOT.V3.FiniteDiscountedSelector
import Mathlib.Tactic

/-!
# P-QUO-01 — exact finite discounted control quotients

This module formalizes the frozen exact-control quotient interface on top of the
counted P-CTL-01 finite discounted-control foundation.

The micro admissible action type at `x` is definitionally the macro action type
at `f x`.  Thus the source clause "the admissible action set is the same on each
fibre" is represented without an auxiliary action transport.  Reward closure
and all-action transition pushforward closure are explicit structure fields.
They imply expectation, Q-value and Bellman intertwining, hence exact pullback
of the unique optimal value.  Finally, any macro stationary argmax selector is
lifted to a micro stationary policy whose infinite discounted value is optimal
against the full causal history-dependent randomized policy class.
-/

namespace UEOT.V3.FiniteDiscountedControl

open CausalPolicy

universe uX uY uA

variable {X : Type uX} [Fintype X]
variable {Y : Type uY} [Fintype Y]
variable {Abar : Y → Type uA} [∀ y, Fintype (Abar y)] [∀ y, Nonempty (Abar y)]

/-- Probability mass of a finite row on one fibre of `f`.  Classical finite
membership is hidden inside this noncomputable helper rather than exposed as a
source assumption. -/
noncomputable def fiberMass (f : X → Y) (p : X → ℝ) (y : Y) : ℝ := by
  classical
  exact ∑ x : X, if f x = y then p x else 0

/-- Exact control quotient data for the frozen P-QUO-01 finite model.

`micro` uses the action family `x ↦ Abar (f x)` definitionally, so states in one
fibre literally share the same admissible action type. -/
structure ExactControlQuotient (X : Type uX) [Fintype X]
    (Y : Type uY) [Fintype Y]
    (Abar : Y → Type uA) [∀ y, Fintype (Abar y)] [∀ y, Nonempty (Abar y)] where
  f : X → Y
  surjective : Function.Surjective f
  micro : Model X (fun x => Abar (f x))
  macroModel : Model Y Abar
  discount_eq : micro.discount = macroModel.discount
  reward_closed : ∀ x (a : Abar (f x)),
    micro.reward x a = macroModel.reward (f x) a
  transition_closed : ∀ x (a : Abar (f x)) (y : Y),
    fiberMass f (micro.transition x a) y = macroModel.transition (f x) a y

namespace ExactControlQuotient

variable (Q : ExactControlQuotient X Y Abar)

/-- Pull a macro value function back along the quotient map. -/
def pullback (v : Y → ℝ) : X → ℝ := fun x => v (Q.f x)

@[simp] theorem pullback_apply (v : Y → ℝ) (x : X) :
    Q.pullback v x = v (Q.f x) := rfl

/-- All-action pushforward closure implies exact equality of one-step
expectations on pulled-back macro value functions. -/
theorem expect_pullback (x : X) (a : Abar (Q.f x)) (v : Y → ℝ) :
    Q.micro.expect x a (Q.pullback v) = Q.macroModel.expect (Q.f x) a v := by
  classical
  simp only [Model.expect, pullback]
  calc
    (∑ x' : X, Q.micro.transition x a x' * v (Q.f x')) =
        ∑ x' : X, ∑ y : Y,
          if Q.f x' = y then Q.micro.transition x a x' * v y else 0 := by
      apply Finset.sum_congr rfl
      intro x' hx
      simp
    _ = ∑ y : Y, ∑ x' : X,
          if Q.f x' = y then Q.micro.transition x a x' * v y else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ y : Y,
          fiberMass Q.f (Q.micro.transition x a) y * v y := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [fiberMass]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x' hx
      by_cases hxy : Q.f x' = y <;> simp [hxy]
    _ = ∑ y : Y, Q.macroModel.transition (Q.f x) a y * v y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Q.transition_closed x a y]
    _ = Q.macroModel.expect (Q.f x) a v := rfl

/-- Reward closure, common discount and transition pushforward closure give
exact action-value intertwining. -/
theorem qValue_pullback (x : X) (a : Abar (Q.f x)) (v : Y → ℝ) :
    Q.micro.qValue (Q.pullback v) x a =
      Q.macroModel.qValue v (Q.f x) a := by
  simp only [Model.qValue]
  rw [Q.reward_closed x a, Q.discount_eq, Q.expect_pullback x a v]

/-- Frozen-source Bellman intertwining:
`T (vbar ∘ f) = (Tbar vbar) ∘ f`. -/
theorem bellman_pullback (v : Y → ℝ) :
    Q.micro.bellman (Q.pullback v) = Q.pullback (Q.macroModel.bellman v) := by
  funext x
  simp only [Model.bellman, pullback]
  have hfun :
      (fun a : Abar (Q.f x) => Q.micro.qValue (Q.pullback v) x a) =
        (fun a : Abar (Q.f x) => Q.macroModel.qValue v (Q.f x) a) := by
    funext a
    exact Q.qValue_pullback x a v
  exact congrArg
    (fun g : Abar (Q.f x) → ℝ =>
      (Finset.univ : Finset (Abar (Q.f x))).sup' Finset.univ_nonempty g)
    hfun

/-- The macro Bellman fixed point pulls back to the unique micro Bellman fixed
point. -/
theorem optimalValue_pullback :
    Q.micro.optimalValue = Q.pullback Q.macroModel.optimalValue := by
  symm
  apply Q.micro.fixedPoint_unique
  calc
    Q.micro.bellman (Q.pullback Q.macroModel.optimalValue) =
        Q.pullback (Q.macroModel.bellman Q.macroModel.optimalValue) :=
      Q.bellman_pullback Q.macroModel.optimalValue
    _ = Q.pullback Q.macroModel.optimalValue := by
      rw [Q.macroModel.optimalValue_fixed]

@[simp] theorem optimalValue_apply (x : X) :
    Q.micro.optimalValue x = Q.macroModel.optimalValue (Q.f x) :=
  congrFun Q.optimalValue_pullback x

/-- Optimal action values agree actionwise across the exact quotient. -/
theorem optimal_qValue_pullback (x : X) (a : Abar (Q.f x)) :
    Q.micro.qValue Q.micro.optimalValue x a =
      Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a := by
  rw [Q.optimalValue_pullback]
  exact Q.qValue_pullback x a Q.macroModel.optimalValue

/-- Lift a macro stationary selector to the micro state space. -/
def liftSelector (σbar : ∀ y, Abar y) : ∀ x, Abar (Q.f x) :=
  fun x => σbar (Q.f x)

@[simp] theorem liftSelector_apply (σbar : ∀ y, Abar y) (x : X) :
    Q.liftSelector σbar x = σbar (Q.f x) := rfl

/-- Any macro selector that attains the macro Bellman optimum remains
pointwise Bellman-optimal after lifting. -/
theorem liftSelector_optimal_actionwise (σbar : ∀ y, Abar y)
    (hσbar : ∀ y,
      Q.macroModel.qValue Q.macroModel.optimalValue y (σbar y) =
        Q.macroModel.optimalValue y) :
    ∀ x,
      Q.micro.qValue Q.micro.optimalValue x (Q.liftSelector σbar x) =
        Q.micro.optimalValue x := by
  intro x
  calc
    Q.micro.qValue Q.micro.optimalValue x (Q.liftSelector σbar x) =
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) (σbar (Q.f x)) :=
      Q.optimal_qValue_pullback x (Q.liftSelector σbar x)
    _ = Q.macroModel.optimalValue (Q.f x) := hσbar (Q.f x)
    _ = Q.micro.optimalValue x := (Q.optimalValue_apply x).symm

/-- A lifted macro argmax selector attains the micro optimal value for every
state and external causal time. -/
theorem liftSelector_infiniteValue_eq_optimal (σbar : ∀ y, Abar y)
    (hσbar : ∀ y,
      Q.macroModel.qValue Q.macroModel.optimalValue y (σbar y) =
        Q.macroModel.optimalValue y)
    {t : ℕ} (x : X) :
    infiniteValue (selectorPolicy (Q.liftSelector σbar)) Q.micro (t := t) x =
      Q.micro.optimalValue x := by
  exact selector_infiniteValue_eq_optimal Q.micro (Q.liftSelector σbar)
    (Q.liftSelector_optimal_actionwise σbar hσbar) (t := t) x

/-- A lifted macro argmax selector is micro-optimal against the entire causal
history-dependent randomized policy class. -/
theorem liftSelector_optimal_against_all_causal (σbar : ∀ y, Abar y)
    (hσbar : ∀ y,
      Q.macroModel.qValue Q.macroModel.optimalValue y (σbar y) =
        Q.macroModel.optimalValue y) :
    (∀ {t : ℕ} (x : X),
      infiniteValue (selectorPolicy (Q.liftSelector σbar)) Q.micro (t := t) x =
        Q.micro.optimalValue x) ∧
    (∀ (π : CausalPolicy X (fun x => Abar (Q.f x))) {t : ℕ} (h : π.Memory t),
      infiniteValue π Q.micro h ≤ Q.micro.optimalValue (π.current h)) := by
  exact selector_optimal_against_all_causal Q.micro (Q.liftSelector σbar)
    (Q.liftSelector_optimal_actionwise σbar hσbar)

/-- The canonical macro greedy selector lifts to a micro-optimal policy. -/
theorem macroGreedy_lift_optimal :
    (∀ {t : ℕ} (x : X),
      infiniteValue (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
        Q.micro (t := t) x = Q.micro.optimalValue x) ∧
    (∀ (π : CausalPolicy X (fun x => Abar (Q.f x))) {t : ℕ} (h : π.Memory t),
      infiniteValue π Q.micro h ≤ Q.micro.optimalValue (π.current h)) := by
  exact Q.liftSelector_optimal_against_all_causal Q.macroModel.greedyAction
    (fun y => Q.macroModel.greedyAction_spec y)

/-- P-QUO-01 source-facing closure: exact value pullback, actionwise optimal-Q
agreement, and macro-optimal-policy lifting to micro optimality.  The policy
comparison is against the full causal randomized class supplied by P-CTL-01. -/
theorem p_quo_01 :
    (∀ x : X, Q.micro.optimalValue x = Q.macroModel.optimalValue (Q.f x)) ∧
    (∀ (x : X) (a : Abar (Q.f x)),
      Q.micro.qValue Q.micro.optimalValue x a =
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a) ∧
    (∀ {t : ℕ} (x : X),
      infiniteValue (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
        Q.micro (t := t) x = Q.micro.optimalValue x) ∧
    (∀ (π : CausalPolicy X (fun x => Abar (Q.f x))) {t : ℕ} (h : π.Memory t),
      infiniteValue π Q.micro h ≤ Q.micro.optimalValue (π.current h)) := by
  refine ⟨Q.optimalValue_apply, Q.optimal_qValue_pullback, ?_, ?_⟩
  · intro t x
    exact Q.liftSelector_infiniteValue_eq_optimal Q.macroModel.greedyAction
      (fun y => Q.macroModel.greedyAction_spec y) (t := t) x
  · intro π t h
    exact infiniteValue_le_optimal π Q.micro h

end ExactControlQuotient

end UEOT.V3.FiniteDiscountedControl
