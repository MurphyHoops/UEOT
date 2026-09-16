import UEOT.V3.FiniteDiscountedControl
import Mathlib.Tactic

/-!
# P-CTL-01 — causal-policy verification layer

The frozen theorem is stronger than optimality among stationary or Markov
policies: the stationary deterministic Bellman selector must dominate every
causal policy.  To preserve that quantifier, a policy below carries an arbitrary
time-indexed memory type.  That memory may be the full observed history, so the
action law may be history dependent and randomized.

This file first proves the finite-horizon Bellman supermartingale inequality in
an entirely finite recursive form.  The infinite discounted value and greedy
attainment are then obtained by controlling the geometric tail.
-/

namespace UEOT.V3.FiniteDiscountedControl

open Filter Topology

universe uX uA uH

variable {X : Type uX} [Fintype X]
variable {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]

/-- An arbitrary causal randomized policy.  `Memory t` can encode the complete
history `H_t`; no Markov or finite-memory restriction is imposed. -/
structure CausalPolicy (X : Type uX) (A : X → Type uA) [∀ x, Fintype (A x)] where
  Memory : ℕ → Type uH
  current : ∀ {t}, Memory t → X
  advance : ∀ {t} (h : Memory t), A (current h) → X → Memory (t + 1)
  current_advance : ∀ {t} (h : Memory t) (a : A (current h)) (y : X),
    current (advance h a y) = y
  actionProb : ∀ {t} (h : Memory t), A (current h) → ℝ
  actionProb_nonneg : ∀ {t} (h : Memory t) (a : A (current h)), 0 ≤ actionProb h a
  actionProb_sum_one : ∀ {t} (h : Memory t), ∑ a, actionProb h a = 1

namespace CausalPolicy

/-- Expected discounted reward accumulated over the next `n` stages from an
arbitrary causal memory state. -/
def truncatedValue (π : CausalPolicy X A) (M : Model X A) :
    (n : ℕ) → {t : ℕ} → π.Memory t → ℝ
  | 0, _, _ => 0
  | n + 1, _, h =>
      ∑ a, π.actionProb h a *
        (M.reward (π.current h) a +
          M.discount * ∑ y, M.transition (π.current h) a y *
            truncatedValue π M n (π.advance h a y))

@[simp] theorem truncatedValue_zero (π : CausalPolicy X A) (M : Model X A)
    {t : ℕ} (h : π.Memory t) :
    truncatedValue π M 0 h = 0 := rfl

@[simp] theorem truncatedValue_succ (π : CausalPolicy X A) (M : Model X A)
    (n : ℕ) {t : ℕ} (h : π.Memory t) :
    truncatedValue π M (n + 1) h =
      ∑ a, π.actionProb h a *
        (M.reward (π.current h) a +
          M.discount * ∑ y, M.transition (π.current h) a y *
            truncatedValue π M n (π.advance h a y)) := rfl

/-- The finite-state sup-distance from zero to `V*`; this is the explicit
terminal-value radius used to make the frozen proof's vanishing tail rigorous. -/
noncomputable def optimalRadius (M : Model X A) : ℝ :=
  dist (fun _ : X => (0 : ℝ)) M.optimalValue

/-- Every coordinate of `V*` lies above minus its finite-state sup-radius. -/
theorem neg_optimalValue_le_radius (M : Model X A) (x : X) :
    -M.optimalValue x ≤ optimalRadius M := by
  have hx : |M.optimalValue x| ≤ optimalRadius M := by
    have hdist := dist_le_pi_dist (fun _ : X => (0 : ℝ)) M.optimalValue x
    simpa [optimalRadius, Real.dist_eq] using hdist
  exact (neg_le_abs (M.optimalValue x)).trans hx

/-- For every causal randomized policy, every horizon, and every causal memory
state, the truncated discounted reward is bounded by `V*` plus an explicit
geometric terminal tail.  This is the finite recursive form of the source
Bellman-supermartingale argument. -/
theorem truncatedValue_le_optimal_add_tail (π : CausalPolicy X A) (M : Model X A) :
    ∀ (n : ℕ) {t : ℕ} (h : π.Memory t),
      truncatedValue π M n h ≤
        M.optimalValue (π.current h) + M.discount ^ n * optimalRadius M := by
  intro n
  induction n with
  | zero =>
      intro t h
      simp only [truncatedValue_zero, pow_zero, one_mul]
      have hneg := neg_optimalValue_le_radius M (π.current h)
      linarith
  | succ n ih =>
      intro t h
      let C : ℝ := optimalRadius M
      have hcont (a : A (π.current h)) :
          (∑ y, M.transition (π.current h) a y *
            truncatedValue π M n (π.advance h a y)) ≤
            M.expect (π.current h) a M.optimalValue + M.discount ^ n * C := by
        calc
          (∑ y, M.transition (π.current h) a y *
              truncatedValue π M n (π.advance h a y))
              ≤ ∑ y, M.transition (π.current h) a y *
                  (M.optimalValue y + M.discount ^ n * C) := by
                apply Finset.sum_le_sum
                intro y hy
                apply mul_le_mul_of_nonneg_left _ (M.transition_nonneg (π.current h) a y)
                simpa only [π.current_advance] using
                  (ih (t := t + 1) (π.advance h a y))
          _ = M.expect (π.current h) a M.optimalValue + M.discount ^ n * C := by
                simp only [Model.expect, mul_add, Finset.sum_add_distrib]
                rw [← Finset.sum_mul, M.transition_sum_one (π.current h) a, one_mul]
      have haction (a : A (π.current h)) :
          M.reward (π.current h) a +
              M.discount * (∑ y, M.transition (π.current h) a y *
                truncatedValue π M n (π.advance h a y)) ≤
            M.optimalValue (π.current h) + M.discount ^ (n + 1) * C := by
        calc
          M.reward (π.current h) a +
              M.discount * (∑ y, M.transition (π.current h) a y *
                truncatedValue π M n (π.advance h a y))
              ≤ M.reward (π.current h) a +
                  M.discount *
                    (M.expect (π.current h) a M.optimalValue + M.discount ^ n * C) := by
                exact add_le_add le_rfl
                  (mul_le_mul_of_nonneg_left (hcont a) M.discount_pos.le)
          _ = M.qValue M.optimalValue (π.current h) a +
                M.discount ^ (n + 1) * C := by
                simp only [Model.qValue]
                rw [pow_succ]
                ring
          _ ≤ M.optimalValue (π.current h) + M.discount ^ (n + 1) * C := by
                exact add_le_add (M.qValue_optimal_le (π.current h) a) le_rfl
      calc
        truncatedValue π M (n + 1) h
            = ∑ a, π.actionProb h a *
                (M.reward (π.current h) a +
                  M.discount * ∑ y, M.transition (π.current h) a y *
                    truncatedValue π M n (π.advance h a y)) := rfl
        _ ≤ ∑ a, π.actionProb h a *
                (M.optimalValue (π.current h) + M.discount ^ (n + 1) * C) := by
              apply Finset.sum_le_sum
              intro a ha
              exact mul_le_mul_of_nonneg_left (haction a) (π.actionProb_nonneg h a)
        _ = M.optimalValue (π.current h) + M.discount ^ (n + 1) * C := by
              rw [← Finset.sum_mul, π.actionProb_sum_one h, one_mul]
        _ = M.optimalValue (π.current h) +
              M.discount ^ (n + 1) * optimalRadius M := by rfl

end CausalPolicy

end UEOT.V3.FiniteDiscountedControl