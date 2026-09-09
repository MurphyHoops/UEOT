import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Finite-horizon foundation of P-TEL-01. The terminal potential is retained.
No infinite-horizon convergence theorem is claimed. -/

namespace UEOT.Reward

def discounted (β : ℝ) (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, β ^ t * r t

theorem discounted_zero (β : ℝ) (r : ℕ → ℝ) : discounted β r 0 = 0 := by
  simp [discounted]

theorem discounted_succ (β : ℝ) (r : ℕ → ℝ) (n : ℕ) :
    discounted β r (n + 1) = discounted β r n + β ^ n * r n := by
  exact Finset.sum_range_succ _ n

theorem potential_telescope (β : ℝ) (ψ : ℕ → ℝ) (n : ℕ) :
    discounted β (fun t => β * ψ (t + 1) - ψ t) n = β ^ n * ψ n - ψ 0 := by
  induction n with
  | zero => simp [discounted]
  | succ n ih => rw [discounted_succ, ih, pow_succ]; ring

theorem shaping_finite (β a c : ℝ) (r ψ : ℕ → ℝ) (n : ℕ) :
    discounted β (fun t => a * r t + β * ψ (t + 1) - ψ t + c) n =
      a * discounted β r n + β ^ n * ψ n - ψ 0 +
        c * discounted β (fun _ => 1) n := by
  induction n with
  | zero => simp [discounted]
  | succ n ih =>
    rw [discounted_succ, ih, discounted_succ, discounted_succ, pow_succ]
    ring

theorem shaping_terminal_corrected (β a c : ℝ) (r ψ : ℕ → ℝ) (n : ℕ) :
    discounted β (fun t => a * r t + β * ψ (t + 1) - ψ t + c) n - β ^ n * ψ n =
      a * discounted β r n - ψ 0 + c * discounted β (fun _ => 1) n := by
  rw [shaping_finite]
  ring

theorem geometric_finite (β : ℝ) (n : ℕ) :
    (1 - β) * discounted β (fun _ => 1) n = 1 - β ^ n := by
  induction n with
  | zero => simp [discounted]
  | succ n ih =>
    rw [discounted_succ, mul_add, ih, pow_succ]
    ring

def IsMaximizer {P : Type*} (value : P → ℝ) (p : P) : Prop :=
  ∀ q, value q ≤ value p

theorem positive_affine_maximizer {P : Type*} (value : P → ℝ)
    (a b : ℝ) (ha : 0 < a) (p : P) :
    IsMaximizer (fun q => a * value q + b) p ↔ IsMaximizer value p := by
  constructor
  · intro h q
    have hq := h q
    nlinarith
  · intro h q
    have hq := h q
    nlinarith

end UEOT.Reward
