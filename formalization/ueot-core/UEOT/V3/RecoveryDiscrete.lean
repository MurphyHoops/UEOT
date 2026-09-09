import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# P-REC-01 foundation — discrete affine recovery recursion

The probabilistic source theorem reduces after taking total expectations to the
scalar recursion

  m (n+1) ≤ κ m n + η.

This module machine-checks the exact geometric recursion bound.  The
conditional-expectation bridge and Markov tail bound are kept as the next
source-facing layer and are not claimed here.
-/

namespace UEOT.V3.RecoveryDiscrete

open scoped BigOperators

theorem geometric_sum_identity (κ : ℝ) (n : ℕ) :
    (1 - κ) * (∑ i ∈ Finset.range n, κ ^ i) = 1 - κ ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

theorem one_add_mul_geometric_sum (κ : ℝ) (n : ℕ) :
    1 + κ * (∑ i ∈ Finset.range n, κ ^ i) =
      ∑ i ∈ Finset.range (n + 1), κ ^ i := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih, pow_succ]
      ring

theorem affine_recurrence_sum_bound
    (m : ℕ → ℝ) (κ η : ℝ) (hκ0 : 0 ≤ κ)
    (hrec : ∀ n, m (n + 1) ≤ κ * m n + η) :
    ∀ n, m n ≤ κ ^ n * m 0 + η * (∑ i ∈ Finset.range n, κ ^ i) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        m (n + 1) ≤ κ * m n + η := hrec n
        _ ≤ κ * (κ ^ n * m 0 +
              η * (∑ i ∈ Finset.range n, κ ^ i)) + η := by
            have hm := mul_le_mul_of_nonneg_left ih hκ0
            linarith
        _ = κ ^ (n + 1) * m 0 +
              η * (∑ i ∈ Finset.range (n + 1), κ ^ i) := by
            rw [pow_succ]
            have hgeom := one_add_mul_geometric_sum κ n
            ring_nf at hgeom ⊢
            rw [← hgeom]
            ring

/-- Exact scalar closed form appearing in P-REC-01. -/
theorem affine_recurrence_closed_bound
    (m : ℕ → ℝ) (κ η : ℝ)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hrec : ∀ n, m (n + 1) ≤ κ * m n + η) :
    ∀ n, m n ≤
      κ ^ n * m 0 + η * ((1 - κ ^ n) / (1 - κ)) := by
  intro n
  have hbase := affine_recurrence_sum_bound m κ η hκ0 hrec n
  have hden : 1 - κ ≠ 0 := ne_of_gt (sub_pos.mpr hκ1)
  have hgeom :
      (∑ i ∈ Finset.range n, κ ^ i) =
        (1 - κ ^ n) / (1 - κ) := by
    apply (eq_div_iff hden).2
    simpa [mul_comm] using geometric_sum_identity κ n
  simpa [hgeom] using hbase

end UEOT.V3.RecoveryDiscrete
