import UEOT.V3.FiniteDiscountedCausal
import Mathlib.Tactic

/-!
# P-CTL-01 — infinite-horizon causal-policy closure

This module closes the analytic gap between the finite causal Bellman bound and
the frozen infinite-horizon statement.  Bounded one-stage rewards give a
geometric bound on successive finite-horizon values.  Hence every causal,
history-dependent randomized policy has a well-defined infinite discounted
value.  Passing the finite Bellman domination inequality to the limit yields
optimal-value domination for the full causal policy class.
-/

namespace UEOT.V3.FiniteDiscountedControl

open Filter Topology

universe uX uA

variable {X : Type uX} [Fintype X]
variable {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]

namespace CausalPolicy

/-- Once a state exists, the model's declared absolute reward bound is
necessarily nonnegative. -/
theorem rewardBound_nonneg_at (M : Model X A) (x : X) : 0 ≤ M.rewardBound := by
  let a : A x := Classical.choice (inferInstance : Nonempty (A x))
  exact (abs_nonneg (M.reward x a)).trans (M.reward_abs_le x a)

/-- Successive finite-horizon causal values differ by at most the next discounted
reward envelope.  This estimate is uniform over all causal memories. -/
theorem abs_truncatedValue_succ_sub_le (π : CausalPolicy X A) (M : Model X A) :
    ∀ (n : ℕ) {t : ℕ} (h : π.Memory t),
      |truncatedValue π M (n + 1) h - truncatedValue π M n h| ≤
        M.rewardBound * M.discount ^ n := by
  intro n
  induction n with
  | zero =>
      intro t h
      have hbase :
          |∑ a, π.actionProb h a * M.reward (π.current h) a| ≤ M.rewardBound := by
        calc
          |∑ a, π.actionProb h a * M.reward (π.current h) a|
              ≤ ∑ a, |π.actionProb h a * M.reward (π.current h) a| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ a, π.actionProb h a * |M.reward (π.current h) a| := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [abs_mul, abs_of_nonneg (π.actionProb_nonneg h a)]
          _ ≤ ∑ a, π.actionProb h a * M.rewardBound := by
                apply Finset.sum_le_sum
                intro a ha
                exact mul_le_mul_of_nonneg_left
                  (M.reward_abs_le (π.current h) a) (π.actionProb_nonneg h a)
          _ = M.rewardBound := by
                rw [← Finset.sum_mul, π.actionProb_sum_one h, one_mul]
      simpa [truncatedValue] using hbase
  | succ n ih =>
      intro t h
      have hinner (a : A (π.current h)) :
          |(∑ y, M.transition (π.current h) a y *
                truncatedValue π M (n + 1) (π.advance h a y)) -
            (∑ y, M.transition (π.current h) a y *
                truncatedValue π M n (π.advance h a y))| ≤
            M.rewardBound * M.discount ^ n := by
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ y,
              (M.transition (π.current h) a y *
                  truncatedValue π M (n + 1) (π.advance h a y) -
               M.transition (π.current h) a y *
                  truncatedValue π M n (π.advance h a y))|
              ≤ ∑ y,
                  |M.transition (π.current h) a y *
                      truncatedValue π M (n + 1) (π.advance h a y) -
                   M.transition (π.current h) a y *
                      truncatedValue π M n (π.advance h a y)| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ y, M.transition (π.current h) a y *
                |truncatedValue π M (n + 1) (π.advance h a y) -
                  truncatedValue π M n (π.advance h a y)| := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [← mul_sub, abs_mul,
                  abs_of_nonneg (M.transition_nonneg (π.current h) a y)]
          _ ≤ ∑ y, M.transition (π.current h) a y *
                (M.rewardBound * M.discount ^ n) := by
                apply Finset.sum_le_sum
                intro y hy
                exact mul_le_mul_of_nonneg_left
                  (ih (t := t + 1) (π.advance h a y))
                  (M.transition_nonneg (π.current h) a y)
          _ = M.rewardBound * M.discount ^ n := by
                rw [← Finset.sum_mul, M.transition_sum_one (π.current h) a, one_mul]
      rw [truncatedValue_succ π M (n + 1) h, truncatedValue_succ π M n h,
        ← Finset.sum_sub_distrib]
      calc
        |∑ a,
            (π.actionProb h a *
                (M.reward (π.current h) a +
                  M.discount *
                    ∑ y, M.transition (π.current h) a y *
                      truncatedValue π M (n + 1) (π.advance h a y)) -
             π.actionProb h a *
                (M.reward (π.current h) a +
                  M.discount *
                    ∑ y, M.transition (π.current h) a y *
                      truncatedValue π M n (π.advance h a y)))|
            ≤ ∑ a,
                |π.actionProb h a *
                    (M.reward (π.current h) a +
                      M.discount *
                        ∑ y, M.transition (π.current h) a y *
                          truncatedValue π M (n + 1) (π.advance h a y)) -
                 π.actionProb h a *
                    (M.reward (π.current h) a +
                      M.discount *
                        ∑ y, M.transition (π.current h) a y *
                          truncatedValue π M n (π.advance h a y))| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ a, π.actionProb h a *
              (M.discount *
                |(∑ y, M.transition (π.current h) a y *
                      truncatedValue π M (n + 1) (π.advance h a y)) -
                  (∑ y, M.transition (π.current h) a y *
                      truncatedValue π M n (π.advance h a y))|) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [← mul_sub, abs_mul, abs_of_nonneg (π.actionProb_nonneg h a)]
              have hdiff :
                  (M.reward (π.current h) a +
                      M.discount *
                        ∑ y, M.transition (π.current h) a y *
                          truncatedValue π M (n + 1) (π.advance h a y)) -
                    (M.reward (π.current h) a +
                      M.discount *
                        ∑ y, M.transition (π.current h) a y *
                          truncatedValue π M n (π.advance h a y)) =
                    M.discount *
                      ((∑ y, M.transition (π.current h) a y *
                          truncatedValue π M (n + 1) (π.advance h a y)) -
                       (∑ y, M.transition (π.current h) a y *
                          truncatedValue π M n (π.advance h a y))) := by
                ring
              rw [hdiff, abs_mul, abs_of_nonneg M.discount_pos.le]
        _ ≤ ∑ a, π.actionProb h a *
              (M.discount * (M.rewardBound * M.discount ^ n)) := by
              apply Finset.sum_le_sum
              intro a ha
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hinner a) M.discount_pos.le)
                (π.actionProb_nonneg h a)
        _ = M.rewardBound * M.discount ^ (n + 1) := by
              rw [← Finset.sum_mul, π.actionProb_sum_one h, one_mul, pow_succ]
              ring

/-- The sequence of finite-horizon values of every causal policy is Cauchy. -/
theorem truncatedValue_cauchy (π : CausalPolicy X A) (M : Model X A)
    {t : ℕ} (h : π.Memory t) :
    CauchySeq (fun n => truncatedValue π M n h) := by
  refine cauchySeq_of_le_geometric M.discount M.rewardBound M.discount_lt_one ?_
  intro n
  simpa [Real.dist_eq, abs_sub_comm] using
    (abs_truncatedValue_succ_sub_le π M n h)

/-- Infinite discounted causal value, defined as the limit of finite-horizon
values whose existence was proved above. -/
noncomputable def infiniteValue (π : CausalPolicy X A) (M : Model X A)
    {t : ℕ} (h : π.Memory t) : ℝ :=
  limUnder atTop (fun n => truncatedValue π M n h)

/-- Finite-horizon causal values converge to the infinite discounted value. -/
theorem truncatedValue_tendsto_infiniteValue (π : CausalPolicy X A) (M : Model X A)
    {t : ℕ} (h : π.Memory t) :
    Tendsto (fun n => truncatedValue π M n h) atTop (𝓝 (infiniteValue π M h)) := by
  simpa [infiniteValue] using (truncatedValue_cauchy π M h).tendsto_limUnder

/-- Every causal, history-dependent randomized policy is dominated by the
Bellman fixed point.  No stationarity or Markov restriction appears in the
quantifier. -/
theorem infiniteValue_le_optimal (π : CausalPolicy X A) (M : Model X A)
    {t : ℕ} (h : π.Memory t) :
    infiniteValue π M h ≤ M.optimalValue (π.current h) := by
  have hleft := truncatedValue_tendsto_infiniteValue π M h
  have hpow : Tendsto (fun n : ℕ => M.discount ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one M.discount_pos.le M.discount_lt_one
  have htail0 :
      Tendsto (fun n : ℕ => M.discount ^ n * optimalRadius M) atTop (𝓝 0) := by
    simpa using Filter.Tendsto.mul_const (optimalRadius M) hpow
  have hright :
      Tendsto
        (fun n : ℕ =>
          M.optimalValue (π.current h) + M.discount ^ n * optimalRadius M)
        atTop (𝓝 (M.optimalValue (π.current h))) := by
    simpa using tendsto_const_nhds.add htail0
  exact le_of_tendsto_of_tendsto' hleft hright
    (fun n => truncatedValue_le_optimal_add_tail π M n h)

end CausalPolicy

end UEOT.V3.FiniteDiscountedControl