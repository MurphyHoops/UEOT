import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# P-CTL-01 — finite discounted control

This module formalizes the frozen Core 3 finite-state discounted-control
foundation.  Actions are genuinely state dependent: `A x` is a finite nonempty
type for each state `x`.

The first layer below establishes the exact Bellman contraction, its unique
fixed point, value-iteration convergence from an arbitrary initial value, and a
pointwise finite greedy selector.  The causal-policy domination layer is added
on top of this same model; no compact/Feller assumptions from P-CTL-02 are used.
-/

namespace UEOT.V3.FiniteDiscountedControl

open Filter Topology

universe uX uA

variable {X : Type uX} [Fintype X]
variable {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]

/-- A finite discounted controlled Markov model with state-dependent actions. -/
structure Model (X : Type uX) [Fintype X] (A : X → Type uA)
    [∀ x, Fintype (A x)] where
  transition : ∀ x, A x → X → ℝ
  reward : ∀ x, A x → ℝ
  rewardBound : ℝ
  discount : ℝ
  transition_nonneg : ∀ x a y, 0 ≤ transition x a y
  transition_sum_one : ∀ x a, ∑ y, transition x a y = 1
  reward_abs_le : ∀ x a, |reward x a| ≤ rewardBound
  discount_pos : 0 < discount
  discount_lt_one : discount < 1

namespace Model

variable (M : Model X A)

/-- One-step expectation of a state value under an admissible state-action pair. -/
def expect (x : X) (a : A x) (v : X → ℝ) : ℝ :=
  ∑ y, M.transition x a y * v y

/-- Bellman action value for continuation value `v`. -/
def qValue (v : X → ℝ) (x : X) (a : A x) : ℝ :=
  M.reward x a + M.discount * M.expect x a v

/-- Frozen-source Bellman operator, maximizing over the actual admissible
state-dependent action type. -/
noncomputable def bellman (v : X → ℝ) : X → ℝ :=
  fun x => Finset.univ.sup' Finset.univ_nonempty (fun a : A x => M.qValue v x a)

/-- The discount as a nonnegative real, used as the metric contraction constant. -/
def discountNN : NNReal := ⟨M.discount, M.discount_pos.le⟩

@[simp] theorem coe_discountNN : (M.discountNN : ℝ) = M.discount := rfl

/-- Probability-weighted expectation is nonexpansive in the sup metric. -/
theorem abs_expect_sub_le_dist (x : X) (a : A x) (v w : X → ℝ) :
    |M.expect x a v - M.expect x a w| ≤ dist v w := by
  simp only [expect]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ y, (M.transition x a y * v y - M.transition x a y * w y)|
        ≤ ∑ y, |M.transition x a y * v y - M.transition x a y * w y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, M.transition x a y * |v y - w y| := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← mul_sub, abs_mul, abs_of_nonneg (M.transition_nonneg x a y)]
    _ ≤ ∑ y, M.transition x a y * dist v w := by
      apply Finset.sum_le_sum
      intro y hy
      apply mul_le_mul_of_nonneg_left _ (M.transition_nonneg x a y)
      simpa [Real.dist_eq] using dist_le_pi_dist v w y
    _ = dist v w := by
      rw [← Finset.sum_mul, M.transition_sum_one x a, one_mul]

/-- Each action-value map is `β`-Lipschitz in the continuation value. -/
theorem abs_qValue_sub_le (v w : X → ℝ) (x : X) (a : A x) :
    |M.qValue v x a - M.qValue w x a| ≤ M.discount * dist v w := by
  have h := M.abs_expect_sub_le_dist x a v w
  have hβ : 0 ≤ M.discount := M.discount_pos.le
  calc
    |M.qValue v x a - M.qValue w x a|
        = M.discount * |M.expect x a v - M.expect x a w| := by
          simp only [qValue]
          rw [show M.reward x a + M.discount * M.expect x a v -
                (M.reward x a + M.discount * M.expect x a w) =
                M.discount * (M.expect x a v - M.expect x a w) by ring,
              abs_mul, abs_of_nonneg hβ]
    _ ≤ M.discount * dist v w := mul_le_mul_of_nonneg_left h hβ

/-- Finite maximization preserves the same pointwise Lipschitz constant. -/
theorem abs_bellman_apply_sub_le (v w : X → ℝ) (x : X) :
    |M.bellman v x - M.bellman w x| ≤ M.discount * dist v w := by
  obtain ⟨av, hav_mem, hav⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (A x)))
      Finset.univ_nonempty (fun a => M.qValue v x a)
  obtain ⟨aw, haw_mem, haw⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (A x)))
      Finset.univ_nonempty (fun a => M.qValue w x a)
  have hvw := M.abs_qValue_sub_le v w x av
  have hwv := M.abs_qValue_sub_le v w x aw
  have hw_max : M.qValue w x av ≤ M.qValue w x aw := by
    rw [← haw]
    exact Finset.le_sup' (fun a : A x => M.qValue w x a) hav_mem
  have hv_max : M.qValue v x aw ≤ M.qValue v x av := by
    rw [← hav]
    exact Finset.le_sup' (fun a : A x => M.qValue v x a) haw_mem
  change
    |(Finset.univ.sup' Finset.univ_nonempty (fun a : A x => M.qValue v x a)) -
      (Finset.univ.sup' Finset.univ_nonempty (fun a : A x => M.qValue w x a))| ≤
      M.discount * dist v w
  rw [hav, haw, abs_le]
  constructor
  · have hlow := (abs_le.mp hwv).1
    linarith
  · have hupp := (abs_le.mp hvw).2
    linarith

/-- Bellman is globally Lipschitz with constant `β` in the finite-state sup metric. -/
theorem bellman_lipschitz : LipschitzWith M.discountNN M.bellman := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro v w
  apply (dist_pi_le_iff (mul_nonneg (by positivity) dist_nonneg)).2
  intro x
  simpa [Real.dist_eq] using M.abs_bellman_apply_sub_le v w x

/-- The source assumption `0 < β < 1` makes the Bellman map a contraction. -/
theorem bellman_contracting : ContractingWith M.discountNN M.bellman := by
  refine ⟨?_, M.bellman_lipschitz⟩
  change M.discount < 1
  exact M.discount_lt_one

/-- The canonical Bellman fixed point supplied by Banach's theorem. -/
noncomputable def optimalValue : X → ℝ :=
  ContractingWith.fixedPoint M.bellman M.bellman_contracting

/-- The canonical value is a Bellman fixed point. -/
theorem optimalValue_fixed : M.bellman M.optimalValue = M.optimalValue :=
  M.bellman_contracting.fixedPoint_isFixedPt

/-- The Bellman fixed point is unique. -/
theorem fixedPoint_unique {v : X → ℝ} (hv : M.bellman v = v) :
    v = M.optimalValue :=
  M.bellman_contracting.fixedPoint_unique hv

/-- Value iteration converges from every initial value function. -/
theorem valueIteration_tendsto (v₀ : X → ℝ) :
    Tendsto (fun n => M.bellman^[n] v₀) atTop (𝓝 M.optimalValue) :=
  M.bellman_contracting.tendsto_iterate_fixedPoint v₀

/-- A pointwise maximizing stationary deterministic action exists by finite
nonempty admissibility. -/
noncomputable def greedyAction (x : X) : A x :=
  Classical.choose <|
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (A x)))
      Finset.univ_nonempty (fun a => M.qValue M.optimalValue x a)

/-- The greedy action attains the Bellman maximum at the fixed point. -/
theorem greedyAction_spec (x : X) :
    M.qValue M.optimalValue x (M.greedyAction x) = M.optimalValue x := by
  have hchoose :=
    (Classical.choose_spec <|
      Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (A x)))
        Finset.univ_nonempty (fun a => M.qValue M.optimalValue x a)).2
  have hbell : M.bellman M.optimalValue x = M.optimalValue x :=
    congrFun M.optimalValue_fixed x
  rw [bellman] at hbell
  exact hchoose ▸ hbell

/-- Every admissible action is dominated by the Bellman fixed point.  This is
exactly the one-step inequality iterated in the causal-policy verification
argument. -/
theorem qValue_optimal_le (x : X) (a : A x) :
    M.qValue M.optimalValue x a ≤ M.optimalValue x := by
  calc
    M.qValue M.optimalValue x a ≤ M.bellman M.optimalValue x := by
      unfold bellman
      exact Finset.le_sup' (fun b : A x => M.qValue M.optimalValue x b) (Finset.mem_univ a)
    _ = M.optimalValue x := congrFun M.optimalValue_fixed x

/-- Frozen-source residual stopping certificate:
`‖v - V*‖∞ ≤ ‖Tv - v‖∞ / (1 - β)` (metric form, with the symmetric numerator). -/
theorem valueError_le_residual (v : X → ℝ) :
    dist v M.optimalValue ≤ dist v (M.bellman v) / (1 - M.discount) := by
  simpa [optimalValue] using M.bellman_contracting.dist_fixedPoint_le v

end Model

end UEOT.V3.FiniteDiscountedControl