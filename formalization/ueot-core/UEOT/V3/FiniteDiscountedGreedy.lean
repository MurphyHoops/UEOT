import UEOT.V3.FiniteDiscountedCausalInfinite
import Mathlib.Tactic

/-!
# P-CTL-01 — stationary deterministic greedy attainment

The causal upper bound is only half of the frozen theorem.  This module builds
the finite Bellman selector as an explicit stationary deterministic causal
policy and proves that its infinite discounted value equals `V*`.  Together
with `infiniteValue_le_optimal`, this establishes optimality over the full
history-dependent randomized causal class.
-/

namespace UEOT.V3.FiniteDiscountedControl

open Filter Topology
open CausalPolicy

universe uX uA

variable {X : Type uX} [Fintype X]
variable {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]

/-- Finite admissible action spaces are classically decidable.  Keeping this
instance local avoids adding constructive decidable-equality assumptions to the
frozen theorem statement. -/
noncomputable local instance actionDecidableEq (x : X) : DecidableEq (A x) :=
  Classical.decEq (A x)

/-- The Bellman maximizing selector represented as a stationary deterministic
causal policy.  Its memory is just the current state and its action law is the
Dirac mass at `greedyAction`. -/
noncomputable def greedyPolicy (M : Model X A) : CausalPolicy X A where
  Memory := fun _ => X
  current := fun x => x
  advance := fun _ _ y => y
  current_advance := by
    intro t h a y
    rfl
  actionProb := fun h a => if a = M.greedyAction h then 1 else 0
  actionProb_nonneg := by
    intro t h a
    by_cases ha : a = M.greedyAction h <;> simp [ha]
  actionProb_sum_one := by
    intro t h
    simp

@[simp] theorem greedyPolicy_current (M : Model X A) {t : ℕ} (x : X) :
    (greedyPolicy M).current (t := t) x = x := rfl

@[simp] theorem greedyPolicy_advance (M : Model X A) {t : ℕ} (x : X)
    (a : A x) (y : X) :
    (greedyPolicy M).advance (t := t) x a y = y := rfl

@[simp] theorem greedyPolicy_actionProb (M : Model X A) {t : ℕ} (x : X) (a : A x) :
    (greedyPolicy M).actionProb (t := t) x a =
      if a = M.greedyAction x then 1 else 0 := rfl

/-- Under the deterministic greedy policy, the causal recursion reduces to the
single Bellman-selected action.  The time index is explicit because the greedy
policy has the constant memory family `Memory t = X`, so it cannot be inferred
from the memory value alone. -/
@[simp] theorem greedy_truncatedValue_succ (M : Model X A) (n : ℕ) {t : ℕ} (x : X) :
    truncatedValue (greedyPolicy M) M (n + 1) (t := t) x =
      M.reward x (M.greedyAction x) +
        M.discount * ∑ y, M.transition x (M.greedyAction x) y *
          truncatedValue (greedyPolicy M) M n (t := t + 1) y := by
  simp [truncatedValue_succ, greedyPolicy]

namespace Model

/-- Policy-evaluation Bellman map for the stationary deterministic greedy
selector fixed at `V*`. -/
noncomputable def greedyBellman (M : Model X A) (v : X → ℝ) : X → ℝ :=
  fun x => M.qValue v x (M.greedyAction x)

/-- The greedy policy-evaluation Bellman map has the same discount Lipschitz
constant as the optimal Bellman map. -/
theorem greedyBellman_lipschitz (M : Model X A) :
    LipschitzWith M.discountNN M.greedyBellman := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro v w
  apply (dist_pi_le_iff (mul_nonneg (by positivity) dist_nonneg)).2
  intro x
  simpa [greedyBellman, Real.dist_eq] using
    M.abs_qValue_sub_le v w x (M.greedyAction x)

/-- The greedy policy-evaluation map is a contraction. -/
theorem greedyBellman_contracting (M : Model X A) :
    ContractingWith M.discountNN M.greedyBellman := by
  refine ⟨?_, M.greedyBellman_lipschitz⟩
  change M.discount < 1
  exact M.discount_lt_one

/-- `V*` is a fixed point of the policy-evaluation map induced by its own
greedy selector. -/
theorem greedyBellman_optimal_fixed (M : Model X A) :
    M.greedyBellman M.optimalValue = M.optimalValue := by
  funext x
  simpa [greedyBellman] using M.greedyAction_spec x

/-- Policy evaluation of the frozen greedy selector converges from every
initial value to `V*`. -/
theorem greedyValueIteration_tendsto (M : Model X A) (v₀ : X → ℝ) :
    Tendsto (fun n => (M.greedyBellman)^[n] v₀) atTop (𝓝 M.optimalValue) := by
  have h := M.greedyBellman_contracting.tendsto_iterate_fixedPoint v₀
  have hfix :
      ContractingWith.fixedPoint M.greedyBellman M.greedyBellman_contracting =
        M.optimalValue :=
    (M.greedyBellman_contracting.fixedPoint_unique M.greedyBellman_optimal_fixed).symm
  rw [hfix] at h
  exact h

end Model

/-- The `n`-stage value of the deterministic greedy causal policy is exactly the
`n`-fold policy-evaluation Bellman iterate from zero.  This identity is uniform
in the external causal time index. -/
theorem greedy_truncatedValue_eq_iterate (M : Model X A) :
    ∀ (n : ℕ) (t : ℕ) (x : X),
      truncatedValue (greedyPolicy M) M n (t := t) x =
        ((M.greedyBellman)^[n] (fun _ : X => (0 : ℝ))) x := by
  intro n
  induction n with
  | zero =>
      intro t x
      simp [truncatedValue]
  | succ n ih =>
      intro t x
      rw [greedy_truncatedValue_succ (t := t), Function.iterate_succ_apply']
      simp only [Model.greedyBellman, Model.qValue, Model.expect]
      simp_rw [ih (t + 1)]

/-- Finite-horizon values of the stationary deterministic greedy policy converge
pointwise to `V*`, uniformly with respect to the external causal time index. -/
theorem greedy_truncatedValue_tendsto_optimal (M : Model X A) {t : ℕ} (x : X) :
    Tendsto (fun n => truncatedValue (greedyPolicy M) M n (t := t) x)
      atTop (𝓝 (M.optimalValue x)) := by
  have hfun := M.greedyValueIteration_tendsto (fun _ : X => (0 : ℝ))
  have hx := tendsto_pi_nhds.mp hfun x
  exact hx.congr' <| Eventually.of_forall fun n =>
    (greedy_truncatedValue_eq_iterate M n t x).symm

/-- The stationary deterministic greedy policy attains the Bellman optimum at
every state and at every external causal time index. -/
theorem greedy_infiniteValue_eq_optimal (M : Model X A) {t : ℕ} (x : X) :
    infiniteValue (greedyPolicy M) M (t := t) x = M.optimalValue x := by
  exact tendsto_nhds_unique
    (truncatedValue_tendsto_infiniteValue (greedyPolicy M) M (t := t) x)
    (greedy_truncatedValue_tendsto_optimal M (t := t) x)

/-- P-CTL-01 causal-optimality core: every causal randomized policy is bounded
by `V*`, and a stationary deterministic policy attains `V*` at every state. -/
theorem p_ctl_01_causal_optimality (M : Model X A) :
    (∀ (π : CausalPolicy X A) {t : ℕ} (h : π.Memory t),
      infiniteValue π M h ≤ M.optimalValue (π.current h)) ∧
    (∀ {t : ℕ} (x : X),
      infiniteValue (greedyPolicy M) M (t := t) x = M.optimalValue x) := by
  constructor
  · intro π t h
    exact infiniteValue_le_optimal π M h
  · intro t x
    exact greedy_infiniteValue_eq_optimal M (t := t) x

end UEOT.V3.FiniteDiscountedControl
