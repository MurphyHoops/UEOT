import UEOT.V3.FiniteDiscountedGreedy
import Mathlib.Tactic

/-!
# Generic stationary deterministic selector evaluation

This module factors the policy-evaluation argument used by P-CTL-01 away from
the particular canonical `greedyAction`.  It is the reusable bridge needed by
P-QUO-01: any stationary selector that attains the Bellman optimum pointwise
has infinite discounted value equal to `V*`, including non-canonical selectors
chosen from a tied argmax set.
-/

namespace UEOT.V3.FiniteDiscountedControl

open Filter Topology
open CausalPolicy

universe uX uA

variable {X : Type uX} [Fintype X]
variable {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]

noncomputable local instance selectorActionDecidableEq (x : X) : DecidableEq (A x) :=
  Classical.decEq (A x)

/-- A stationary deterministic selector represented as a causal policy. -/
noncomputable def selectorPolicy (σ : ∀ x, A x) : CausalPolicy X A where
  Memory := fun _ => X
  current := fun x => x
  advance := fun _ _ y => y
  current_advance := by
    intro t h a y
    rfl
  actionProb := fun h a => if a = σ h then 1 else 0
  actionProb_nonneg := by
    intro t h a
    by_cases ha : a = σ h <;> simp [ha]
  actionProb_sum_one := by
    intro t h
    simp

@[simp] theorem selectorPolicy_current (σ : ∀ x, A x) {t : ℕ} (x : X) :
    (selectorPolicy σ).current (t := t) x = x := rfl

@[simp] theorem selectorPolicy_advance (σ : ∀ x, A x) {t : ℕ} (x : X)
    (a : A x) (y : X) :
    (selectorPolicy σ).advance (t := t) x a y = y := rfl

@[simp] theorem selectorPolicy_actionProb (σ : ∀ x, A x) {t : ℕ} (x : X) (a : A x) :
    (selectorPolicy σ).actionProb (t := t) x a = if a = σ x then 1 else 0 := rfl

/-- Under a deterministic stationary selector, the causal recursion reduces to
that selector's one-step policy-evaluation Bellman expression. -/
@[simp] theorem selector_truncatedValue_succ (M : Model X A) (σ : ∀ x, A x)
    (n : ℕ) {t : ℕ} (x : X) :
    truncatedValue (selectorPolicy σ) M (n + 1) (t := t) x =
      M.reward x (σ x) +
        M.discount * ∑ y, M.transition x (σ x) y *
          truncatedValue (selectorPolicy σ) M n (t := t + 1) y := by
  simp [truncatedValue_succ, selectorPolicy]

namespace Model

/-- Policy-evaluation Bellman map for an arbitrary stationary deterministic
selector. -/
noncomputable def selectorBellman (M : Model X A) (σ : ∀ x, A x)
    (v : X → ℝ) : X → ℝ :=
  fun x => M.qValue v x (σ x)

/-- Selector policy evaluation has the same discount Lipschitz constant as the
optimal Bellman map. -/
theorem selectorBellman_lipschitz (M : Model X A) (σ : ∀ x, A x) :
    LipschitzWith M.discountNN (M.selectorBellman σ) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro v w
  apply (dist_pi_le_iff (mul_nonneg (by positivity) dist_nonneg)).2
  intro x
  simpa [selectorBellman, Real.dist_eq] using
    M.abs_qValue_sub_le v w x (σ x)

/-- Selector policy evaluation is a contraction. -/
theorem selectorBellman_contracting (M : Model X A) (σ : ∀ x, A x) :
    ContractingWith M.discountNN (M.selectorBellman σ) := by
  refine ⟨?_, M.selectorBellman_lipschitz σ⟩
  change M.discount < 1
  exact M.discount_lt_one

/-- If a selector attains `V*` actionwise, then `V*` is a fixed point of its
policy-evaluation Bellman map. -/
theorem selectorBellman_optimal_fixed (M : Model X A) (σ : ∀ x, A x)
    (hσ : ∀ x, M.qValue M.optimalValue x (σ x) = M.optimalValue x) :
    M.selectorBellman σ M.optimalValue = M.optimalValue := by
  funext x
  exact hσ x

/-- Evaluation iterates of any pointwise Bellman-optimal selector converge from
every initial value to `V*`. -/
theorem selectorValueIteration_tendsto (M : Model X A) (σ : ∀ x, A x)
    (hσ : ∀ x, M.qValue M.optimalValue x (σ x) = M.optimalValue x)
    (v₀ : X → ℝ) :
    Tendsto (fun n => (M.selectorBellman σ)^[n] v₀) atTop (𝓝 M.optimalValue) := by
  have h := (M.selectorBellman_contracting σ).tendsto_iterate_fixedPoint v₀
  have hfix :
      ContractingWith.fixedPoint (M.selectorBellman σ) (M.selectorBellman_contracting σ) =
        M.optimalValue :=
    ((M.selectorBellman_contracting σ).fixedPoint_unique
      (M.selectorBellman_optimal_fixed σ hσ)).symm
  rw [hfix] at h
  exact h

end Model

/-- The finite-horizon value of a stationary deterministic selector is exactly
its policy-evaluation Bellman iterate from zero. -/
theorem selector_truncatedValue_eq_iterate (M : Model X A) (σ : ∀ x, A x) :
    ∀ (n : ℕ) (t : ℕ) (x : X),
      truncatedValue (selectorPolicy σ) M n (t := t) x =
        ((M.selectorBellman σ)^[n] (fun _ : X => (0 : ℝ))) x := by
  intro n
  induction n with
  | zero =>
      intro t x
      simp [truncatedValue]
  | succ n ih =>
      intro t x
      rw [selector_truncatedValue_succ (M := M) (σ := σ) (t := t),
        Function.iterate_succ_apply']
      simp only [Model.selectorBellman, Model.qValue, Model.expect]
      simp_rw [ih (t + 1)]

/-- Finite-horizon values of any pointwise Bellman-optimal stationary selector
converge to `V*`. -/
theorem selector_truncatedValue_tendsto_optimal (M : Model X A) (σ : ∀ x, A x)
    (hσ : ∀ x, M.qValue M.optimalValue x (σ x) = M.optimalValue x)
    {t : ℕ} (x : X) :
    Tendsto (fun n => truncatedValue (selectorPolicy σ) M n (t := t) x)
      atTop (𝓝 (M.optimalValue x)) := by
  have hfun := M.selectorValueIteration_tendsto σ hσ (fun _ : X => (0 : ℝ))
  have hx := tendsto_pi_nhds.mp hfun x
  exact hx.congr' <| Eventually.of_forall fun n =>
    (selector_truncatedValue_eq_iterate M σ n t x).symm

/-- Any stationary deterministic selector that attains the Bellman optimum
pointwise has infinite discounted value exactly `V*`.  This theorem is
intentionally selector-generic so quotient policy lifting preserves argmax ties. -/
theorem selector_infiniteValue_eq_optimal (M : Model X A) (σ : ∀ x, A x)
    (hσ : ∀ x, M.qValue M.optimalValue x (σ x) = M.optimalValue x)
    {t : ℕ} (x : X) :
    infiniteValue (selectorPolicy σ) M (t := t) x = M.optimalValue x := by
  exact tendsto_nhds_unique
    (truncatedValue_tendsto_infiniteValue (selectorPolicy σ) M (t := t) x)
    (selector_truncatedValue_tendsto_optimal M σ hσ (t := t) x)

/-- A pointwise Bellman-optimal stationary selector is optimal against the full
causal history-dependent randomized policy class. -/
theorem selector_optimal_against_all_causal (M : Model X A) (σ : ∀ x, A x)
    (hσ : ∀ x, M.qValue M.optimalValue x (σ x) = M.optimalValue x) :
    (∀ {t : ℕ} (x : X),
      infiniteValue (selectorPolicy σ) M (t := t) x = M.optimalValue x) ∧
    (∀ (π : CausalPolicy X A) {t : ℕ} (h : π.Memory t),
      infiniteValue π M h ≤ M.optimalValue (π.current h)) := by
  constructor
  · intro t x
    exact selector_infiniteValue_eq_optimal M σ hσ (t := t) x
  · intro π t h
    exact infiniteValue_le_optimal π M h

end UEOT.V3.FiniteDiscountedControl
