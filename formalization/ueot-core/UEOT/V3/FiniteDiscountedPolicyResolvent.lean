import UEOT.V3.FiniteDiscountedCausalInfinite
import Mathlib.Tactic

/-!
# P-QUO-04 infrastructure — stationary randomized policies and resolvent

This module introduces the stationary randomized policy object required by the
frozen Core 3 §20.4 fixed-policy identities.  It defines the induced reward and
Markov kernel, the fixed-policy Bellman operator and value, and a genuine
linear inverse for `I - β P^π`.
-/

namespace UEOT.V3.FiniteDiscountedControl

open Filter Topology

universe uX uA

variable {X : Type uX} [Fintype X]
variable {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]

/-- A stationary randomized policy for the finite controlled model. -/
structure StationaryPolicy (A : X → Type uA) [∀ x, Fintype (A x)] where
  prob : ∀ x, A x → ℝ
  prob_nonneg : ∀ x a, 0 ≤ prob x a
  prob_sum_one : ∀ x, ∑ a, prob x a = 1

namespace StationaryPolicy

/-- Deterministic selectors embed canonically as stationary randomized
policies. -/
noncomputable def ofSelector (σ : ∀ x, A x) : StationaryPolicy A := by
  classical
  exact
    { prob := fun x a => if a = σ x then 1 else 0
      prob_nonneg := by
        intro x a
        split <;> simp_all
      prob_sum_one := by
        intro x
        simp }

/-- A stationary randomized policy as a causal policy with current state as
its complete memory.  This is the semantic bridge to the existing causal
infinite-horizon value layer. -/
abbrev toCausalPolicy (π : StationaryPolicy A) : CausalPolicy X A where
  Memory := fun _ => X
  current := fun x => x
  advance := fun _ _ y => y
  current_advance := by intro t x a y; rfl
  actionProb := fun x a => π.prob x a
  actionProb_nonneg := π.prob_nonneg
  actionProb_sum_one := π.prob_sum_one

@[simp] theorem toCausalPolicy_current (π : StationaryPolicy A) {t : ℕ} (x : X) :
    π.toCausalPolicy.current (t := t) x = x := rfl

@[simp] theorem toCausalPolicy_actionProb (π : StationaryPolicy A) {t : ℕ}
    (x : X) (a : A x) :
    π.toCausalPolicy.actionProb (t := t) x a = π.prob x a := rfl

end StationaryPolicy

namespace Model

variable (M : Model X A)

/-- Reward induced by a fixed stationary randomized policy. -/
def policyReward (π : StationaryPolicy A) (x : X) : ℝ :=
  ∑ a, π.prob x a * M.reward x a

/-- Markov transition kernel induced by a fixed stationary randomized policy. -/
def policyTransition (π : StationaryPolicy A) (x y : X) : ℝ :=
  ∑ a, π.prob x a * M.transition x a y

theorem policyTransition_nonneg (π : StationaryPolicy A) (x y : X) :
    0 ≤ M.policyTransition π x y := by
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (π.prob_nonneg x a) (M.transition_nonneg x a y)

theorem policyTransition_sum_one (π : StationaryPolicy A) (x : X) :
    ∑ y, M.policyTransition π x y = 1 := by
  simp only [policyTransition]
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ y, π.prob x a * M.transition x a y) =
        ∑ a, π.prob x a * ∑ y, M.transition x a y := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ = ∑ a, π.prob x a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [M.transition_sum_one x a, mul_one]
    _ = 1 := π.prob_sum_one x

/-- One-step expectation under the policy-induced Markov kernel. -/
def policyExpect (π : StationaryPolicy A) (v : X → ℝ) (x : X) : ℝ :=
  ∑ y, M.policyTransition π x y * v y

theorem abs_policyExpect_sub_le_dist (π : StationaryPolicy A)
    (v w : X → ℝ) (x : X) :
    |M.policyExpect π v x - M.policyExpect π w x| ≤ dist v w := by
  simp only [policyExpect]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ y, (M.policyTransition π x y * v y -
      M.policyTransition π x y * w y)|
        ≤ ∑ y, |M.policyTransition π x y * v y -
          M.policyTransition π x y * w y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, M.policyTransition π x y * |v y - w y| := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← mul_sub, abs_mul, abs_of_nonneg (M.policyTransition_nonneg π x y)]
    _ ≤ ∑ y, M.policyTransition π x y * dist v w := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left
        (by simpa [Real.dist_eq] using dist_le_pi_dist v w y)
        (M.policyTransition_nonneg π x y)
    _ = dist v w := by
      rw [← Finset.sum_mul, M.policyTransition_sum_one π x, one_mul]

/-- Fixed-policy Bellman map `r^π + β P^π v`. -/
def policyBellman (π : StationaryPolicy A) (v : X → ℝ) : X → ℝ :=
  fun x => M.policyReward π x + M.discount * M.policyExpect π v x

theorem policyBellman_lipschitz (π : StationaryPolicy A) :
    LipschitzWith M.discountNN (M.policyBellman π) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro v w
  apply (dist_pi_le_iff (mul_nonneg (by positivity) dist_nonneg)).2
  intro x
  have h := M.abs_policyExpect_sub_le_dist π v w x
  have hβ : 0 ≤ M.discount := M.discount_pos.le
  simp only [policyBellman]
  rw [Real.dist_eq]
  calc
    |(M.policyReward π x + M.discount * M.policyExpect π v x) -
      (M.policyReward π x + M.discount * M.policyExpect π w x)|
        = M.discount * |M.policyExpect π v x - M.policyExpect π w x| := by
      rw [show
        (M.policyReward π x + M.discount * M.policyExpect π v x) -
          (M.policyReward π x + M.discount * M.policyExpect π w x) =
            M.discount * (M.policyExpect π v x - M.policyExpect π w x) by ring,
        abs_mul, abs_of_nonneg hβ]
    _ ≤ M.discount * dist v w := mul_le_mul_of_nonneg_left h hβ

theorem policyBellman_contracting (π : StationaryPolicy A) :
    ContractingWith M.discountNN (M.policyBellman π) := by
  refine ⟨?_, M.policyBellman_lipschitz π⟩
  change M.discount < 1
  exact M.discount_lt_one

/-- Exact infinite discounted value of the fixed stationary randomized policy. -/
noncomputable def policyValue (π : StationaryPolicy A) : X → ℝ :=
  ContractingWith.fixedPoint (M.policyBellman π) (M.policyBellman_contracting π)

theorem policyValue_fixed (π : StationaryPolicy A) :
    M.policyBellman π (M.policyValue π) = M.policyValue π :=
  (M.policyBellman_contracting π).fixedPoint_isFixedPt

theorem policyValue_unique (π : StationaryPolicy A) {v : X → ℝ}
    (hv : M.policyBellman π v = v) : v = M.policyValue π :=
  (M.policyBellman_contracting π).fixedPoint_unique hv

/-- Finite-horizon causal values of a stationary randomized policy are exactly
iterations of its fixed-policy Bellman map from zero. -/
theorem stationary_truncatedValue_eq_iterate (π : StationaryPolicy A) :
    ∀ (n : ℕ) (t : ℕ) (x : X),
      CausalPolicy.truncatedValue π.toCausalPolicy M n (t := t)
        (show π.toCausalPolicy.Memory t from x) =
        ((M.policyBellman π)^[n] (fun _ : X => (0 : ℝ))) x := by
  intro n
  induction n with
  | zero =>
      intro t x
      simp [CausalPolicy.truncatedValue]
  | succ n ih =>
      intro t x
      rw [CausalPolicy.truncatedValue_succ, Function.iterate_succ_apply']
      simp only [StationaryPolicy.toCausalPolicy_current,
        StationaryPolicy.toCausalPolicy_actionProb, policyBellman, policyReward,
        policyExpect, policyTransition]
      simp_rw [ih (t + 1)]
      calc
        (∑ a, π.prob x a *
            (M.reward x a + M.discount *
              ∑ y, M.transition x a y *
                ((M.policyBellman π)^[n] (fun _ : X => (0 : ℝ))) y)) =
            (∑ a, π.prob x a * M.reward x a) +
              M.discount *
                ∑ a, ∑ y, π.prob x a * M.transition x a y *
                  ((M.policyBellman π)^[n] (fun _ : X => (0 : ℝ))) y := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          have hs :
              (∑ y, π.prob x a * M.transition x a y *
                ((M.policyBellman π)^[n] (fun _ : X => (0 : ℝ))) y) =
                π.prob x a * ∑ y, M.transition x a y *
                  ((M.policyBellman π)^[n] (fun _ : X => (0 : ℝ))) y := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y hy
            ring
          rw [hs]
          ring
        _ = (∑ a, π.prob x a * M.reward x a) +
              M.discount *
                ∑ y, (∑ a, π.prob x a * M.transition x a y) *
                  ((M.policyBellman π)^[n] (fun _ : X => (0 : ℝ))) y := by
          congr 2
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.sum_mul]

/-- The fixed-point policy value is the same value supplied by the repository's
causal infinite-horizon semantics. -/
theorem stationary_infiniteValue_eq_policyValue (π : StationaryPolicy A)
    {t : ℕ} (x : X) :
    CausalPolicy.infiniteValue π.toCausalPolicy M (t := t)
      (show π.toCausalPolicy.Memory t from x) = M.policyValue π x := by
  have hfun := (M.policyBellman_contracting π).tendsto_iterate_fixedPoint
    (fun _ : X => (0 : ℝ))
  have hx := tendsto_pi_nhds.mp hfun x
  have htrunc :
      Tendsto
        (fun n => CausalPolicy.truncatedValue π.toCausalPolicy M n (t := t)
          (show π.toCausalPolicy.Memory t from x))
        atTop (𝓝 (M.policyValue π x)) := by
    exact hx.congr' <| Eventually.of_forall fun n =>
      (M.stationary_truncatedValue_eq_iterate π n t x).symm
  exact tendsto_nhds_unique
    (CausalPolicy.truncatedValue_tendsto_infiniteValue π.toCausalPolicy M (t := t) x)
    htrunc

/-- Linear policy transition operator `P^π`. -/
def policyTransitionLinear (π : StationaryPolicy A) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun := M.policyExpect π
  map_add' := by
    intro v w
    funext x
    simp [policyExpect, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    funext x
    change (∑ y, M.policyTransition π x y * (c * v y)) =
      c * ∑ y, M.policyTransition π x y * v y
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring

@[simp] theorem policyTransitionLinear_apply (π : StationaryPolicy A)
    (v : X → ℝ) (x : X) :
    M.policyTransitionLinear π v x = M.policyExpect π v x := rfl

/-- Source operator `I - β P^π`. -/
def policyResidualLinear (π : StationaryPolicy A) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) :=
  LinearMap.id - M.discount • M.policyTransitionLinear π

@[simp] theorem policyResidualLinear_apply (π : StationaryPolicy A)
    (v : X → ℝ) (x : X) :
    M.policyResidualLinear π v x = v x - M.discount * M.policyExpect π v x := by
  rfl

/-- Affine contraction whose fixed point solves `(I - β P^π)u = b`. -/
def policyForcingBellman (π : StationaryPolicy A) (b : X → ℝ) (u : X → ℝ) : X → ℝ :=
  fun x => b x + M.discount * M.policyExpect π u x

theorem policyForcingBellman_contracting (π : StationaryPolicy A) (b : X → ℝ) :
    ContractingWith M.discountNN (M.policyForcingBellman π b) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
  · change M.discount < 1
    exact M.discount_lt_one
  · intro v w
    apply (dist_pi_le_iff (mul_nonneg M.discount_pos.le dist_nonneg)).2
    intro x
    have h := M.abs_policyExpect_sub_le_dist π v w x
    simp only [policyForcingBellman, Real.dist_eq]
    rw [show
      (b x + M.discount * M.policyExpect π v x) -
        (b x + M.discount * M.policyExpect π w x) =
          M.discount * (M.policyExpect π v x - M.policyExpect π w x) by ring,
      abs_mul, abs_of_nonneg M.discount_pos.le]
    exact mul_le_mul_of_nonneg_left h M.discount_pos.le

/-- For a forcing term `b`, the resolvent is the unique fixed point of
`u ↦ b + β P^π u`.  The linear equivalence below proves that this is exactly
`(I - β P^π)⁻¹ b`. -/
noncomputable def policyResolvent (π : StationaryPolicy A) (b : X → ℝ) : X → ℝ :=
  ContractingWith.fixedPoint (M.policyForcingBellman π b)
    (M.policyForcingBellman_contracting π b)

theorem policyResolvent_fixed (π : StationaryPolicy A) (b : X → ℝ) :
    M.policyForcingBellman π b (M.policyResolvent π b) =
      M.policyResolvent π b := by
  exact (M.policyForcingBellman_contracting π b).fixedPoint_isFixedPt

theorem policyResidual_resolvent (π : StationaryPolicy A) (b : X → ℝ) :
    M.policyResidualLinear π (M.policyResolvent π b) = b := by
  funext x
  have h := congrFun (M.policyResolvent_fixed π b) x
  simp only [policyForcingBellman, policyResidualLinear_apply] at h ⊢
  linarith

theorem policyResolvent_residual (π : StationaryPolicy A) (v : X → ℝ) :
    M.policyResolvent π (M.policyResidualLinear π v) = v := by
  symm
  apply (M.policyForcingBellman_contracting π (M.policyResidualLinear π v)).fixedPoint_unique
  funext x
  simp [policyForcingBellman, policyResidualLinear_apply]


/-- The `n`-step policy expectation `((P^π)^n b)(x)`. -/
def policyExpectIterate (π : StationaryPolicy A) (n : ℕ) (b : X → ℝ) : X → ℝ :=
  (M.policyExpect π)^[n] b

@[simp] theorem policyExpectIterate_zero (π : StationaryPolicy A) (b : X → ℝ) :
    M.policyExpectIterate π 0 b = b := rfl

@[simp] theorem policyExpectIterate_succ (π : StationaryPolicy A) (n : ℕ) (b : X → ℝ) :
    M.policyExpectIterate π (n + 1) b = M.policyExpect π (M.policyExpectIterate π n b) := by
  simp [policyExpectIterate, Function.iterate_succ_apply']

theorem abs_policyExpectIterate_le_dist_zero (π : StationaryPolicy A)
    (n : ℕ) (b : X → ℝ) (x : X) :
    |M.policyExpectIterate π n b x| ≤ dist b 0 := by
  induction n generalizing x with
  | zero =>
      simpa [policyExpectIterate, Real.dist_eq] using dist_le_pi_dist b 0 x
  | succ n ih =>
      rw [policyExpectIterate_succ]
      have h := M.abs_policyExpect_sub_le_dist π (M.policyExpectIterate π n b) 0 x
      have hz : M.policyExpect π (0 : X → ℝ) x = 0 := by simp [policyExpect]
      rw [hz, sub_zero] at h
      have hd : dist (M.policyExpectIterate π n b) 0 ≤ dist b 0 :=
        (dist_pi_le_iff (dist_nonneg : 0 ≤ dist b 0)).2 (fun y => by
          simpa [Real.dist_eq] using ih y)
      exact h.trans hd

/-- Pointwise Neumann series `∑_{n≥0} β^n (P^π)^n b`. -/
noncomputable def policyNeumannSeries (π : StationaryPolicy A) (b : X → ℝ) (x : X) : ℝ :=
  ∑' n : ℕ, M.discount ^ n * M.policyExpectIterate π n b x

theorem summable_policyNeumannSeries (π : StationaryPolicy A) (b : X → ℝ) (x : X) :
    Summable (fun n : ℕ => M.discount ^ n * M.policyExpectIterate π n b x) := by
  refine ((summable_geometric_of_lt_one M.discount_pos.le M.discount_lt_one).mul_left (dist b 0)).of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg M.discount_pos.le n)]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left (M.abs_policyExpectIterate_le_dist_zero π n b x)
      (pow_nonneg M.discount_pos.le n)

/-- The Neumann series satisfies the same fixed-point equation as the resolvent. -/
theorem policyNeumannSeries_fixed (π : StationaryPolicy A) (b : X → ℝ) :
    M.policyForcingBellman π b (M.policyNeumannSeries π b) = M.policyNeumannSeries π b := by
  funext x
  classical
  have hs x := M.summable_policyNeumannSeries π b x
  have hstep :
      M.discount * M.policyExpect π (M.policyNeumannSeries π b) x =
        ∑' n : ℕ, M.discount ^ (n + 1) * M.policyExpectIterate π (n + 1) b x := by
    unfold policyExpect policyNeumannSeries
    calc
      M.discount * ∑ y, M.policyTransition π x y *
          (∑' n : ℕ, M.discount ^ n * M.policyExpectIterate π n b y) =
        ∑ y, ∑' n : ℕ, M.discount *
          (M.policyTransition π x y *
            (M.discount ^ n * M.policyExpectIterate π n b y)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          rw [← tsum_mul_left, ← tsum_mul_left]
      _ = ∑' n : ℕ, ∑ y, M.discount *
          (M.policyTransition π x y *
            (M.discount ^ n * M.policyExpectIterate π n b y)) := by
          rw [Summable.tsum_finsetSum]
          intro y hy
          exact (hs y).mul_left (M.policyTransition π x y) |>.mul_left M.discount
      _ = ∑' n : ℕ, M.discount ^ (n + 1) * M.policyExpectIterate π (n + 1) b x := by
          apply tsum_congr
          intro n
          rw [policyExpectIterate_succ]
          simp only [policyExpect]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          rw [pow_succ]
          ring
  unfold policyForcingBellman
  change b x + M.discount * M.policyExpect π (M.policyNeumannSeries π b) x =
    M.policyNeumannSeries π b x
  rw [hstep]
  unfold policyNeumannSeries
  rw [hs x |>.tsum_eq_zero_add]
  simp only [pow_zero, policyExpectIterate_zero, one_mul]

/-- The fixed-point resolvent is exactly its convergent Neumann series. -/
theorem policyResolvent_eq_neumann (π : StationaryPolicy A) (b : X → ℝ) :
    M.policyResolvent π b = M.policyNeumannSeries π b := by
  symm
  apply (M.policyForcingBellman_contracting π b).fixedPoint_unique
  exact M.policyNeumannSeries_fixed π b

/-- The source residual operator as a linear equivalence.  Its inverse is the
fixed-policy resolvent `(I - β P^π)⁻¹`. -/
noncomputable def policyResidualEquiv (π : StationaryPolicy A) :
    (X → ℝ) ≃ₗ[ℝ] (X → ℝ) where
  toLinearMap := M.policyResidualLinear π
  invFun := M.policyResolvent π
  left_inv := M.policyResolvent_residual π
  right_inv := M.policyResidual_resolvent π

@[simp] theorem policyResidualEquiv_symm_apply (π : StationaryPolicy A)
    (b : X → ℝ) :
    (M.policyResidualEquiv π).symm b = M.policyResolvent π b := rfl

/-- Frozen §20.4 policy residual `b_π = r^π + β P^π w - w`. -/
def policyReferenceResidual (π : StationaryPolicy A) (w : X → ℝ) : X → ℝ :=
  fun x => M.policyReward π x + M.discount * M.policyExpect π w x - w x

/-- Exact source-level resolvent identity from frozen §20.4. -/
theorem policyValue_sub_reference_eq_resolvent (π : StationaryPolicy A) (w : X → ℝ) :
    M.policyValue π - w = M.policyResolvent π (M.policyReferenceResidual π w) := by
  symm
  rw [← M.policyResolvent_residual π (M.policyValue π - w)]
  congr 1
  funext x
  have hV := congrFun (M.policyValue_fixed π) x
  simp only [policyBellman] at hV
  simp only [policyResidualLinear_apply, policyReferenceResidual, Pi.sub_apply]
  have hlin :
      M.policyExpect π (M.policyValue π - w) x =
        M.policyExpect π (M.policyValue π) x - M.policyExpect π w x := by
    change
      (∑ y, M.policyTransition π x y * (M.policyValue π y - w y)) =
        (∑ y, M.policyTransition π x y * M.policyValue π y) -
          ∑ y, M.policyTransition π x y * w y
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [hlin]
  linarith

end Model

end UEOT.V3.FiniteDiscountedControl
