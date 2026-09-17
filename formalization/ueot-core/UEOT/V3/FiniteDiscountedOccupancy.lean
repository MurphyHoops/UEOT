import UEOT.V3.FiniteDiscountedPolicyResolvent
import Mathlib.Tactic

/-!
# P-QUO-04 infrastructure — finite discounted occupancy

For a finite initial probability row `μ` and a stationary randomized policy
`π`, this module defines the policy evolution `μ_t = μ (P^π)^t` and the frozen
§20.4 discounted occupancy

`d_μ^π = (1 - β) * ∑_{t ≥ 0} β^t μ_t`.

The occupancy is proved to be a probability row, to satisfy its exact
fixed-point equation, and to evaluate the fixed-policy resolvent exactly.  A
state-action occupancy is exposed from the same policy semantics for P-QUO-05.
-/

namespace UEOT.V3.FiniteDiscountedControl

universe uX uA

variable {X : Type uX} [Fintype X]
variable {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]

/-- A finite probability row on the state space. -/
structure ProbabilityRow (X : Type uX) [Fintype X] where
  prob : X → ℝ
  prob_nonneg : ∀ x, 0 ≤ prob x
  prob_sum_one : ∑ x, prob x = 1

namespace ProbabilityRow

variable (μ : ProbabilityRow X)

/-- Expectation of a state function against a finite probability row. -/
def expect (v : X → ℝ) : ℝ :=
  ∑ x, μ.prob x * v x

theorem prob_le_one (x : X) : μ.prob x ≤ 1 := by
  classical
  calc
    μ.prob x ≤ ∑ y, μ.prob y := by
      exact Finset.single_le_sum (fun y _ => μ.prob_nonneg y) (Finset.mem_univ x)
    _ = 1 := μ.prob_sum_one

theorem expect_congr {v w : X → ℝ} (h : ∀ x, v x = w x) :
    μ.expect v = μ.expect w := by
  classical
  unfold expect
  apply Finset.sum_congr rfl
  intro x hx
  rw [h x]

theorem expect_add (v w : X → ℝ) :
    μ.expect (v + w) = μ.expect v + μ.expect w := by
  classical
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_smul (c : ℝ) (v : X → ℝ) :
    μ.expect (c • v) = c * μ.expect v := by
  classical
  simp only [expect, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

end ProbabilityRow

namespace Model

variable (M : Model X A)

/-- One forward row step under the policy-induced Markov kernel. -/
def policyRowStep (π : StationaryPolicy A) (μ : ProbabilityRow X) : ProbabilityRow X := by
  classical
  exact
    { prob := fun y => ∑ x, μ.prob x * M.policyTransition π x y
      prob_nonneg := by
        intro y
        exact Finset.sum_nonneg fun x _ =>
          mul_nonneg (μ.prob_nonneg x) (M.policyTransition_nonneg π x y)
      prob_sum_one := by
        rw [Finset.sum_comm]
        calc
          (∑ x, ∑ y, μ.prob x * M.policyTransition π x y) =
              ∑ x, μ.prob x * ∑ y, M.policyTransition π x y := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
          _ = ∑ x, μ.prob x := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [M.policyTransition_sum_one π x, mul_one]
          _ = 1 := μ.prob_sum_one }

@[simp] theorem policyRowStep_prob (π : StationaryPolicy A) (μ : ProbabilityRow X) (y : X) :
    (M.policyRowStep π μ).prob y = ∑ x, μ.prob x * M.policyTransition π x y := rfl

/-- Evolution of the initial row under repeated multiplication by `P^π`. -/
def policyStateRow (π : StationaryPolicy A) (μ : ProbabilityRow X) : ℕ → ProbabilityRow X
  | 0 => μ
  | t + 1 => M.policyRowStep π (policyStateRow π μ t)

@[simp] theorem policyStateRow_zero (π : StationaryPolicy A) (μ : ProbabilityRow X) :
    M.policyStateRow π μ 0 = μ := rfl

@[simp] theorem policyStateRow_succ (π : StationaryPolicy A) (μ : ProbabilityRow X) (t : ℕ) :
    M.policyStateRow π μ (t + 1) = M.policyRowStep π (M.policyStateRow π μ t) := rfl

theorem policyRowStep_expect (π : StationaryPolicy A) (μ : ProbabilityRow X) (v : X → ℝ) :
    (M.policyRowStep π μ).expect v = μ.expect (M.policyExpect π v) := by
  classical
  simp only [ProbabilityRow.expect, policyRowStep_prob, policyExpect]
  calc
    (∑ y, (∑ x, μ.prob x * M.policyTransition π x y) * v y) =
        ∑ y, ∑ x, (μ.prob x * M.policyTransition π x y) * v y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_mul]
    _ = ∑ x, ∑ y, (μ.prob x * M.policyTransition π x y) * v y := by
      rw [Finset.sum_comm]
    _ = ∑ x, μ.prob x * ∑ y, M.policyTransition π x y * v y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring

/-- The scalar discounted series at a state before multiplying by `1 - β`. -/
noncomputable def discountedStateSeries
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (x : X) : ℝ :=
  ∑' t : ℕ, M.discount ^ t * (M.policyStateRow π μ t).prob x

theorem summable_discount_stateProb
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (x : X) :
    Summable (fun t : ℕ => M.discount ^ t * (M.policyStateRow π μ t).prob x) := by
  refine (summable_geometric_of_lt_one M.discount_pos.le M.discount_lt_one).of_norm_bounded ?_
  intro t
  have hβ : 0 ≤ M.discount ^ t := pow_nonneg M.discount_pos.le t
  have hp0 : 0 ≤ (M.policyStateRow π μ t).prob x :=
    (M.policyStateRow π μ t).prob_nonneg x
  have hp1 : (M.policyStateRow π μ t).prob x ≤ 1 :=
    (M.policyStateRow π μ t).prob_le_one x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hβ hp0)]
  simpa using mul_le_mul_of_nonneg_left hp1 hβ

theorem discountedStateSeries_nonneg
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (x : X) :
    0 ≤ M.discountedStateSeries π μ x := by
  unfold discountedStateSeries
  exact tsum_nonneg fun t =>
    mul_nonneg (pow_nonneg M.discount_pos.le t) ((M.policyStateRow π μ t).prob_nonneg x)

/-- Frozen §20.4 state occupancy, exactly
`(1-β) * ∑_{t≥0} β^t μ(P^π)^t`. -/
noncomputable def discountedStateOccupancyProb
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (x : X) : ℝ :=
  (1 - M.discount) * M.discountedStateSeries π μ x

theorem discountedStateOccupancyProb_nonneg
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (x : X) :
    0 ≤ M.discountedStateOccupancyProb π μ x := by
  exact mul_nonneg (sub_nonneg.mpr M.discount_lt_one.le)
    (M.discountedStateSeries_nonneg π μ x)

theorem discountedStateOccupancyProb_sum_one
    (π : StationaryPolicy A) (μ : ProbabilityRow X) :
    ∑ x, M.discountedStateOccupancyProb π μ x = 1 := by
  classical
  have hswap :
      (∑' t : ℕ, ∑ x, M.discount ^ t * (M.policyStateRow π μ t).prob x) =
        ∑ x, ∑' t : ℕ, M.discount ^ t * (M.policyStateRow π μ t).prob x := by
    simpa using
      (Summable.tsum_finsetSum
        (s := (Finset.univ : Finset X))
        (f := fun x t => M.discount ^ t * (M.policyStateRow π μ t).prob x)
        (fun x hx => M.summable_discount_stateProb π μ x))
  calc
    ∑ x, M.discountedStateOccupancyProb π μ x =
        (1 - M.discount) * ∑ x, M.discountedStateSeries π μ x := by
      simp only [discountedStateOccupancyProb]
      rw [Finset.mul_sum]
    _ = (1 - M.discount) *
        ∑' t : ℕ, ∑ x, M.discount ^ t * (M.policyStateRow π μ t).prob x := by
      simp only [discountedStateSeries]
      rw [hswap]
    _ = (1 - M.discount) * ∑' t : ℕ, M.discount ^ t := by
      congr 1
      apply tsum_congr
      intro t
      rw [← Finset.mul_sum, (M.policyStateRow π μ t).prob_sum_one, mul_one]
    _ = (1 - M.discount) * (1 - M.discount)⁻¹ := by
      rw [tsum_geometric_of_lt_one M.discount_pos.le M.discount_lt_one]
    _ = 1 := by
      apply mul_inv_cancel₀
      linarith [M.discount_lt_one]

/-- The discounted state occupancy packaged as a probability row. -/
noncomputable def discountedStateOccupancy
    (π : StationaryPolicy A) (μ : ProbabilityRow X) : ProbabilityRow X where
  prob := M.discountedStateOccupancyProb π μ
  prob_nonneg := M.discountedStateOccupancyProb_nonneg π μ
  prob_sum_one := M.discountedStateOccupancyProb_sum_one π μ

@[simp] theorem discountedStateOccupancy_prob
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (x : X) :
    (M.discountedStateOccupancy π μ).prob x =
      (1 - M.discount) * ∑' t : ℕ,
        M.discount ^ t * (M.policyStateRow π μ t).prob x := rfl

/-- The unnormalized discounted series satisfies the row resolvent equation. -/
theorem discountedStateSeries_fixed
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (y : X) :
    M.discountedStateSeries π μ y = μ.prob y +
      M.discount * ∑ x, M.discountedStateSeries π μ x * M.policyTransition π x y := by
  classical
  have hy := M.summable_discount_stateProb π μ y
  have htail :
      (∑' t : ℕ,
          M.discount ^ (t + 1) * (M.policyStateRow π μ (t + 1)).prob y) =
        M.discount * ∑ x,
          M.discountedStateSeries π μ x * M.policyTransition π x y := by
    calc
      (∑' t : ℕ,
          M.discount ^ (t + 1) * (M.policyStateRow π μ (t + 1)).prob y) =
          M.discount * ∑' t : ℕ,
            M.discount ^ t * (M.policyStateRow π μ (t + 1)).prob y := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro t
        rw [pow_succ]
        ring
      _ = M.discount * ∑' t : ℕ, ∑ x,
            (M.discount ^ t * (M.policyStateRow π μ t).prob x) *
              M.policyTransition π x y := by
        congr 1
        apply tsum_congr
        intro t
        simp only [policyStateRow_succ, policyRowStep_prob]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = M.discount * ∑ x, ∑' t : ℕ,
            (M.discount ^ t * (M.policyStateRow π μ t).prob x) *
              M.policyTransition π x y := by
        congr 1
        rw [Summable.tsum_finsetSum]
        intro x hx
        exact (M.summable_discount_stateProb π μ x).mul_right (M.policyTransition π x y)
      _ = M.discount * ∑ x,
            M.discountedStateSeries π μ x * M.policyTransition π x y := by
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        unfold discountedStateSeries
        rw [(M.summable_discount_stateProb π μ x).tsum_mul_right]
  change
    (∑' t : ℕ, M.discount ^ t * (M.policyStateRow π μ t).prob y) =
      μ.prob y + M.discount * ∑ x,
        M.discountedStateSeries π μ x * M.policyTransition π x y
  rw [hy.tsum_eq_zero_add]
  simp only [pow_zero, one_mul, policyStateRow_zero]
  rw [htail]

/-- Exact discounted-occupancy row fixed point
`d = (1-β) μ + β d P^π`. -/
theorem discountedStateOccupancy_fixed
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (y : X) :
    (M.discountedStateOccupancy π μ).prob y =
      (1 - M.discount) * μ.prob y +
        M.discount * ∑ x,
          (M.discountedStateOccupancy π μ).prob x * M.policyTransition π x y := by
  classical
  change
    (1 - M.discount) * M.discountedStateSeries π μ y =
      (1 - M.discount) * μ.prob y +
        M.discount * ∑ x,
          ((1 - M.discount) * M.discountedStateSeries π μ x) *
            M.policyTransition π x y
  rw [M.discountedStateSeries_fixed π μ y]
  have hsum :
      (∑ x, ((1 - M.discount) * M.discountedStateSeries π μ x) *
          M.policyTransition π x y) =
        (1 - M.discount) * ∑ x,
          M.discountedStateSeries π μ x * M.policyTransition π x y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hsum]
  ring

/-- Expectation form of the occupancy fixed point:
`E_d[v] = (1-β) E_μ[v] + β E_d[P^π v]`. -/
theorem discountedStateOccupancy_expect_fixed
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (v : X → ℝ) :
    (M.discountedStateOccupancy π μ).expect v =
      (1 - M.discount) * μ.expect v +
        M.discount * (M.discountedStateOccupancy π μ).expect (M.policyExpect π v) := by
  classical
  let d := M.discountedStateOccupancy π μ
  calc
    d.expect v =
        ∑ y, ((1 - M.discount) * μ.prob y +
          M.discount * (M.policyRowStep π d).prob y) * v y := by
      unfold ProbabilityRow.expect
      apply Finset.sum_congr rfl
      intro y hy
      congr 1
      simpa [d, policyRowStep_prob] using M.discountedStateOccupancy_fixed π μ y
    _ = (1 - M.discount) * μ.expect v +
          M.discount * (M.policyRowStep π d).expect v := by
      simp only [add_mul, Finset.sum_add_distrib, ProbabilityRow.expect]
      rw [Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro x hx <;> ring
    _ = (1 - M.discount) * μ.expect v +
          M.discount * d.expect (M.policyExpect π v) := by
      rw [M.policyRowStep_expect π d v]

/-- Exact §20.4 occupancy evaluation of the resolvent:
`μ (I-βP^π)⁻¹ b = E_{d_μ^π}[b] / (1-β)`. -/
theorem initial_expect_policyResolvent_eq_occupancy_expect_div
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (b : X → ℝ) :
    μ.expect (M.policyResolvent π b) =
      (M.discountedStateOccupancy π μ).expect b / (1 - M.discount) := by
  let u := M.policyResolvent π b
  let d := M.discountedStateOccupancy π μ
  have hocc := M.discountedStateOccupancy_expect_fixed π μ u
  have hu : ∀ x, u x = b x + M.discount * M.policyExpect π u x := by
    intro x
    have h := congrFun (M.policyResolvent_fixed π b) x
    simpa [u, policyForcingBellman] using h.symm
  have hres : d.expect u = d.expect b + M.discount * d.expect (M.policyExpect π u) := by
    calc
      d.expect u = d.expect (b + M.discount • M.policyExpect π u) := by
        apply d.expect_congr
        intro x
        simpa using hu x
      _ = d.expect b + d.expect (M.discount • M.policyExpect π u) :=
        d.expect_add b (M.discount • M.policyExpect π u)
      _ = d.expect b + M.discount * d.expect (M.policyExpect π u) := by
        rw [d.expect_smul]
  have hmain : (1 - M.discount) * μ.expect u = d.expect b := by
    linarith
  apply (eq_div_iff (by linarith [M.discount_lt_one] : 1 - M.discount ≠ 0)).2
  simpa [u, d, mul_comm] using hmain

/-- Frozen §20.4 source-facing expectation identity for the reference residual. -/
theorem policyValue_sub_reference_initial_expect_eq_occupancy
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (w : X → ℝ) :
    μ.expect (M.policyValue π - w) =
      (M.discountedStateOccupancy π μ).expect (M.policyReferenceResidual π w) /
        (1 - M.discount) := by
  rw [M.policyValue_sub_reference_eq_resolvent π w]
  exact M.initial_expect_policyResolvent_eq_occupancy_expect_div π μ
    (M.policyReferenceResidual π w)

/-- Discounted state-action occupancy induced by the same state occupancy and
stationary randomized policy. -/
noncomputable def discountedStateActionOccupancy
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (x : X) (a : A x) : ℝ :=
  (M.discountedStateOccupancy π μ).prob x * π.prob x a

theorem discountedStateActionOccupancy_nonneg
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (x : X) (a : A x) :
    0 ≤ M.discountedStateActionOccupancy π μ x a :=
  mul_nonneg ((M.discountedStateOccupancy π μ).prob_nonneg x) (π.prob_nonneg x a)

theorem discountedStateActionOccupancy_stateMarginal
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (x : X) :
    ∑ a, M.discountedStateActionOccupancy π μ x a =
      (M.discountedStateOccupancy π μ).prob x := by
  classical
  unfold discountedStateActionOccupancy
  rw [← Finset.mul_sum, π.prob_sum_one x, mul_one]

theorem discountedStateActionOccupancy_sum_one
    (π : StationaryPolicy A) (μ : ProbabilityRow X) :
    ∑ x, ∑ a, M.discountedStateActionOccupancy π μ x a = 1 := by
  classical
  simp_rw [M.discountedStateActionOccupancy_stateMarginal π μ]
  exact (M.discountedStateOccupancy π μ).prob_sum_one

/-- Expectation of a state-action observable against discounted occupancy. -/
noncomputable def discountedStateActionExpect
    (π : StationaryPolicy A) (μ : ProbabilityRow X)
    (g : ∀ x, A x → ℝ) : ℝ :=
  ∑ x, ∑ a, M.discountedStateActionOccupancy π μ x a * g x a


/-- Source-facing P-QUO-04 closure.  It packages the frozen §20.4 resolvent
identity together with its convergent Neumann representation, the exact
discounted state occupancy and row fixed point, the exact occupancy expectation
identity, and the state-action occupancy induced by the same stationary policy. -/
theorem p_quo_04
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (w : X → ℝ) :
    (M.policyValue π - w = M.policyResolvent π (M.policyReferenceResidual π w)) ∧
    (M.policyResolvent π (M.policyReferenceResidual π w) =
      M.policyNeumannSeries π (M.policyReferenceResidual π w)) ∧
    (∀ x,
      (M.discountedStateOccupancy π μ).prob x =
        (1 - M.discount) * ∑' t : ℕ,
          M.discount ^ t * (M.policyStateRow π μ t).prob x) ∧
    (∀ y,
      (M.discountedStateOccupancy π μ).prob y =
        (1 - M.discount) * μ.prob y +
          M.discount * ∑ x,
            (M.discountedStateOccupancy π μ).prob x * M.policyTransition π x y) ∧
    (μ.expect (M.policyValue π - w) =
      (M.discountedStateOccupancy π μ).expect (M.policyReferenceResidual π w) /
        (1 - M.discount)) ∧
    (∀ x,
      ∑ a, M.discountedStateActionOccupancy π μ x a =
        (M.discountedStateOccupancy π μ).prob x) ∧
    (∑ x, ∑ a, M.discountedStateActionOccupancy π μ x a = 1) := by
  refine ⟨M.policyValue_sub_reference_eq_resolvent π w,
    M.policyResolvent_eq_neumann π (M.policyReferenceResidual π w), ?_, ?_,
    M.policyValue_sub_reference_initial_expect_eq_occupancy π μ w, ?_, ?_⟩
  · intro x
    rfl
  · exact M.discountedStateOccupancy_fixed π μ
  · exact M.discountedStateActionOccupancy_stateMarginal π μ
  · exact M.discountedStateActionOccupancy_sum_one π μ

end Model

end UEOT.V3.FiniteDiscountedControl
