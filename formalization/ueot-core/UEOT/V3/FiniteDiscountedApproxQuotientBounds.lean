import UEOT.V3.FiniteDiscountedApproxQuotient
import Mathlib.Tactic

/-!
# P-QUO-02 — span-sensitive value and policy-regret bounds

This module closes the frozen source theorem after the true-TV foundation.
The comparison function is the pullback of the macro optimal value.  The
all-action TV/span estimate gives both the optimal Bellman residual and the
fixed lifted-policy residual.  The P-CTL-01 contraction certificates then give
the `D` value bounds, and causal-policy domination plus the two `D` bounds gives
the source `2D` regret certificate.
-/

namespace UEOT.V3.FiniteDiscountedControl

open CausalPolicy

universe uX uY uA

variable {X : Type uX} [Fintype X]
variable {Y : Type uY} [Fintype Y]
variable {Abar : Y → Type uA} [∀ y, Fintype (Abar y)] [∀ y, Nonempty (Abar y)]

namespace ApproxControlQuotient

variable (Q : ApproxControlQuotient X Y Abar)

/-- Frozen-source comparison function `w = Vbar* ∘ f`. -/
noncomputable def w : X → ℝ :=
  Q.pullback Q.macroModel.optimalValue

/-- Frozen-source one-step comparison error
`δ = ε_r + β ε_p sp(Vbar*)`. -/
noncomputable def delta : ℝ :=
  Q.epsilonReward +
    Q.macroModel.discount * Q.epsilonTransition *
      UEOT.V3.TVSpan.span Q.macroModel.optimalValue

/-- Frozen-source global error radius `D = δ / (1 - β)`. -/
noncomputable def D : ℝ :=
  Q.delta / (1 - Q.macroModel.discount)

/-- The frozen one-step error radius is nonnegative. -/
theorem delta_nonneg : 0 ≤ Q.delta := by
  unfold delta
  exact add_nonneg Q.epsilonReward_nonneg <|
    mul_nonneg
      (mul_nonneg Q.macroModel.discount_pos.le Q.epsilonTransition_nonneg)
      (FiniteProbabilityRow.span_nonneg Q.macroModel.optimalValue)

/-- The frozen global radius is nonnegative. -/
theorem D_nonneg : 0 ≤ Q.D := by
  unfold D
  exact div_nonneg Q.delta_nonneg (sub_nonneg.mpr Q.macroModel.discount_lt_one.le)

/-- Reward approximation plus the true-TV/span continuation bound gives the
frozen actionwise Bellman-expression error. -/
theorem abs_qValue_pullback_sub_le
    (x : X) (a : Abar (Q.f x)) (v : Y → ℝ) :
    |Q.micro.qValue (Q.pullback v) x a -
      Q.macroModel.qValue v (Q.f x) a| ≤
      Q.epsilonReward +
        Q.macroModel.discount * Q.epsilonTransition *
          UEOT.V3.TVSpan.span v := by
  have hr := Q.reward_approx x a
  have he := Q.abs_expect_pullback_sub_le_span x a v
  have hβ : 0 ≤ Q.macroModel.discount := Q.macroModel.discount_pos.le
  simp only [Model.qValue]
  rw [Q.discount_eq]
  calc
    |(Q.micro.reward x a +
          Q.macroModel.discount * Q.micro.expect x a (Q.pullback v)) -
        (Q.macroModel.reward (Q.f x) a +
          Q.macroModel.discount * Q.macroModel.expect (Q.f x) a v)|
        ≤ |Q.micro.reward x a - Q.macroModel.reward (Q.f x) a| +
            |Q.macroModel.discount *
              (Q.micro.expect x a (Q.pullback v) -
                Q.macroModel.expect (Q.f x) a v)| := by
          rw [show
            (Q.micro.reward x a +
                Q.macroModel.discount * Q.micro.expect x a (Q.pullback v)) -
              (Q.macroModel.reward (Q.f x) a +
                Q.macroModel.discount * Q.macroModel.expect (Q.f x) a v) =
              (Q.micro.reward x a - Q.macroModel.reward (Q.f x) a) +
                Q.macroModel.discount *
                  (Q.micro.expect x a (Q.pullback v) -
                    Q.macroModel.expect (Q.f x) a v) by ring]
          exact abs_add_le _ _
    _ = |Q.micro.reward x a - Q.macroModel.reward (Q.f x) a| +
          Q.macroModel.discount *
            |Q.micro.expect x a (Q.pullback v) -
              Q.macroModel.expect (Q.f x) a v| := by
          rw [abs_mul, abs_of_nonneg hβ]
    _ ≤ Q.epsilonReward +
          Q.macroModel.discount *
            (UEOT.V3.TVSpan.span v * Q.epsilonTransition) :=
          add_le_add hr (mul_le_mul_of_nonneg_left he hβ)
    _ = Q.epsilonReward +
          Q.macroModel.discount * Q.epsilonTransition *
            UEOT.V3.TVSpan.span v := by ring

/-- Finite maximization over the common action set preserves the same
actionwise approximation radius. -/
theorem abs_bellman_pullback_sub_le
    (x : X) (v : Y → ℝ) :
    |Q.micro.bellman (Q.pullback v) x -
      Q.macroModel.bellman v (Q.f x)| ≤
      Q.epsilonReward +
        Q.macroModel.discount * Q.epsilonTransition *
          UEOT.V3.TVSpan.span v := by
  obtain ⟨amicro, hamicro_mem, hamicro⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Abar (Q.f x))))
      Finset.univ_nonempty
      (fun a => Q.micro.qValue (Q.pullback v) x a)
  obtain ⟨amacro, hamacro_mem, hamacro⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Abar (Q.f x))))
      Finset.univ_nonempty
      (fun a => Q.macroModel.qValue v (Q.f x) a)
  have hmicro := Q.abs_qValue_pullback_sub_le x amicro v
  have hmacro := Q.abs_qValue_pullback_sub_le x amacro v
  have hmacro_max :
      Q.macroModel.qValue v (Q.f x) amicro ≤
        Q.macroModel.qValue v (Q.f x) amacro := by
    rw [← hamacro]
    exact Finset.le_sup'
      (fun a : Abar (Q.f x) => Q.macroModel.qValue v (Q.f x) a)
      hamicro_mem
  have hmicro_max :
      Q.micro.qValue (Q.pullback v) x amacro ≤
        Q.micro.qValue (Q.pullback v) x amicro := by
    rw [← hamicro]
    exact Finset.le_sup'
      (fun a : Abar (Q.f x) => Q.micro.qValue (Q.pullback v) x a)
      hamacro_mem
  change
    |(Finset.univ.sup' Finset.univ_nonempty
        (fun a : Abar (Q.f x) => Q.micro.qValue (Q.pullback v) x a)) -
      (Finset.univ.sup' Finset.univ_nonempty
        (fun a : Abar (Q.f x) => Q.macroModel.qValue v (Q.f x) a))| ≤ _
  rw [hamicro, hamacro, abs_le]
  constructor
  · have hlower := (abs_le.mp hmacro).1
    linarith
  · have hupper := (abs_le.mp hmicro).2
    linarith

/-- The pulled-back macro optimal value has optimal Bellman residual at most
`δ` in every micro state. -/
theorem optimalBellman_residual_pointwise (x : X) :
    |Q.micro.bellman Q.w x - Q.w x| ≤ Q.delta := by
  have h :=
    Q.abs_bellman_pullback_sub_le x Q.macroModel.optimalValue
  have hfix :
      Q.macroModel.bellman Q.macroModel.optimalValue (Q.f x) =
        Q.macroModel.optimalValue (Q.f x) :=
    congrFun Q.macroModel.optimalValue_fixed (Q.f x)
  rw [hfix] at h
  simpa [w, delta] using h

/-- Sup-metric form of the optimal Bellman residual bound. -/
theorem optimalBellman_residual :
    dist Q.w (Q.micro.bellman Q.w) ≤ Q.delta := by
  apply (dist_pi_le_iff Q.delta_nonneg).2
  intro x
  simpa [Real.dist_eq, abs_sub_comm] using Q.optimalBellman_residual_pointwise x

/-- First frozen conclusion: the micro optimal value is within `D` of the
pulled-back macro optimal value.  On a finite product this metric is exactly the
sup metric characterized by `dist_pi_le_iff`. -/
theorem optimalValue_dist_w_le :
    dist Q.micro.optimalValue Q.w ≤ Q.D := by
  have hcert := Q.micro.valueError_le_residual Q.w
  have hres := Q.optimalBellman_residual
  have hden : 0 ≤ 1 - Q.micro.discount :=
    sub_nonneg.mpr Q.micro.discount_lt_one.le
  calc
    dist Q.micro.optimalValue Q.w = dist Q.w Q.micro.optimalValue := dist_comm _ _
    _ ≤ dist Q.w (Q.micro.bellman Q.w) / (1 - Q.micro.discount) := hcert
    _ ≤ Q.delta / (1 - Q.micro.discount) :=
      div_le_div_of_nonneg_right hres hden
    _ = Q.D := by simp [D, Q.discount_eq]

/-- Lift a macro stationary selector through the quotient map. -/
def liftSelector (σbar : ∀ y, Abar y) : ∀ x, Abar (Q.f x) :=
  fun x => σbar (Q.f x)

@[simp] theorem liftSelector_apply (σbar : ∀ y, Abar y) (x : X) :
    Q.liftSelector σbar x = σbar (Q.f x) := rfl

/-- Any macro selector attaining the macro Bellman optimum gives the same `δ`
residual for its lifted micro policy-evaluation Bellman map.  No uniqueness of
the macro argmax is assumed. -/
theorem selectorBellman_residual_pointwise
    (σbar : ∀ y, Abar y)
    (hσbar : ∀ y,
      Q.macroModel.qValue Q.macroModel.optimalValue y (σbar y) =
        Q.macroModel.optimalValue y)
    (x : X) :
    |Q.micro.selectorBellman (Q.liftSelector σbar) Q.w x - Q.w x| ≤ Q.delta := by
  have h := Q.abs_qValue_pullback_sub_le
    x (σbar (Q.f x)) Q.macroModel.optimalValue
  rw [hσbar (Q.f x)] at h
  simpa [Model.selectorBellman, liftSelector, w, delta] using h

/-- Sup-metric lifted-policy Bellman residual bound. -/
theorem selectorBellman_residual
    (σbar : ∀ y, Abar y)
    (hσbar : ∀ y,
      Q.macroModel.qValue Q.macroModel.optimalValue y (σbar y) =
        Q.macroModel.optimalValue y) :
    dist Q.w (Q.micro.selectorBellman (Q.liftSelector σbar) Q.w) ≤ Q.delta := by
  apply (dist_pi_le_iff Q.delta_nonneg).2
  intro x
  simpa [Real.dist_eq, abs_sub_comm] using
    Q.selectorBellman_residual_pointwise σbar hσbar x

/-- The value of every lifted tied macro-optimal stationary selector lies within
`D` of `w`. -/
theorem selectorValue_dist_w_le
    (σbar : ∀ y, Abar y)
    (hσbar : ∀ y,
      Q.macroModel.qValue Q.macroModel.optimalValue y (σbar y) =
        Q.macroModel.optimalValue y) :
    dist (Q.micro.selectorValue (Q.liftSelector σbar)) Q.w ≤ Q.D := by
  have hcert :=
    Q.micro.selectorValueError_le_residual (Q.liftSelector σbar) Q.w
  have hres := Q.selectorBellman_residual σbar hσbar
  have hden : 0 ≤ 1 - Q.micro.discount :=
    sub_nonneg.mpr Q.micro.discount_lt_one.le
  calc
    dist (Q.micro.selectorValue (Q.liftSelector σbar)) Q.w =
        dist Q.w (Q.micro.selectorValue (Q.liftSelector σbar)) := dist_comm _ _
    _ ≤ dist Q.w (Q.micro.selectorBellman (Q.liftSelector σbar) Q.w) /
          (1 - Q.micro.discount) := hcert
    _ ≤ Q.delta / (1 - Q.micro.discount) :=
      div_le_div_of_nonneg_right hres hden
    _ = Q.D := by simp [D, Q.discount_eq]

/-- Second frozen conclusion for any (possibly tied) macro-optimal stationary
selector: its lift has pointwise micro regret between zero and `2D`. -/
theorem liftSelector_regret_le_two_D
    (σbar : ∀ y, Abar y)
    (hσbar : ∀ y,
      Q.macroModel.qValue Q.macroModel.optimalValue y (σbar y) =
        Q.macroModel.optimalValue y)
    {t : ℕ} (x : X) :
    0 ≤ Q.micro.optimalValue x -
      infiniteValue (selectorPolicy (Q.liftSelector σbar)) Q.micro (t := t) x ∧
    Q.micro.optimalValue x -
      infiniteValue (selectorPolicy (Q.liftSelector σbar)) Q.micro (t := t) x ≤
      2 * Q.D := by
  have hdom :=
    infiniteValue_le_optimal
      (selectorPolicy (Q.liftSelector σbar)) Q.micro (t := t) x
  have hinf :=
    selector_infiniteValue_eq_selectorValue
      Q.micro (Q.liftSelector σbar) (t := t) x
  have hoptPoint :
      |Q.micro.optimalValue x - Q.w x| ≤ Q.D := by
    have hpoint :=
      (dist_le_pi_dist Q.micro.optimalValue Q.w x).trans Q.optimalValue_dist_w_le
    simpa [Real.dist_eq] using hpoint
  have hselPoint :
      |Q.micro.selectorValue (Q.liftSelector σbar) x - Q.w x| ≤ Q.D := by
    have hpoint :=
      (dist_le_pi_dist (Q.micro.selectorValue (Q.liftSelector σbar)) Q.w x).trans
        (Q.selectorValue_dist_w_le σbar hσbar)
    simpa [Real.dist_eq] using hpoint
  constructor
  · exact sub_nonneg.mpr hdom
  · rw [hinf]
    have h1 := (abs_le.mp hoptPoint).2
    have h2 := (abs_le.mp hselPoint).1
    linarith

/-- Source-facing P-QUO-02 closure.  The canonical finite macro greedy selector
exists by P-CTL-01, is macro-optimal, and its lift receives the frozen `2D`
regret certificate. -/
theorem p_quo_02 :
    dist Q.micro.optimalValue (Q.pullback Q.macroModel.optimalValue) ≤ Q.D ∧
    (∀ {t : ℕ} (x : X),
      0 ≤ Q.micro.optimalValue x -
        infiniteValue
          (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
          Q.micro (t := t) x ∧
      Q.micro.optimalValue x -
        infiniteValue
          (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
          Q.micro (t := t) x ≤ 2 * Q.D) := by
  constructor
  · simpa [w] using Q.optimalValue_dist_w_le
  · intro t x
    exact Q.liftSelector_regret_le_two_D
      Q.macroModel.greedyAction
      (fun y => Q.macroModel.greedyAction_spec y)
      (t := t) x

end ApproxControlQuotient

end UEOT.V3.FiniteDiscountedControl
