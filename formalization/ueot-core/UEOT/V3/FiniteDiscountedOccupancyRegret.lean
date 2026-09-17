import UEOT.V3.FiniteDiscountedApproxQuotientBounds
import UEOT.V3.FiniteDiscountedOccupancy
import Mathlib.Tactic

/-!
# P-QUO-05 — occupancy-weighted quotient-policy regret

This module proves the frozen Core 3 §20.5 local-error refinement of the
approximate finite discounted quotient theorem.  Unlike P-QUO-02's uniform
certificate, the source theorem weights the state-action dependent one-step
errors by the discounted occupancies of the true optimal and lifted policies.
-/

namespace UEOT.V3.FiniteDiscountedControl

universe uX uY uA

variable {X : Type uX} [Fintype X]
variable {Y : Type uY} [Fintype Y]
variable {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
variable {Abar : Y → Type uA} [∀ y, Fintype (Abar y)] [∀ y, Nonempty (Abar y)]

namespace ProbabilityRow

/-- Linearity of a finite probability-row expectation under subtraction. -/
theorem expect_sub {S : Type*} [Fintype S] (μ : ProbabilityRow S)
    (v w : S → ℝ) :
    μ.expect (v - w) = μ.expect v - μ.expect w := by
  classical
  unfold expect
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Pi.sub_apply]
  ring

end ProbabilityRow

namespace Model

variable (M : Model X A)

/-- The action-level reference residual used in frozen §20.5:
`b(x,a) = r(x,a) + β P_{x,a} w - w(x)`. -/
def actionReferenceResidual (w : X → ℝ) (x : X) (a : A x) : ℝ :=
  M.reward x a + M.discount * M.expect x a w - w x

/-- The fixed-policy residual is exactly the action residual averaged with the
stationary randomized policy. -/
theorem policyReferenceResidual_eq_actionAverage
    (π : StationaryPolicy A) (w : X → ℝ) (x : X) :
    M.policyReferenceResidual π w x =
      ∑ a, π.prob x a * M.actionReferenceResidual w x a := by
  classical
  simp only [policyReferenceResidual, policyReward, policyExpect, policyTransition,
    actionReferenceResidual, expect]
  have htrans :
      (∑ y, (∑ a, π.prob x a * M.transition x a y) * w y) =
        ∑ a, π.prob x a * ∑ y, M.transition x a y * w y := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  calc
    (∑ a, π.prob x a * M.reward x a) +
          M.discount * (∑ y, (∑ a, π.prob x a * M.transition x a y) * w y) - w x =
        (∑ a, π.prob x a * M.reward x a) +
          M.discount * (∑ a, π.prob x a * ∑ y, M.transition x a y * w y) - w x := by
      rw [htrans]
    _ = ∑ a, π.prob x a *
          (M.reward x a + M.discount * (∑ y, M.transition x a y * w y) - w x) := by
      calc
        (∑ a, π.prob x a * M.reward x a) +
              M.discount * (∑ a, π.prob x a * ∑ y, M.transition x a y * w y) - w x =
            (∑ a, π.prob x a * M.reward x a) +
              M.discount * (∑ a, π.prob x a * ∑ y, M.transition x a y * w y) -
                (∑ a, π.prob x a) * w x := by
          rw [π.prob_sum_one x, one_mul]
        _ = ∑ a, π.prob x a *
              (M.reward x a + M.discount * (∑ y, M.transition x a y * w y) - w x) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a ha
          ring

/-- P-QUO-04's state-occupancy residual expectation is the same expectation
of the action residual against the induced state-action occupancy. -/
theorem discountedStateOccupancy_expect_policyResidual_eq_stateActionExpect
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (w : X → ℝ) :
    (M.discountedStateOccupancy π μ).expect (M.policyReferenceResidual π w) =
      M.discountedStateActionExpect π μ (M.actionReferenceResidual w) := by
  classical
  unfold ProbabilityRow.expect discountedStateActionExpect
  apply Finset.sum_congr rfl
  intro x hx
  rw [M.policyReferenceResidual_eq_actionAverage π w x]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  unfold discountedStateActionOccupancy
  ring

/-- State-action form of the exact P-QUO-04 occupancy identity. -/
theorem policyValue_sub_reference_initial_expect_eq_stateActionOccupancy
    (π : StationaryPolicy A) (μ : ProbabilityRow X) (w : X → ℝ) :
    μ.expect (M.policyValue π - w) =
      M.discountedStateActionExpect π μ (M.actionReferenceResidual w) /
        (1 - M.discount) := by
  rw [M.policyValue_sub_reference_initial_expect_eq_occupancy π μ w]
  rw [M.discountedStateOccupancy_expect_policyResidual_eq_stateActionExpect π μ w]

/-- A deterministic selector embedded as a stationary policy has the same
policy-evaluation Bellman map as the existing selector API. -/
theorem policyBellman_ofSelector (σ : ∀ x, A x) (v : X → ℝ) :
    M.policyBellman (StationaryPolicy.ofSelector σ) v = M.selectorBellman σ v := by
  classical
  funext x
  simp [policyBellman, policyReward, policyExpect, policyTransition,
    StationaryPolicy.ofSelector, selectorBellman, qValue, expect]

/-- The stationary-policy fixed point of a deterministic selector is exactly
the selector fixed point already used by P-QUO-02. -/
theorem policyValue_ofSelector_eq_selectorValue (σ : ∀ x, A x) :
    M.policyValue (StationaryPolicy.ofSelector σ) = M.selectorValue σ := by
  symm
  apply M.policyValue_unique (StationaryPolicy.ofSelector σ)
  rw [M.policyBellman_ofSelector σ]
  exact M.selectorValue_fixed σ

/-- The canonical greedy selector, embedded in the stationary-policy API, has
the true optimal value. -/
theorem policyValue_ofSelector_greedy_eq_optimal :
    M.policyValue (StationaryPolicy.ofSelector M.greedyAction) = M.optimalValue := by
  rw [M.policyValue_ofSelector_eq_selectorValue M.greedyAction]
  symm
  apply M.selectorValue_unique M.greedyAction
  exact M.selectorBellman_optimal_fixed M.greedyAction (fun x => M.greedyAction_spec x)

/-- A deterministic selector collapses state-action occupancy expectation to
the selected action at each state. -/
theorem discountedStateActionExpect_ofSelector
    (σ : ∀ x, A x) (μ : ProbabilityRow X) (g : ∀ x, A x → ℝ) :
    M.discountedStateActionExpect (StationaryPolicy.ofSelector σ) μ g =
      ∑ x, (M.discountedStateOccupancy (StationaryPolicy.ofSelector σ) μ).prob x *
        g x (σ x) := by
  classical
  unfold discountedStateActionExpect discountedStateActionOccupancy StationaryPolicy.ofSelector
  apply Finset.sum_congr rfl
  intro x hx
  simp

/-- Monotonicity of state-action expectation under the discounted occupancy. -/
theorem discountedStateActionExpect_mono
    (π : StationaryPolicy A) (μ : ProbabilityRow X)
    (g h : ∀ x, A x → ℝ)
    (hgh : ∀ x a, g x a ≤ h x a) :
    M.discountedStateActionExpect π μ g ≤
      M.discountedStateActionExpect π μ h := by
  classical
  unfold discountedStateActionExpect
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_mul_of_nonneg_left
    (hgh x a) (M.discountedStateActionOccupancy_nonneg π μ x a)

/-- Negation commutes with state-action occupancy expectation. -/
theorem discountedStateActionExpect_neg
    (π : StationaryPolicy A) (μ : ProbabilityRow X)
    (g : ∀ x, A x → ℝ) :
    M.discountedStateActionExpect π μ (fun x a => -g x a) =
      -M.discountedStateActionExpect π μ g := by
  classical
  unfold discountedStateActionExpect
  simp [mul_neg]

end Model

/-! ## Source-strength local quotient data for P-QUO-05 -/

/-- A finite approximate control quotient carrying exactly the local reward and
transition errors used by frozen §20.5.  In particular, this structure does not
require the additional uniform error radii from P-QUO-02. -/
structure LocalApproxControlQuotient
    (X : Type uX) [Fintype X]
    (Y : Type uY) [Fintype Y]
    (Abar : Y → Type uA) [∀ y, Fintype (Abar y)] where
  f : X → Y
  surjective : Function.Surjective f
  micro : Model X (fun x => Abar (f x))
  macroModel : Model Y Abar
  discount_eq : micro.discount = macroModel.discount
  epsilonReward : ∀ x, Abar (f x) → ℝ
  epsilonTransition : ∀ x, Abar (f x) → ℝ
  reward_approx : ∀ x (a : Abar (f x)),
    |micro.reward x a - macroModel.reward (f x) a| ≤ epsilonReward x a
  transition_tv_approx : ∀ x (a : Abar (f x)),
    FiniteProbabilityRow.tvDist
      (pushforwardTransitionPMF f micro x a)
      (macroModel.transitionPMF (f x) a) ≤ epsilonTransition x a

namespace LocalApproxControlQuotient

variable (Q : LocalApproxControlQuotient X Y Abar)

/-- Pull a macro value function back to the micro state space. -/
def pullback (v : Y → ℝ) : X → ℝ := fun x => v (Q.f x)

/-- Frozen §20.5 reference function `w = Vbar* ∘ f`. -/
noncomputable def w : X → ℝ := Q.pullback Q.macroModel.optimalValue

/-- Lift a macro stationary selector through the quotient map. -/
def liftSelector (σbar : ∀ y, Abar y) : ∀ x, Abar (Q.f x) :=
  fun x => σbar (Q.f x)

/-- The stationary micro policy induced by a lifted macro selector. -/
noncomputable def liftedPolicy (σbar : ∀ y, Abar y) :
    StationaryPolicy (fun x => Abar (Q.f x)) :=
  StationaryPolicy.ofSelector (Q.liftSelector σbar)

/-- Frozen local one-step error
`δ(x,a) = ε_r(x,a) + β ε_p(x,a) sp(Vbar*)`. -/
noncomputable def localDelta (x : X) (a : Abar (Q.f x)) : ℝ :=
  Q.epsilonReward x a +
    Q.macroModel.discount * Q.epsilonTransition x a *
      UEOT.V3.TVSpan.span Q.macroModel.optimalValue

/-- Local TV error implies the span-sensitive continuation error without any
uniform error-radius hypothesis. -/
theorem abs_expect_pullback_sub_le_span
    (x : X) (a : Abar (Q.f x)) (v : Y → ℝ) :
    |Q.micro.expect x a (Q.pullback v) -
      Q.macroModel.expect (Q.f x) a v| ≤
      UEOT.V3.TVSpan.span v * Q.epsilonTransition x a := by
  have htv := Q.transition_tv_approx x a
  have h :=
    FiniteProbabilityRow.abs_expectation_sub_le_span_tvDist
      (pushforwardTransitionPMF Q.f Q.micro x a)
      (Q.macroModel.transitionPMF (Q.f x) a) v
  rw [pushforward_expect_eq Q.f Q.micro x a v] at h
  simp only [Model.expect, Model.transitionPMF_apply_toReal] at h
  exact h.trans <|
    mul_le_mul_of_nonneg_left htv (FiniteProbabilityRow.span_nonneg v)

/-- Local reward and transition bounds give the exact actionwise approximation
to the macro optimal Bellman expression. -/
theorem abs_qValue_w_sub_macro_optimal_le
    (x : X) (a : Abar (Q.f x)) :
    |Q.micro.qValue Q.w x a -
      Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a| ≤
      Q.localDelta x a := by
  have hr := Q.reward_approx x a
  have he := Q.abs_expect_pullback_sub_le_span x a Q.macroModel.optimalValue
  have hβ : 0 ≤ Q.macroModel.discount := Q.macroModel.discount_pos.le
  simp only [Model.qValue]
  rw [Q.discount_eq]
  calc
    |(Q.micro.reward x a +
          Q.macroModel.discount * Q.micro.expect x a Q.w) -
        (Q.macroModel.reward (Q.f x) a +
          Q.macroModel.discount * Q.macroModel.expect (Q.f x) a Q.macroModel.optimalValue)|
        ≤ |Q.micro.reward x a - Q.macroModel.reward (Q.f x) a| +
            |Q.macroModel.discount *
              (Q.micro.expect x a Q.w -
                Q.macroModel.expect (Q.f x) a Q.macroModel.optimalValue)| := by
          rw [show
            (Q.micro.reward x a +
                Q.macroModel.discount * Q.micro.expect x a Q.w) -
              (Q.macroModel.reward (Q.f x) a +
                Q.macroModel.discount * Q.macroModel.expect (Q.f x) a Q.macroModel.optimalValue) =
              (Q.micro.reward x a - Q.macroModel.reward (Q.f x) a) +
                Q.macroModel.discount *
                  (Q.micro.expect x a Q.w -
                    Q.macroModel.expect (Q.f x) a Q.macroModel.optimalValue) by ring]
          exact abs_add_le _ _
    _ = |Q.micro.reward x a - Q.macroModel.reward (Q.f x) a| +
          Q.macroModel.discount *
            |Q.micro.expect x a Q.w -
              Q.macroModel.expect (Q.f x) a Q.macroModel.optimalValue| := by
          rw [abs_mul, abs_of_nonneg hβ]
    _ ≤ Q.epsilonReward x a +
          Q.macroModel.discount *
            (UEOT.V3.TVSpan.span Q.macroModel.optimalValue * Q.epsilonTransition x a) :=
          add_le_add hr (mul_le_mul_of_nonneg_left he hβ)
    _ = Q.localDelta x a := by
          simp [localDelta]
          ring

/-- Every micro action has reference residual at most the local source error,
because its macro Bellman advantage is nonpositive. -/
theorem actionReferenceResidual_le_localDelta
    (x : X) (a : Abar (Q.f x)) :
    Q.micro.actionReferenceResidual Q.w x a ≤ Q.localDelta x a := by
  have happ := Q.abs_qValue_w_sub_macro_optimal_le x a
  have hmacro := Q.macroModel.qValue_optimal_le (Q.f x) a
  have hw : Q.w x = Q.macroModel.optimalValue (Q.f x) := rfl
  have hupper := (abs_le.mp happ).2
  unfold Model.actionReferenceResidual
  change Q.micro.qValue Q.w x a - Q.w x ≤ Q.localDelta x a
  rw [hw]
  linarith

/-- On any designated macro-optimal selector, the lifted action residual is at
least the negative local source error.  This keeps tied macro optima explicit. -/
theorem neg_localDelta_le_liftedOptimalResidual
    (σbar : ∀ y, Abar y)
    (hσbar : ∀ y,
      Q.macroModel.qValue Q.macroModel.optimalValue y (σbar y) =
        Q.macroModel.optimalValue y)
    (x : X) :
    -Q.localDelta x (σbar (Q.f x)) ≤
      Q.micro.actionReferenceResidual Q.w x (σbar (Q.f x)) := by
  let a := σbar (Q.f x)
  have happ := Q.abs_qValue_w_sub_macro_optimal_le x a
  have hmacro := hσbar (Q.f x)
  have hw : Q.w x = Q.macroModel.optimalValue (Q.f x) := rfl
  have hlower := (abs_le.mp happ).1
  unfold Model.actionReferenceResidual
  change -Q.localDelta x a ≤ Q.micro.qValue Q.w x a - Q.w x
  rw [hw, ← hmacro]
  exact hlower

/-- The frozen local error averaged under a designated discounted state-action
occupancy. -/
noncomputable def localErrorExpect
    (π : StationaryPolicy (fun x => Abar (Q.f x)))
    (μ : ProbabilityRow X) : ℝ :=
  Q.micro.discountedStateActionExpect π μ Q.localDelta

/-- The actionwise upper residual bound integrates under any stationary policy,
including any true-optimal policy chosen among ties. -/
theorem residualExpect_le_localError
    (π : StationaryPolicy (fun x => Abar (Q.f x)))
    (μ : ProbabilityRow X) :
    Q.micro.discountedStateActionExpect π μ
        (Q.micro.actionReferenceResidual Q.w) ≤
      Q.localErrorExpect π μ := by
  exact Q.micro.discountedStateActionExpect_mono
    π μ (Q.micro.actionReferenceResidual Q.w) Q.localDelta
    (fun x a => Q.actionReferenceResidual_le_localDelta x a)

/-- The lifted macro-optimal occupancy integrates the lower residual bound. -/
theorem neg_liftedLocalError_le_residualExpect
    (σbar : ∀ y, Abar y)
    (hσbar : ∀ y,
      Q.macroModel.qValue Q.macroModel.optimalValue y (σbar y) =
        Q.macroModel.optimalValue y)
    (μ : ProbabilityRow X) :
    -Q.localErrorExpect (Q.liftedPolicy σbar) μ ≤
      Q.micro.discountedStateActionExpect (Q.liftedPolicy σbar) μ
        (Q.micro.actionReferenceResidual Q.w) := by
  unfold localErrorExpect liftedPolicy
  rw [Q.micro.discountedStateActionExpect_ofSelector]
  rw [Q.micro.discountedStateActionExpect_ofSelector]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro x hx
  have hpoint := Q.neg_localDelta_le_liftedOptimalResidual σbar hσbar x
  have hweight :=
    (Q.micro.discountedStateOccupancy
      (StationaryPolicy.ofSelector (Q.liftSelector σbar)) μ).prob_nonneg x
  have hmul := mul_le_mul_of_nonneg_left hpoint hweight
  simpa [liftSelector, mul_neg] using hmul

/-- **P-QUO-05.** Frozen §20.5 occupancy-weighted quotient-policy regret.

`πstar` is an arbitrary designated true-optimal stationary micro policy and
`σbar` is an arbitrary macro-optimal selector.  Therefore the two occupancy
expectations remain those of the actual chosen policies, including tied-optimal
cases; no uniform P-QUO-02 error radius is assumed. -/
theorem p_quo_05
    (πstar : StationaryPolicy (fun x => Abar (Q.f x)))
    (hπstar : Q.micro.policyValue πstar = Q.micro.optimalValue)
    (σbar : ∀ y, Abar y)
    (hσbar : ∀ y,
      Q.macroModel.qValue Q.macroModel.optimalValue y (σbar y) =
        Q.macroModel.optimalValue y)
    (μ : ProbabilityRow X) :
    μ.expect Q.micro.optimalValue -
        μ.expect (Q.micro.policyValue (Q.liftedPolicy σbar)) ≤
      (Q.localErrorExpect πstar μ +
        Q.localErrorExpect (Q.liftedPolicy σbar) μ) /
          (1 - Q.micro.discount) := by
  let πhat := Q.liftedPolicy σbar
  let b := Q.micro.actionReferenceResidual Q.w
  have hstar :=
    Q.micro.policyValue_sub_reference_initial_expect_eq_stateActionOccupancy
      πstar μ Q.w
  have hhat :=
    Q.micro.policyValue_sub_reference_initial_expect_eq_stateActionOccupancy
      πhat μ Q.w
  rw [hπstar] at hstar
  rw [ProbabilityRow.expect_sub] at hstar hhat
  have hstarBound := Q.residualExpect_le_localError πstar μ
  have hhatBound := Q.neg_liftedLocalError_le_residualExpect σbar hσbar μ
  have hden : 0 < 1 - Q.micro.discount := by
    linarith [Q.micro.discount_lt_one]
  have hres :
      Q.micro.discountedStateActionExpect πstar μ b -
          Q.micro.discountedStateActionExpect πhat μ b ≤
        Q.localErrorExpect πstar μ + Q.localErrorExpect πhat μ := by
    dsimp [πhat, b] at hstarBound hhatBound ⊢
    linarith
  have hregret :
      μ.expect Q.micro.optimalValue - μ.expect (Q.micro.policyValue πhat) =
        (Q.micro.discountedStateActionExpect πstar μ b -
          Q.micro.discountedStateActionExpect πhat μ b) /
            (1 - Q.micro.discount) := by
    have hdenne : 1 - Q.micro.discount ≠ 0 := ne_of_gt hden
    have hstar' := (eq_div_iff hdenne).mp hstar
    have hhat' := (eq_div_iff hdenne).mp hhat
    apply (eq_div_iff hdenne).2
    calc
      (μ.expect Q.micro.optimalValue - μ.expect (Q.micro.policyValue πhat)) *
            (1 - Q.micro.discount) =
          (μ.expect Q.micro.optimalValue - μ.expect Q.w) *
              (1 - Q.micro.discount) -
            (μ.expect (Q.micro.policyValue πhat) - μ.expect Q.w) *
              (1 - Q.micro.discount) := by ring
      _ = Q.micro.discountedStateActionExpect πstar μ b -
            Q.micro.discountedStateActionExpect πhat μ b := by
        dsimp [b]
        rw [hstar', hhat']
  change
    μ.expect Q.micro.optimalValue - μ.expect (Q.micro.policyValue πhat) ≤
      (Q.localErrorExpect πstar μ + Q.localErrorExpect πhat μ) /
        (1 - Q.micro.discount)
  rw [hregret]
  exact div_le_div_of_nonneg_right hres hden.le

end LocalApproxControlQuotient

end UEOT.V3.FiniteDiscountedControl
