import UEOT.V3.Compression.ApproximateGoaGaugeStability

/-!
# Action-gap stability under approximate quotient gauge

The preceding approximate-GOA gauge theorem deliberately fixed one transported
policy.  This module states the extra hypothesis needed to identify that policy
with the target model's own canonical greedy policy.

The key quantity is the source optimal-action gap.  Approximate quotient
certificates first give a relabeled optimal-Q perturbation radius
`D_Q + D_R`.  If every competing source action is separated from the source
greedy action by strictly more than twice that radius, the ordering cannot
flip after transport.  The target greedy selector is then exactly the
transported source greedy selector, so the fixed-policy stationary perturbation
theorem upgrades to an optimal-policy near-GOA theorem.
-/

namespace UEOT.V3.Compression.ActionGapGaugeStability

open Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.GoaGaugeInvariance
open UEOT.V3.Compression.ApproximateSemanticGauge
open UEOT.V3.Compression.ApproximateGoaGaugeStability

universe uX uS uA

noncomputable section

variable {X : Type uX} [Fintype X] [Nonempty X]
variable {S : Type uS} [Fintype S] [Nonempty S]
variable {Act : Type uA} [Fintype Act] [Nonempty Act]

/-- One approximate quotient's macro optimal action-value differs from the
corresponding micro optimal action-value by at most its global P-QUO radius
`D`.

This sharpens the existing one-step `delta` estimate by using the already
proved optimal-value radius and the Bellman action-value Lipschitz estimate:
`delta + beta * D = D`. -/
theorem macroOptimalQ_micro_le
    (Q : ApproxControlQuotient X S (fun _ => Act))
    (x : X) (a : Act) :
    |Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a -
      Q.micro.qValue Q.micro.optimalValue x a| ≤ Q.D := by
  have happrox0 :=
    Q.abs_qValue_pullback_sub_le x a Q.macroModel.optimalValue
  have happrox :
      |Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a -
        Q.micro.qValue Q.w x a| ≤ Q.delta := by
    rw [abs_sub_comm]
    simpa only [ApproxControlQuotient.w, ApproxControlQuotient.delta] using happrox0
  have hlip0 := Q.micro.abs_qValue_sub_le Q.w Q.micro.optimalValue x a
  have hlip :
      |Q.micro.qValue Q.w x a - Q.micro.qValue Q.micro.optimalValue x a| ≤
        Q.micro.discount * Q.D := by
    have hdist : dist Q.w Q.micro.optimalValue ≤ Q.D := by
      simpa only [dist_comm] using Q.optimalValue_dist_w_le
    exact hlip0.trans
      (mul_le_mul_of_nonneg_left hdist Q.micro.discount_pos.le)
  have htri := abs_sub_le
    (Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a)
    (Q.micro.qValue Q.w x a)
    (Q.micro.qValue Q.micro.optimalValue x a)
  have hsum :
      |Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a -
        Q.micro.qValue Q.micro.optimalValue x a| ≤
        Q.delta + Q.micro.discount * Q.D :=
    htri.trans (add_le_add happrox hlip)
  have hden : 0 < 1 - Q.macroModel.discount :=
    sub_pos.mpr Q.macroModel.discount_lt_one
  have hdeltaD : Q.delta + Q.micro.discount * Q.D = Q.D := by
    rw [ApproxControlQuotient.D, Q.discount_eq]
    field_simp [ne_of_gt hden]
    ring
  rwa [hdeltaD] at hsum

/-- Two approximate quotients of the same micro model have relabeled optimal
action-values within the sum of their global P-QUO radii. -/
theorem macroOptimalQ_relabel_le
    (Q R : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (e : S ≃ S) (he : e ∘ Q.f = R.f)
    (s : S) (a : Act) :
    |Q.macroModel.qValue Q.macroModel.optimalValue s a -
      R.macroModel.qValue R.macroModel.optimalValue (e s) a| ≤
      Q.D + R.D := by
  rcases Q.surjective s with ⟨x, rfl⟩
  have hex : e (Q.f x) = R.f x := by
    simpa only [Function.comp_apply] using congrFun he x
  have hQ := macroOptimalQ_micro_le Q x a
  have hR0 := macroOptimalQ_micro_le R x a
  have hR :
      |Q.micro.qValue Q.micro.optimalValue x a -
        R.macroModel.qValue R.macroModel.optimalValue (e (Q.f x)) a| ≤ R.D := by
    rw [hMicro, hex]
    rw [abs_sub_comm]
    exact hR0
  exact (abs_sub_le
    (Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a)
    (Q.micro.qValue Q.micro.optimalValue x a)
    (R.macroModel.qValue R.macroModel.optimalValue (e (Q.f x)) a)).trans
      (add_le_add hQ hR)

/-- A strict source action gap wider than twice the cross-quotient optimal-Q
radius makes the transported source greedy action strictly optimal in the
target model. -/
theorem transportedSourceGreedy_strictlyOptimal
    (Q R : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (e : S ≃ S) (he : e ∘ Q.f = R.f)
    (hgap : ∀ s a, a ≠ Q.macroModel.greedyAction s →
      2 * (Q.D + R.D) <
        Q.macroModel.qValue Q.macroModel.optimalValue s
            (Q.macroModel.greedyAction s) -
          Q.macroModel.qValue Q.macroModel.optimalValue s a) :
    ∀ s a, a ≠ Q.macroModel.greedyAction s →
      R.macroModel.qValue R.macroModel.optimalValue (e s)
          (Q.macroModel.greedyAction s) >
        R.macroModel.qValue R.macroModel.optimalValue (e s) a := by
  intro s a hne
  have hstar := macroOptimalQ_relabel_le Q R hMicro e he s
    (Q.macroModel.greedyAction s)
  have ha := macroOptimalQ_relabel_le Q R hMicro e he s a
  have hstarUpper := (abs_le.mp hstar).2
  have haLower := (abs_le.mp ha).1
  have hg := hgap s a hne
  linarith

/-- Under the strict source action-gap condition, the target's canonical
greedy action agrees pointwise with the transported source greedy action. -/
theorem targetGreedy_eq_transportedSourceGreedy
    (Q R : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (e : S ≃ S) (he : e ∘ Q.f = R.f)
    (hgap : ∀ s a, a ≠ Q.macroModel.greedyAction s →
      2 * (Q.D + R.D) <
        Q.macroModel.qValue Q.macroModel.optimalValue s
            (Q.macroModel.greedyAction s) -
          Q.macroModel.qValue Q.macroModel.optimalValue s a) :
    ∀ s, R.macroModel.greedyAction (e s) = Q.macroModel.greedyAction s := by
  intro s
  by_contra hne
  have hstrict := transportedSourceGreedy_strictlyOptimal
    Q R hMicro e he hgap s (R.macroModel.greedyAction (e s)) hne
  have hdom := R.macroModel.qValue_optimal_le
    (e s) (Q.macroModel.greedyAction s)
  have hgreedy := R.macroModel.greedyAction_spec (e s)
  linarith

/-- Function-level policy equality corresponding to the pointwise action-gap
theorem. -/
theorem targetGreedy_eq_transportSelector
    (Q R : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (e : S ≃ S) (he : e ∘ Q.f = R.f)
    (hgap : ∀ s a, a ≠ Q.macroModel.greedyAction s →
      2 * (Q.D + R.D) <
        Q.macroModel.qValue Q.macroModel.optimalValue s
            (Q.macroModel.greedyAction s) -
          Q.macroModel.qValue Q.macroModel.optimalValue s a) :
    R.macroModel.greedyAction =
      transportSelector e Q.macroModel.greedyAction := by
  funext y
  rcases e.surjective y with ⟨s, rfl⟩
  rw [transportSelector_apply_e]
  exact targetGreedy_eq_transportedSourceGreedy Q R hMicro e he hgap s

/-- Full optimal-policy near-GOA gauge stability.

The action-gap hypothesis upgrades the preceding fixed-policy theorem so that
the target kernel is now induced by the target model's own canonical greedy
selector.  Thus the stationary perturbation tube compares the two models'
actual finite GOD/GOA closed loops, not merely a common externally fixed
policy. -/
theorem optimalPolicy_near_goa_gauge_stability
    (Q R : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (e : S ≃ S) (he : e ∘ Q.f = R.f)
    (hgap : ∀ s a, a ≠ Q.macroModel.greedyAction s →
      2 * (Q.D + R.D) <
        Q.macroModel.qValue Q.macroModel.optimalValue s
            (Q.macroModel.greedyAction s) -
          Q.macroModel.qValue Q.macroModel.optimalValue s a)
    (halpha :
      dobrushinAlpha
        (selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction)
        (selectorClosedLoopMatrix_rowStochastic
          Q.macroModel Q.macroModel.greedyAction) < 1) :
    (∀ s, R.macroModel.greedyAction (e s) = Q.macroModel.greedyAction s) ∧
    ∃ mustarQ : stdSimplex ℝ S,
      step
          (selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction)
          (selectorClosedLoopMatrix_rowStochastic
            Q.macroModel Q.macroModel.greedyAction)
          mustarQ = mustarQ ∧
      (∀ nu : stdSimplex ℝ S,
        step
            (selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction)
            (selectorClosedLoopMatrix_rowStochastic
              Q.macroModel Q.macroModel.greedyAction)
            nu = nu → nu = mustarQ) ∧
      ∀ muR : stdSimplex ℝ S,
        step
            (selectorClosedLoopMatrix R.macroModel R.macroModel.greedyAction)
            (selectorClosedLoopMatrix_rowStochastic
              R.macroModel R.macroModel.greedyAction)
            muR = muR →
        lawTV (relabelSimplex e mustarQ) muR ≤
          (Q.epsilonTransition + R.epsilonTransition) /
            (1 - dobrushinAlpha
              (selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction)
              (selectorClosedLoopMatrix_rowStochastic
                Q.macroModel Q.macroModel.greedyAction)) := by
  have hpoint := targetGreedy_eq_transportedSourceGreedy
    Q R hMicro e he hgap
  have hsel := targetGreedy_eq_transportSelector Q R hMicro e he hgap
  constructor
  · exact hpoint
  · rcases fixedPolicy_near_goa_gauge_stability
      Q R hMicro e he Q.macroModel.greedyAction halpha with
      ⟨mustarQ, hfixQ, huniqQ, hbound⟩
    refine ⟨mustarQ, hfixQ, huniqQ, ?_⟩
    intro muR hmuR
    apply hbound muR
    rw [← hsel]
    exact hmuR

end

end UEOT.V3.Compression.ActionGapGaugeStability
