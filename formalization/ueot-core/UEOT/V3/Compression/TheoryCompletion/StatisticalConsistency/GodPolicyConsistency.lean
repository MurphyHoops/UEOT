import UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency.StructuralControlClosure
import UEOT.V3.Compression.TheoryCompletion.GOD
import UEOT.V3.Compression.ActionGapGaugeStability
import UEOT.V3.Compression.MovingEncoderSemanticGoaClosure
import UEOT.V3.Compression.PrimitiveRewardSpanClosure
import Mathlib.Tactic

namespace UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency

open Filter Topology MeasureTheory
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.ActionGapGaugeStability
open UEOT.V3.Compression.MovingEncoderSemanticGoaClosure
open UEOT.V3.Compression.PrimitiveRewardSpanClosure

universe uX uS uA

/-- P3.5 exactification upgrades value consistency from convergence to literal
equality on the fixed recovered encoder. -/
theorem exact_value_consistency_of_realizedEstimator
    {X : Type uX} [Fintype X]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : X → S) (hC : Function.Surjective C)
    (micro : Model X (fun _ => Act))
    (E : RealizedControlEstimator C micro) :
    let Q := exactControlQuotient_of_realizedEstimator C hC micro E
    ∀ x, micro.optimalValue x = Q.macroModel.optimalValue (C x) := by
  dsimp only
  intro x
  exact (exactControlQuotient_of_realizedEstimator C hC micro E).optimalValue_apply x

/-- Exact quotient descent preserves the whole Bellman-optimal action set, not
just one canonical selector. -/
theorem exact_bellmanGODCorrespondence_eq
    {X : Type uX} [Fintype X]
    {S : Type uS} [Fintype S]
    {Abar : S → Type uA}
    [∀ s, Fintype (Abar s)] [∀ s, Nonempty (Abar s)]
    (Q : ExactControlQuotient X S Abar) (x : X) :
    BellmanGODCorrespondence Q.micro x =
      BellmanGODCorrespondence Q.macroModel (Q.f x) := by
  ext a
  rw [mem_bellmanGODCorrespondence_iff,
    mem_bellmanGODCorrespondence_iff,
    Q.optimal_qValue_pullback x a,
    Q.optimalValue_apply x]

/-- Regard an exact quotient as the zero-defect approximate interface used by
existing stability theorems. -/
noncomputable def exactAsApprox
    {X : Type uX} [Fintype X]
    {S : Type uS} [Fintype S]
    {Abar : S → Type uA}
    [∀ s, Fintype (Abar s)] [∀ s, Nonempty (Abar s)]
    (Q : ExactControlQuotient X S Abar) :
    ApproxControlQuotient X S Abar where
  f := Q.f
  surjective := Q.surjective
  micro := Q.micro
  macroModel := Q.macroModel
  discount_eq := Q.discount_eq
  epsilonReward := 0
  epsilonTransition := 0
  epsilonReward_nonneg := le_rfl
  epsilonTransition_nonneg := le_rfl
  reward_approx := by
    intro x a
    rw [Q.reward_closed x a]
    simp
  transition_tv_approx := by
    intro x a
    have heq :
        pushforwardTransitionPMF Q.f Q.micro x a =
          Q.macroModel.transitionPMF (Q.f x) a := by
      apply PMF.ext
      intro y
      apply (ENNReal.toReal_eq_toReal_iff'
        (PMF.apply_ne_top _ y) (PMF.apply_ne_top _ y)).mp
      rw [pushforwardTransitionPMF_apply_toReal,
        Model.transitionPMF_apply_toReal]
      exact Q.transition_closed x a y
    rw [heq]
    letI : MeasurableSpace S := ⊤
    change UEOT.V3.TotalVariation.tvDist
      (Q.macroModel.transitionPMF (Q.f x) a).toMeasure
      (Q.macroModel.transitionPMF (Q.f x) a).toMeasure ≤ 0
    let _ : IsProbabilityMeasure
        (Q.macroModel.transitionPMF (Q.f x) a).toMeasure := by infer_instance
    rw [UEOT.V3.TransportDefect.tvDist_self]

/-- If the estimator uses the known source discount, each estimated macro model
is an ordinary approximate quotient with its *estimator* radii. -/
noncomputable def estimatedApproxControlQuotient
    {X : Type uX} [Fintype X]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    {C : X → S}
    {micro : Model X (fun _ => Act)}
    (E : RealizedControlEstimator C micro)
    (hC : Function.Surjective C)
    (hdiscount : ∀ n, micro.discount = (E.macroHat n).discount)
    (n : ℕ) :
    ApproxControlQuotient X S (fun _ => Act) where
  f := C
  surjective := hC
  micro := micro
  macroModel := E.macroHat n
  discount_eq := hdiscount n
  epsilonReward := E.rewardRadius n
  epsilonTransition := E.transitionRadius n
  epsilonReward_nonneg := E.rewardRadius_nonneg n
  epsilonTransition_nonneg := E.transitionRadius_nonneg n
  reward_approx := E.reward_estimation n
  transition_tv_approx := E.transition_estimation n

/-- Positive canonical action gap upgrades vanishing estimator defects to exact
eventual recovery of the estimator's canonical greedy selector.  Without this
gap only the set-valued GOD statement above is justified. -/
theorem eventually_estimatedGreedy_eq_canonical
    {X : Type uX} [Fintype X] [Nonempty X]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : X → S) (hC : Function.Surjective C)
    (micro : Model X (fun _ => Act))
    (E : RealizedControlEstimator C micro)
    (hdiscount : ∀ n, micro.discount = (E.macroHat n).discount)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hsourceGap :
      let Qexact := exactControlQuotient_of_realizedEstimator C hC micro E
      ∀ s a, a ≠ Qexact.macroModel.greedyAction s →
        gamma ≤
          Qexact.macroModel.qValue Qexact.macroModel.optimalValue s
              (Qexact.macroModel.greedyAction s) -
            Qexact.macroModel.qValue Qexact.macroModel.optimalValue s a) :
    let Qexact := exactControlQuotient_of_realizedEstimator C hC micro E
    ∀ᶠ n in atTop, ∀ s,
      (E.macroHat n).greedyAction s = Qexact.macroModel.greedyAction s := by
  dsimp only
  let _ : Nonempty S := ⟨C (Classical.choice (inferInstance : Nonempty X))⟩
  let Qexact := exactControlQuotient_of_realizedEstimator C hC micro E
  let Qref : ApproxControlQuotient X S (fun _ => Act) := exactAsApprox Qexact
  let Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act) :=
    fun n => estimatedApproxControlQuotient E hC hdiscount n
  have hrefD : Qref.D = 0 :=
    D_eq_zero_of_exact_defects Qref rfl rfl
  have hMicro : ∀ n, Qref.micro = (Qseq n).micro := by
    intro n
    rfl
  have hD : Tendsto (fun n => (Qseq n).D) atTop (𝓝 0) := by
    apply D_tendsto_zero_of_primitive_defects Qref Qseq hMicro
    · simpa [Qseq, estimatedApproxControlQuotient] using
        E.rewardRadius_tendsto_zero
    · simpa [Qseq, estimatedApproxControlQuotient] using
        E.transitionRadius_tendsto_zero
  have hsourceGap' : ∀ s a, a ≠ Qref.macroModel.greedyAction s →
      gamma ≤
        Qref.macroModel.qValue Qref.macroModel.optimalValue s
            (Qref.macroModel.greedyAction s) -
          Qref.macroModel.qValue Qref.macroModel.optimalValue s a := by
    change ∀ s a, a ≠ Qexact.macroModel.greedyAction s →
      gamma ≤
        Qexact.macroModel.qValue Qexact.macroModel.optimalValue s
            (Qexact.macroModel.greedyAction s) -
          Qexact.macroModel.qValue Qexact.macroModel.optimalValue s a
    exact hsourceGap
  have hgap := eventually_actionGap_of_D_tendsto_zero
    Qref Qseq hrefD hD gamma hgamma hsourceGap'
  filter_upwards [hgap] with n hn
  intro s
  have hpolicy := targetGreedy_eq_transportedSourceGreedy
    Qref (Qseq n) (hMicro n) (Equiv.refl S) (by
      funext x
      rfl) hn s
  simpa [Qref, Qseq, Qexact, exactAsApprox, estimatedApproxControlQuotient] using hpolicy

end UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency
