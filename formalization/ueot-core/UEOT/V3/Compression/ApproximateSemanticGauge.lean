import UEOT.V3.Compression.MetricGaugeInvariance
import UEOT.V3.FiniteDiscountedApproxQuotientBounds
import UEOT.V3.InformationPacking
import UEOT.V3.TransportDefect

/-!
# Approximate control-semantic gauge stability

Exact quotient gauge does not by itself imply approximate semantic closeness.
This module keeps the missing hypotheses explicit.

Two approximate finite control quotients are compared only when:

* they describe the same literal micro control model;
* their finite quotient states are exactly aligned by a state equivalence;
* each quotient already carries its own certified reward and transition-TV
  defect envelope relative to that common micro model.

Under those assumptions, the relabeled macro rewards, transition rows and
optimal values differ by the sum of the two certified errors.  This is the
quantitative semantic analogue of the exact `SemanticRelabel` theorem.
-/

namespace UEOT.V3.Compression.ApproximateSemanticGauge

open Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.QuotientGauge
open UEOT.V3.Compression.GaugeSemanticTransfer
open UEOT.V3.Compression.MetricGaugeInvariance

universe uX uS uA

noncomputable section

variable {X : Type uX} [Fintype X] [Nonempty X]
variable {S : Type uS} [Fintype S] [Nonempty S]
variable {Act : Type uA} [Fintype Act] [Nonempty Act]

/-- Canonical finite PMF TV is symmetric. -/
theorem finiteTvDist_symm (p q : PMF S) :
    FiniteProbabilityRow.tvDist p q = FiniteProbabilityRow.tvDist q p := by
  letI : MeasurableSpace S := ⊤
  unfold FiniteProbabilityRow.tvDist
  exact UEOT.V3.InformationPacking.tvDist_symm p.toMeasure q.toMeasure

/-- Canonical finite PMF TV satisfies the triangle inequality. -/
theorem finiteTvDist_triangle (p q r : PMF S) :
    FiniteProbabilityRow.tvDist p r ≤
      FiniteProbabilityRow.tvDist p q + FiniteProbabilityRow.tvDist q r := by
  letI : MeasurableSpace S := ⊤
  unfold FiniteProbabilityRow.tvDist
  exact UEOT.V3.TransportDefect.tvDist_triangle
    p.toMeasure q.toMeasure r.toMeasure

/-- Canonical finite PMF TV is exactly invariant under a bijective relabeling. -/
theorem finiteTvDist_map_equiv
    (e : S ≃ S) (p q : PMF S) :
    FiniteProbabilityRow.tvDist (p.map e) (q.map e) =
      FiniteProbabilityRow.tvDist p q := by
  letI : MeasurableSpace S := ⊤
  let em : S ≃ᵐ S :=
    MeasurableEquiv.mk e Measurable.of_discrete Measurable.of_discrete
  unfold FiniteProbabilityRow.tvDist
  rw [← PMF.toMeasure_map e p Measurable.of_discrete,
      ← PMF.toMeasure_map e q Measurable.of_discrete]
  exact UEOT.V3.TotalVariation.tvDist_map_measurableEquiv
    p.toMeasure q.toMeasure em

/-- If two encoders differ only by the state equivalence `e`, then the
pushforward of one micro transition row through the first encoder, followed by
`e`, is exactly the pushforward through the second encoder. -/
theorem pushforwardTransitionPMF_relabel
    (q r : X → S) (e : S ≃ S)
    (he : e ∘ q = r)
    (M : Model X (fun _ => Act)) (x : X) (a : Act) :
    (pushforwardTransitionPMF q M x a).map e =
      pushforwardTransitionPMF r M x a := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top ((pushforwardTransitionPMF q M x a).map e) y)
    (PMF.apply_ne_top (pushforwardTransitionPMF r M x a) y)).mp
  rw [pmf_map_equiv_apply_toReal,
    pushforwardTransitionPMF_apply_toReal,
    pushforwardTransitionPMF_apply_toReal]
  calc
    fiberMass q (M.transition x a) (e.symm y) =
        fiberMass r (M.transition x a) (e (e.symm y)) :=
      fiberMass_relabel q r e he (M.transition x a) (e.symm y)
    _ = fiberMass r (M.transition x a) y := by simp

/-- Exact state alignment plus two reward-defect certificates gives the
relabeled macro reward error `εr_Q + εr_R`. -/
theorem macroReward_relabel_le
    (Q R : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (e : S ≃ S) (he : e ∘ Q.f = R.f)
    (s : S) (a : Act) :
    |Q.macroModel.reward s a - R.macroModel.reward (e s) a| ≤
      Q.epsilonReward + R.epsilonReward := by
  rcases Q.surjective s with ⟨x, rfl⟩
  have hex : e (Q.f x) = R.f x := by
    simpa only [Function.comp_apply] using congrFun he x
  have hQ := Q.reward_approx x a
  have hR :
      |Q.micro.reward x a - R.macroModel.reward (e (Q.f x)) a| ≤
        R.epsilonReward := by
    rw [hMicro, hex]
    exact R.reward_approx x a
  calc
    |Q.macroModel.reward (Q.f x) a - R.macroModel.reward (e (Q.f x)) a| ≤
        |Q.macroModel.reward (Q.f x) a - Q.micro.reward x a| +
          |Q.micro.reward x a - R.macroModel.reward (e (Q.f x)) a| :=
      abs_sub_le _ _ _
    _ ≤ Q.epsilonReward + R.epsilonReward := by
      rw [abs_sub_comm (Q.macroModel.reward (Q.f x) a) (Q.micro.reward x a)]
      exact add_le_add hQ hR

/-- Exact state alignment plus two transition-TV defect certificates gives the
relabeled macro transition error `εp_Q + εp_R`.

The Q macro row is pushed forward by `e` before comparison, so both sides live
on the same target state labels. -/
theorem macroTransition_relabel_tv_le
    (Q R : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (e : S ≃ S) (he : e ∘ Q.f = R.f)
    (s : S) (a : Act) :
    FiniteProbabilityRow.tvDist
        ((Q.macroModel.transitionPMF s a).map e)
        (R.macroModel.transitionPMF (e s) a) ≤
      Q.epsilonTransition + R.epsilonTransition := by
  rcases Q.surjective s with ⟨x, rfl⟩
  have hex : e (Q.f x) = R.f x := by
    simpa only [Function.comp_apply] using congrFun he x
  let pQ := pushforwardTransitionPMF Q.f Q.micro x a
  let mQ := Q.macroModel.transitionPMF (Q.f x) a
  let pR := pushforwardTransitionPMF R.f R.micro x a
  let mR := R.macroModel.transitionPMF (R.f x) a
  have hbridge : pQ.map e = pR := by
    dsimp [pQ, pR]
    calc
      (pushforwardTransitionPMF Q.f Q.micro x a).map e =
          pushforwardTransitionPMF R.f Q.micro x a :=
        pushforwardTransitionPMF_relabel Q.f R.f e he Q.micro x a
      _ = pushforwardTransitionPMF R.f R.micro x a := by rw [hMicro]
  have hQmap :
      FiniteProbabilityRow.tvDist (pQ.map e) (mQ.map e) ≤
        Q.epsilonTransition := by
    rw [finiteTvDist_map_equiv]
    exact Q.transition_tv_approx x a
  have hQrev :
      FiniteProbabilityRow.tvDist (mQ.map e) pR ≤
        Q.epsilonTransition := by
    rw [← hbridge, finiteTvDist_symm]
    exact hQmap
  have hR : FiniteProbabilityRow.tvDist pR mR ≤ R.epsilonTransition := by
    dsimp [pR, mR]
    exact R.transition_tv_approx x a
  rw [hex]
  change FiniteProbabilityRow.tvDist (mQ.map e) mR ≤ _
  exact (finiteTvDist_triangle (mQ.map e) pR mR).trans
    (add_le_add hQrev hR)

/-- Two approximate quotients of the same micro system have relabeled optimal
values within the sum of their P-QUO-02 global radii. -/
theorem macroOptimalValue_relabel_le
    (Q R : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (e : S ≃ S) (he : e ∘ Q.f = R.f)
    (s : S) :
    |Q.macroModel.optimalValue s - R.macroModel.optimalValue (e s)| ≤
      Q.D + R.D := by
  rcases Q.surjective s with ⟨x, rfl⟩
  have hex : e (Q.f x) = R.f x := by
    simpa only [Function.comp_apply] using congrFun he x
  have hQpoint :=
    (dist_le_pi_dist Q.micro.optimalValue Q.w x).trans Q.optimalValue_dist_w_le
  have hQ :
      |Q.micro.optimalValue x - Q.macroModel.optimalValue (Q.f x)| ≤ Q.D := by
    simpa [Real.dist_eq, ApproxControlQuotient.w,
      ApproxControlQuotient.pullback] using hQpoint
  have hRpoint :=
    (dist_le_pi_dist R.micro.optimalValue R.w x).trans R.optimalValue_dist_w_le
  have hR0 :
      |R.micro.optimalValue x - R.macroModel.optimalValue (R.f x)| ≤ R.D := by
    simpa [Real.dist_eq, ApproxControlQuotient.w,
      ApproxControlQuotient.pullback] using hRpoint
  have hR :
      |Q.micro.optimalValue x - R.macroModel.optimalValue (e (Q.f x))| ≤ R.D := by
    rw [hMicro, hex]
    exact hR0
  calc
    |Q.macroModel.optimalValue (Q.f x) -
        R.macroModel.optimalValue (e (Q.f x))| ≤
        |Q.macroModel.optimalValue (Q.f x) - Q.micro.optimalValue x| +
          |Q.micro.optimalValue x -
            R.macroModel.optimalValue (e (Q.f x))| :=
      abs_sub_le _ _ _
    _ ≤ Q.D + R.D := by
      rw [abs_sub_comm (Q.macroModel.optimalValue (Q.f x))
        (Q.micro.optimalValue x)]
      exact add_le_add hQ hR

/-- The quantitative semantic content of one relabeling between approximate
quotients. -/
def ApproxSemanticRelabel
    (Q R : ApproxControlQuotient X S (fun _ => Act))
    (e : S ≃ S) : Prop :=
  e ∘ Q.f = R.f ∧
  (∀ s a,
    |Q.macroModel.reward s a - R.macroModel.reward (e s) a| ≤
      Q.epsilonReward + R.epsilonReward) ∧
  (∀ s a,
    FiniteProbabilityRow.tvDist
        ((Q.macroModel.transitionPMF s a).map e)
        (R.macroModel.transitionPMF (e s) a) ≤
      Q.epsilonTransition + R.epsilonTransition) ∧
  (∀ s,
    |Q.macroModel.optimalValue s - R.macroModel.optimalValue (e s)| ≤
      Q.D + R.D)

/-- Same source fibres generate one unique state relabeling carrying all three
approximate semantic certificates.  Uniqueness comes from M-QD quotient gauge,
not from the numerical error bounds. -/
theorem existsUnique_approxSemanticRelabel_of_sameFibers
    (Q R : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (hsame : SameFibers Q.f R.f) :
    ∃! e : S ≃ S, ApproxSemanticRelabel Q R e := by
  let e : S ≃ S := quotientEquiv Q.f R.f Q.surjective R.surjective hsame
  have he : e ∘ Q.f = R.f :=
    quotientEquiv_comp Q.f R.f Q.surjective R.surjective hsame
  refine ⟨e, ⟨he, ?_, ?_, ?_⟩, ?_⟩
  · intro s a
    exact macroReward_relabel_le Q R hMicro e he s a
  · intro s a
    exact macroTransition_relabel_tv_le Q R hMicro e he s a
  · intro s
    exact macroOptimalValue_relabel_le Q R hMicro e he s
  · intro e' he'
    exact quotientEquiv_unique Q.f R.f Q.surjective R.surjective hsame e' he'.1

end


end UEOT.V3.Compression.ApproximateSemanticGauge
