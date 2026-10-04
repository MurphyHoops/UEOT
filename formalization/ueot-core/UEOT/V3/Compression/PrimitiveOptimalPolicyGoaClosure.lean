import UEOT.V3.Compression.PrimitiveRewardSpanClosure

/-!
# Primitive-defect optimal-policy GOA closure

The moving optimal-policy GOA theorem previously accepted `D_n -> 0` directly,
and the first value-span closure derived it only after an external uniform span
hypothesis.  `PrimitiveRewardSpanClosure` removes that auxiliary premise for
quotients sharing one finite micro model.  This module exposes the resulting
primitive-input terminal API.
-/

namespace UEOT.V3.Compression.PrimitiveOptimalPolicyGoaClosure

open Filter Topology Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.MovingEncoderSemanticGoaClosure
open UEOT.V3.Compression.PrimitiveRewardSpanClosure

universe uX uS uA

noncomputable section

variable {X : Type uX} [Fintype X] [Nonempty X]
variable {S : Type uS} [Fintype S] [Nonempty S]
variable {Act : Type uA} [Fintype Act] [Nonempty Act]

/-- Primitive reward/transition convergence, exact reference defects, moving
representation lock, a strict source action gap and source closed-loop
contraction suffice for eventual unique optimal-policy near-GOA gauge closure.
No independent `D_n -> 0` or uniform optimal-value-span assumption remains. -/
theorem eventually_existsUnique_optimalPolicyNearGoaGaugeAt_of_primitiveDefects
    (mu : stdSimplex ℝ X) (hfull : ∀ x, 0 < mu x)
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (hGauge : Tendsto
      (fun n => WeightedQuotientGauge.weightedGaugeMismatch mu (Qseq n).f Qref.f)
      atTop (𝓝 0))
    (hMicro : ∀ n, Qref.micro = (Qseq n).micro)
    (hrefR : Qref.epsilonReward = 0)
    (hrefP : Qref.epsilonTransition = 0)
    (hR : Tendsto (fun n => (Qseq n).epsilonReward) atTop (𝓝 0))
    (hP : Tendsto (fun n => (Qseq n).epsilonTransition) atTop (𝓝 0))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hsourceGap : ∀ s a, a ≠ Qref.macroModel.greedyAction s →
      gamma ≤
        Qref.macroModel.qValue Qref.macroModel.optimalValue s
            (Qref.macroModel.greedyAction s) -
          Qref.macroModel.qValue Qref.macroModel.optimalValue s a)
    (halpha :
      FiniteDobrushin.dobrushinAlpha
        (GoaGaugeInvariance.selectorClosedLoopMatrix
          Qref.macroModel Qref.macroModel.greedyAction)
        (GoaGaugeInvariance.selectorClosedLoopMatrix_rowStochastic
          Qref.macroModel Qref.macroModel.greedyAction) < 1) :
    ∀ᶠ n in atTop,
      ∃! e : S ≃ S,
        OptimalPolicyNearGoaGaugeAt Qref (Qseq n) e := by
  have hrefD : Qref.D = 0 :=
    D_eq_zero_of_exact_defects Qref hrefR hrefP
  have hD : Tendsto (fun n => (Qseq n).D) atTop (𝓝 0) :=
    D_tendsto_zero_of_primitive_defects Qref Qseq hMicro hR hP
  exact eventually_existsUnique_optimalPolicyNearGoaGaugeAt
    mu hfull Qref Qseq hGauge hMicro hrefD hD gamma hgamma hsourceGap halpha

/-- Fully primitive moving tail closure.  Under the same hypotheses, the unique
optimal-policy gauge certificate has arbitrarily small stationary-law radius. -/
theorem eventually_optimalPolicyNearGoa_arbitrarily_close_of_primitiveDefects
    (mu : stdSimplex ℝ X) (hfull : ∀ x, 0 < mu x)
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (hGauge : Tendsto
      (fun n => WeightedQuotientGauge.weightedGaugeMismatch mu (Qseq n).f Qref.f)
      atTop (𝓝 0))
    (hMicro : ∀ n, Qref.micro = (Qseq n).micro)
    (hrefR : Qref.epsilonReward = 0)
    (hrefP : Qref.epsilonTransition = 0)
    (hR : Tendsto (fun n => (Qseq n).epsilonReward) atTop (𝓝 0))
    (hP : Tendsto (fun n => (Qseq n).epsilonTransition) atTop (𝓝 0))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hsourceGap : ∀ s a, a ≠ Qref.macroModel.greedyAction s →
      gamma ≤
        Qref.macroModel.qValue Qref.macroModel.optimalValue s
            (Qref.macroModel.greedyAction s) -
          Qref.macroModel.qValue Qref.macroModel.optimalValue s a)
    (halpha :
      FiniteDobrushin.dobrushinAlpha
        (GoaGaugeInvariance.selectorClosedLoopMatrix
          Qref.macroModel Qref.macroModel.greedyAction)
        (GoaGaugeInvariance.selectorClosedLoopMatrix_rowStochastic
          Qref.macroModel Qref.macroModel.greedyAction) < 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ n in atTop,
      ∃! e : S ≃ S,
        OptimalPolicyNearGoaGaugeAt Qref (Qseq n) e ∧
        movingNearGoaRadius Qref Qseq Qref.macroModel.greedyAction n < eta := by
  have hrefD : Qref.D = 0 :=
    D_eq_zero_of_exact_defects Qref hrefR hrefP
  have hD : Tendsto (fun n => (Qseq n).D) atTop (𝓝 0) :=
    D_tendsto_zero_of_primitive_defects Qref Qseq hMicro hR hP
  exact eventually_optimalPolicyNearGoa_arbitrarily_close
    mu hfull Qref Qseq hGauge hMicro hrefD hD gamma hgamma hsourceGap
      halpha hrefP hP eta heta

end
end UEOT.V3.Compression.PrimitiveOptimalPolicyGoaClosure
