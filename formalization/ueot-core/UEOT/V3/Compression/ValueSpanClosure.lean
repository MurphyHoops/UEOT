import UEOT.V3.Compression.MovingEncoderSemanticGoaClosure

/-!
# Value-span closure for moving approximate quotients

The moving encoder/GOA lane previously required `D_n → 0` as an independent
certificate.  That boundary is real without control of the moving macro
optimal-value span, because

`D_n = (εr_n + β εp_n span(V*_n)) / (1 - β)`.

This module closes that gap under one explicit uniform span bound.  A common
literal micro model fixes the discount, the primitive reward/transition defects
go to zero, and the bounded span prevents the transition term from amplifying.
The resulting theorem derives `D_n → 0` rather than assuming it.
-/

namespace UEOT.V3.Compression.ValueSpanClosure

open Filter Topology Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.MovingEncoderSemanticGoaClosure

universe uX uS uA

noncomputable section

variable {X : Type uX} [Fintype X] [Nonempty X]
variable {S : Type uS} [Fintype S] [Nonempty S]
variable {Act : Type uA} [Fintype Act] [Nonempty Act]

/-- A common literal micro model fixes the discount across moving macro models. -/
theorem macroDiscount_eq_ref_of_commonMicro
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qn : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Qref.micro = Qn.micro) :
    Qn.macroModel.discount = Qref.macroModel.discount := by
  calc
    Qn.macroModel.discount = Qn.micro.discount := Qn.discount_eq.symm
    _ = Qref.micro.discount := by rw [← hMicro]
    _ = Qref.macroModel.discount := Qref.discount_eq

/-- A uniform macro optimal-value span bound controls the P-QUO global radius
directly by the primitive reward/transition defect envelope. -/
theorem D_le_of_span_le
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qn : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Qref.micro = Qn.micro)
    (C : ℝ)
    (hspan : UEOT.V3.TVSpan.span Qn.macroModel.optimalValue ≤ C) :
    Qn.D ≤
      (Qn.epsilonReward +
          Qref.macroModel.discount * Qn.epsilonTransition * C) /
        (1 - Qref.macroModel.discount) := by
  have hdisc := macroDiscount_eq_ref_of_commonMicro Qref Qn hMicro
  have hden : 0 ≤ 1 - Qref.macroModel.discount :=
    sub_nonneg.mpr Qref.macroModel.discount_lt_one.le
  rw [ApproxControlQuotient.D, ApproxControlQuotient.delta, hdisc]
  apply div_le_div_of_nonneg_right _ hden
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left hspan
    (mul_nonneg Qref.macroModel.discount_pos.le Qn.epsilonTransition_nonneg)

/-- Primitive semantic defects imply `D_n → 0` once the moving macro optimal
values have one uniform span bound. -/
theorem D_tendsto_zero_of_uniform_span
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (hMicro : ∀ n, Qref.micro = (Qseq n).micro)
    (C : ℝ)
    (hspan : ∀ n, UEOT.V3.TVSpan.span (Qseq n).macroModel.optimalValue ≤ C)
    (hR : Tendsto (fun n => (Qseq n).epsilonReward) atTop (𝓝 0))
    (hP : Tendsto (fun n => (Qseq n).epsilonTransition) atTop (𝓝 0)) :
    Tendsto (fun n => (Qseq n).D) atTop (𝓝 0) := by
  let beta := Qref.macroModel.discount
  let den := 1 - beta
  let upper : ℕ → ℝ := fun n =>
    ((Qseq n).epsilonReward + beta * (Qseq n).epsilonTransition * C) / den
  have hupper0 : Tendsto upper atTop (𝓝 0) := by
    have htrans : Tendsto
        (fun n => beta * (Qseq n).epsilonTransition * C) atTop (𝓝 0) := by
      have h1 : Tendsto
          (fun n => beta * (Qseq n).epsilonTransition) atTop (𝓝 0) := by
        simpa using hP.const_mul beta
      simpa using h1.mul_const C
    have hnum : Tendsto
        (fun n => (Qseq n).epsilonReward +
          beta * (Qseq n).epsilonTransition * C) atTop (𝓝 0) := by
      simpa using hR.add htrans
    simpa [upper, den] using hnum.div_const den
  have hlower : ∀ n, 0 ≤ (Qseq n).D := fun n => (Qseq n).D_nonneg
  have hupper : ∀ n, (Qseq n).D ≤ upper n := by
    intro n
    simpa [upper, beta, den] using
      D_le_of_span_le Qref (Qseq n) (hMicro n) C (hspan n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper0
    (Filter.Eventually.of_forall hlower)
    (Filter.Eventually.of_forall hupper)

/-- Exact reference defects plus primitive moving reward/transition convergence
remove the formerly explicit `D_n → 0` hypothesis from the moving optimal-policy
GOA theorem, provided one uniform optimal-value span bound is available. -/
theorem eventually_existsUnique_optimalPolicyNearGoaGaugeAt_of_uniformSpan
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
    (C : ℝ)
    (hspan : ∀ n, UEOT.V3.TVSpan.span (Qseq n).macroModel.optimalValue ≤ C)
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
    D_tendsto_zero_of_uniform_span Qref Qseq hMicro C hspan hR hP
  exact eventually_existsUnique_optimalPolicyNearGoaGaugeAt
    mu hfull Qref Qseq hGauge hMicro hrefD hD gamma hgamma hsourceGap halpha

/-- Fully primitive tail closure: under the same uniform-span hypothesis, the
moving optimal-policy GOA radius becomes arbitrarily small using only the
primitive reward/transition defect limits. -/
theorem eventually_optimalPolicyNearGoa_arbitrarily_close_of_uniformSpan
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
    (C : ℝ)
    (hspan : ∀ n, UEOT.V3.TVSpan.span (Qseq n).macroModel.optimalValue ≤ C)
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
    D_tendsto_zero_of_uniform_span Qref Qseq hMicro C hspan hR hP
  exact eventually_optimalPolicyNearGoa_arbitrarily_close
    mu hfull Qref Qseq hGauge hMicro hrefD hD gamma hgamma hsourceGap
      halpha hrefP hP eta heta

end

end UEOT.V3.Compression.ValueSpanClosure
