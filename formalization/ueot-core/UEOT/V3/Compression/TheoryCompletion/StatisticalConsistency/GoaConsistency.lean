import UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency.GodPolicyConsistency
import UEOT.V3.Compression.PrimitiveOptimalPolicyGoaClosure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency

open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression
open UEOT.V3.Compression.MovingEncoderSemanticGoaClosure
open UEOT.V3.Compression.PrimitiveOptimalPolicyGoaClosure

universe uX uS uA

/-- Canonical full-support source law used only to discharge the representation
lock interface for a fixed finite nonempty encoder source. -/
noncomputable def canonicalFullSupportLaw
    (X : Type uX) [Fintype X] [Nonempty X] : stdSimplex ℝ X := by
  let mu : PMF X := PMF.uniformOfFintype X
  refine ⟨fun x => (mu x).toReal, ?_, ?_⟩
  · intro x
    exact ENNReal.toReal_nonneg
  · have h := congrArg ENNReal.toReal (PMF.tsum_coe mu)
    rw [tsum_fintype,
      ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top mu x)] at h
    simpa using h

@[simp] theorem canonicalFullSupportLaw_apply
    (X : Type uX) [Fintype X] [Nonempty X] (x : X) :
    canonicalFullSupportLaw X x =
      ((Fintype.card X : ℝ≥0∞)⁻¹).toReal := by
  change (PMF.uniformOfFintype X x).toReal = _
  rw [PMF.uniformOfFintype_apply]

theorem canonicalFullSupportLaw_pos
    (X : Type uX) [Fintype X] [Nonempty X] (x : X) :
    0 < canonicalFullSupportLaw X x := by
  rw [canonicalFullSupportLaw_apply, ENNReal.toReal_inv]
  have hcard : 0 < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos
  simpa using inv_pos.mpr hcard

/-- Under a positive canonical action gap and explicit Dobrushin isolation of
the canonical greedy closed loop, a statistically consistent fixed-encoder
estimator has eventual optimal-policy GOA certificates with arbitrarily small
stationary-law radius.

The full-support source law and representation gauge are not extra assumptions:
the source law is canonical uniform and the gauge mismatch is identically zero
because every estimate uses the same encoder `C`.  `[Nonempty S]` is exposed
only because the downstream Dobrushin API is typeclass-indexed; it is already
implied mathematically by `[Nonempty X]` and surjectivity of `C`. -/
theorem eventually_goa_consistent_of_realizedEstimator
    {X : Type uX} [Fintype X] [Nonempty X]
    {S : Type uS} [Fintype S] [Nonempty S]
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
            Qexact.macroModel.qValue Qexact.macroModel.optimalValue s a)
    (halpha :
      let Qexact := exactControlQuotient_of_realizedEstimator C hC micro E
      FiniteDobrushin.dobrushinAlpha
        (GoaGaugeInvariance.selectorClosedLoopMatrix
          Qexact.macroModel Qexact.macroModel.greedyAction)
        (GoaGaugeInvariance.selectorClosedLoopMatrix_rowStochastic
          Qexact.macroModel Qexact.macroModel.greedyAction) < 1)
    (eta : ℝ) (heta : 0 < eta) :
    let Qexact := exactControlQuotient_of_realizedEstimator C hC micro E
    let Qref : ApproxControlQuotient X S (fun _ => Act) := exactAsApprox Qexact
    let Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act) :=
      fun n => estimatedApproxControlQuotient E hC hdiscount n
    ∀ᶠ n in atTop,
      ∃! e : S ≃ S,
        OptimalPolicyNearGoaGaugeAt Qref (Qseq n) e ∧
        movingNearGoaRadius Qref Qseq Qref.macroModel.greedyAction n < eta := by
  dsimp only
  let mu : stdSimplex ℝ X := canonicalFullSupportLaw X
  let Qexact := exactControlQuotient_of_realizedEstimator C hC micro E
  let Qref : ApproxControlQuotient X S (fun _ => Act) := exactAsApprox Qexact
  let Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act) :=
    fun n => estimatedApproxControlQuotient E hC hdiscount n
  have hfull : ∀ x, 0 < mu x := by
    intro x
    exact canonicalFullSupportLaw_pos X x
  have hGauge : Tendsto
      (fun n => WeightedQuotientGauge.weightedGaugeMismatch mu (Qseq n).f Qref.f)
      atTop (𝓝 0) := by
    have hzero : ∀ n,
        WeightedQuotientGauge.weightedGaugeMismatch mu (Qseq n).f Qref.f = 0 := by
      intro n
      change WeightedQuotientGauge.weightedGaugeMismatch mu C C = 0
      exact WeightedQuotientGauge.weightedGaugeMismatch_self mu C
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) using 1
    funext n
    exact hzero n
  have hMicro : ∀ n, Qref.micro = (Qseq n).micro := by
    intro n
    rfl
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
  have halpha' :
      FiniteDobrushin.dobrushinAlpha
        (GoaGaugeInvariance.selectorClosedLoopMatrix
          Qref.macroModel Qref.macroModel.greedyAction)
        (GoaGaugeInvariance.selectorClosedLoopMatrix_rowStochastic
          Qref.macroModel Qref.macroModel.greedyAction) < 1 := by
    change FiniteDobrushin.dobrushinAlpha
        (GoaGaugeInvariance.selectorClosedLoopMatrix
          Qexact.macroModel Qexact.macroModel.greedyAction)
        (GoaGaugeInvariance.selectorClosedLoopMatrix_rowStochastic
          Qexact.macroModel Qexact.macroModel.greedyAction) < 1
    exact halpha
  exact eventually_optimalPolicyNearGoa_arbitrarily_close_of_primitiveDefects
    mu hfull Qref Qseq hGauge hMicro rfl rfl
    (by simpa [Qseq, estimatedApproxControlQuotient] using
      E.rewardRadius_tendsto_zero)
    (by simpa [Qseq, estimatedApproxControlQuotient] using
      E.transitionRadius_tendsto_zero)
    gamma hgamma hsourceGap' halpha' eta heta

end UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency
