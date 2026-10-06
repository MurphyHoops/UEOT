import UEOT.V3.Compression.ApproximateHistoryEncoder
import UEOT.V3.Compression.StructuralDefectControlLimit
import Mathlib.Tactic

/-!
# P3.4 — estimator error -> structural control defects

This module is the explicit adapter between statistical estimation and the
fixed-source control interfaces used by Core v3.

The estimator may output a different macro model at every sample size.  What is
required is source-facing error control: every micro reward and every encoded
micro transition row is close to the corresponding estimated macro cell, with
radii tending to zero.  From those estimator bounds we *derive* the true
within-encoder-fibre structural defects, with the sharp elementary envelope
`2 * radius`.

Thus P3 does not assume the terminal structural defects vanish.  Their
vanishing is a theorem from estimator consistency.  This is an adapter
interface: P3-STAT response consistency alone does not identify rewards unless
the domain supplies a reward estimator/observable bridge.
-/

namespace UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency

open Filter Topology MeasureTheory
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.Compression.ApproximateHistoryEncoder
open UEOT.V3.Compression.StructuralDefectControlLimit

universe uH uS uA

/-- Realized control-model estimator sequence for one fixed source and one
fixed candidate encoder.  `macroHat n` itself need not converge. -/
structure RealizedControlEstimator
    {H : Type uH} [Fintype H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S)
    (micro : Model H (fun _ => Act)) where
  macroHat : ℕ → Model S (fun _ => Act)
  rewardRadius : ℕ → ℝ
  transitionRadius : ℕ → ℝ
  rewardRadius_nonneg : ∀ n, 0 ≤ rewardRadius n
  transitionRadius_nonneg : ∀ n, 0 ≤ transitionRadius n
  rewardRadius_tendsto_zero : Tendsto rewardRadius atTop (𝓝 0)
  transitionRadius_tendsto_zero : Tendsto transitionRadius atTop (𝓝 0)
  reward_estimation : ∀ n h a,
    |micro.reward h a - (macroHat n).reward (C h) a| ≤ rewardRadius n
  transition_estimation : ∀ n h a,
    FiniteProbabilityRow.tvDist
      (pushforwardTransitionPMF C micro h a)
      ((macroHat n).transitionPMF (C h) a) ≤ transitionRadius n

namespace RealizedControlEstimator

variable
    {H : Type uH} [Fintype H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    {C : H → S}
    {micro : Model H (fun _ => Act)}

/-- Estimation against one common macro cell forces true rewards in the same
encoder fibre to be close. -/
theorem reward_fiber_bound
    (E : RealizedControlEstimator C micro)
    (n : ℕ) {h h' : H} (a : Act) (hsame : C h = C h') :
    |micro.reward h a - micro.reward h' a| ≤ 2 * E.rewardRadius n := by
  have hleft := E.reward_estimation n h a
  have hright := E.reward_estimation n h' a
  rw [← hsame] at hright
  have hright' :
      |(E.macroHat n).reward (C h) a - micro.reward h' a| ≤
        E.rewardRadius n := by
    simpa [abs_sub_comm] using hright
  have htri := abs_add_le
    (micro.reward h a - (E.macroHat n).reward (C h) a)
    ((E.macroHat n).reward (C h) a - micro.reward h' a)
  calc
    |micro.reward h a - micro.reward h' a| =
        |(micro.reward h a - (E.macroHat n).reward (C h) a) +
          ((E.macroHat n).reward (C h) a - micro.reward h' a)| := by ring_nf
    _ ≤ |micro.reward h a - (E.macroHat n).reward (C h) a| +
          |(E.macroHat n).reward (C h) a - micro.reward h' a| := htri
    _ ≤ E.rewardRadius n + E.rewardRadius n := add_le_add hleft hright'
    _ = 2 * E.rewardRadius n := by ring

private theorem finite_tvDist_symm {T : Type*} (p q : PMF T) :
    FiniteProbabilityRow.tvDist p q = FiniteProbabilityRow.tvDist q p := by
  letI : MeasurableSpace T := ⊤
  change UEOT.V3.TotalVariation.tvDist p.toMeasure q.toMeasure =
    UEOT.V3.TotalVariation.tvDist q.toMeasure p.toMeasure
  let _ : IsProbabilityMeasure p.toMeasure := by infer_instance
  let _ : IsProbabilityMeasure q.toMeasure := by infer_instance
  exact UEOT.V3.StatisticalDefect.tvDist_symm _ _

/-- Estimation against one common macro row forces true encoded transition rows
in the same encoder fibre to be close. -/
theorem transition_fiber_bound
    (E : RealizedControlEstimator C micro)
    (n : ℕ) {h h' : H} (a : Act) (hsame : C h = C h') :
    FiniteProbabilityRow.tvDist
      (pushforwardTransitionPMF C micro h a)
      (pushforwardTransitionPMF C micro h' a) ≤
        2 * E.transitionRadius n := by
  let p := pushforwardTransitionPMF C micro h a
  let q := (E.macroHat n).transitionPMF (C h) a
  let r := pushforwardTransitionPMF C micro h' a
  have hleft : FiniteProbabilityRow.tvDist p q ≤ E.transitionRadius n := by
    simpa [p, q] using E.transition_estimation n h a
  have hright0 := E.transition_estimation n h' a
  rw [← hsame] at hright0
  have hright : FiniteProbabilityRow.tvDist q r ≤ E.transitionRadius n := by
    rw [finite_tvDist_symm q r]
    simpa [q, r] using hright0
  have htri := finite_tvDist_triangle p q r
  calc
    FiniteProbabilityRow.tvDist p r ≤
        FiniteProbabilityRow.tvDist p q + FiniteProbabilityRow.tvDist q r := htri
    _ ≤ E.transitionRadius n + E.transitionRadius n := add_le_add hleft hright
    _ = 2 * E.transitionRadius n := by ring

/-- Statistically justified reward structural-defect envelope vanishes. -/
theorem reward_defect_radius_tendsto_zero
    (E : RealizedControlEstimator C micro) :
    Tendsto (fun n => 2 * E.rewardRadius n) atTop (𝓝 0) := by
  simpa using E.rewardRadius_tendsto_zero.const_mul (2 : ℝ)

/-- Statistically justified transition structural-defect envelope vanishes. -/
theorem transition_defect_radius_tendsto_zero
    (E : RealizedControlEstimator C micro) :
    Tendsto (fun n => 2 * E.transitionRadius n) atTop (𝓝 0) := by
  simpa using E.transitionRadius_tendsto_zero.const_mul (2 : ℝ)

/-- Estimator error bounds construct the existing P-CORE-01 fixed-source
approximation interface.  The target is the canonical representative macro
model, so it is fixed across `n`; no convergence of `macroHat n` is needed. -/
noncomputable def toCanonicalFixedSourceApproximation
    (E : RealizedControlEstimator C micro)
    (hC : Function.Surjective C) (n : ℕ) :
    FixedSourceApproximation (Abar := fun _ : S => Act) C micro
      (2 * E.rewardRadius n) (2 * E.transitionRadius n) where
  macroModel := representativeMacroModel C hC micro
  discount_eq := rfl
  reward_approx := by
    intro h a
    change
      |micro.reward h a -
          micro.reward (representative C hC (C h)) a| ≤
        2 * E.rewardRadius n
    exact E.reward_fiber_bound n a
      (encoder_representative C hC (C h)).symm
  transition_tv_approx := by
    intro h a
    rw [representativeMacroModel_transitionPMF]
    exact E.transition_fiber_bound n a
      (encoder_representative C hC (C h)).symm

@[simp] theorem toCanonicalFixedSourceApproximation_macroModel
    (E : RealizedControlEstimator C micro)
    (hC : Function.Surjective C) (n : ℕ) :
    (E.toCanonicalFixedSourceApproximation hC n).macroModel =
      representativeMacroModel C hC micro := rfl

end RealizedControlEstimator

end UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency
