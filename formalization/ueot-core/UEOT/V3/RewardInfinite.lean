import UEOT.Core.Reward
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# P-TEL-01 — infinite-horizon analytic core

This module lifts the already verified finite-horizon shaping identity to an
infinite discounted limit.  It is deliberately phrased for policy-induced
expected sequences: Markov-control existence is a P-CTL responsibility, while
P-TEL-01 only needs the value sequences, bounded potential, and discount
convergence.
-/

namespace UEOT.V3.RewardInfinite

open Filter Topology
open UEOT.Reward

open MeasureTheory

theorem bounded_potential_integrable
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ψ : X → ℝ) (M : ℝ)
    (hψm : StronglyMeasurable ψ)
    (hψ : ∀ x, |ψ x| ≤ M) :
    Integrable ψ μ := by
  refine Integrable.of_bound hψm.aestronglyMeasurable M ?_
  exact Filter.Eventually.of_forall (fun x => by
    simpa [Real.norm_eq_abs] using hψ x)

theorem bounded_expected_potential
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ψ : X → ℝ) (M : ℝ)
    (hψm : StronglyMeasurable ψ)
    (hψ : ∀ x, |ψ x| ≤ M) :
    |∫ x, ψ x ∂μ| ≤ M := by
  have hint : Integrable ψ μ :=
    bounded_potential_integrable μ ψ M hψm hψ
  have hb :
      ‖∫ x, ψ x ∂μ‖ ≤ M * μ.real Set.univ :=
    norm_integral_le_of_norm_le_const
      (μ := μ)
      (Filter.Eventually.of_forall (fun x => by
        simpa [Real.norm_eq_abs] using hψ x))
  simpa [Real.norm_eq_abs] using hb

noncomputable def expectedPotential
    {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X) (ψ : X → ℝ) (n : ℕ) : ℝ :=
  ∫ x, ψ x ∂μ n

theorem expectedPotential_bounded
    {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (μ n)]
    (ψ : X → ℝ) (M : ℝ)
    (hψm : StronglyMeasurable ψ)
    (hψ : ∀ x, |ψ x| ≤ M) :
    ∀ n, |expectedPotential μ ψ n| ≤ M := by
  intro n
  exact bounded_expected_potential (μ n) ψ M hψm hψ

theorem expectedPotential_dirac
    {X : Type*} [MeasurableSpace X]
    (ψ : X → ℝ) (hψm : StronglyMeasurable ψ) (x : X) :
    expectedPotential (fun _ => Measure.dirac x) ψ 0 = ψ x := by
  simp [expectedPotential, integral_dirac' ψ x hψm]

theorem bounded_potential_tail
    (β M : ℝ) (ψ : ℕ → ℝ)
    (hβ : |β| < 1)
    (hψ : ∀ n, |ψ n| ≤ M) :
    Tendsto (fun n => β ^ n * ψ n) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun n => |β| ^ n * M) ?_ ?_
  · exact Filter.Eventually.of_forall (fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hψ n) (pow_nonneg (abs_nonneg β) n))
  · simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg β) hβ).mul_const M

theorem discounted_one_tendsto
    (β : ℝ) (hβ : |β| < 1) :
    Tendsto (fun n => discounted β (fun _ => 1) n)
      atTop (𝓝 ((1 - β)⁻¹)) := by
  have hnorm : ‖β‖ < 1 := by simpa [Real.norm_eq_abs] using hβ
  have hsum : HasSum (fun n : ℕ => β ^ n) ((1 - β)⁻¹) :=
    hasSum_geometric_of_norm_lt_one hnorm
  simpa [discounted] using hsum.tendsto_sum_nat

theorem shaping_tendsto
    (β a c M V : ℝ) (r ψ : ℕ → ℝ)
    (hβ : |β| < 1)
    (hψ : ∀ n, |ψ n| ≤ M)
    (hr : Tendsto (fun n => discounted β r n) atTop (𝓝 V)) :
    Tendsto
      (fun n => discounted β
        (fun t => a * r t + β * ψ (t + 1) - ψ t + c) n)
      atTop
      (𝓝 (a * V - ψ 0 + c * (1 - β)⁻¹)) := by
  have htail := bounded_potential_tail β M ψ hβ hψ
  have hgeom := discounted_one_tendsto β hβ
  have hlim :
      Tendsto
        (fun n =>
          a * discounted β r n + β ^ n * ψ n - ψ 0 +
            c * discounted β (fun _ => 1) n)
        atTop
        (𝓝 (a * V - ψ 0 + c * (1 - β)⁻¹)) := by
    simpa using
      (((Tendsto.const_mul a hr).add htail).sub tendsto_const_nhds).add
        (Tendsto.const_mul c hgeom)
  simpa only [shaping_finite] using hlim

theorem shaping_limit_value
    (β a c M V V' : ℝ) (r ψ : ℕ → ℝ)
    (hβ : |β| < 1)
    (hψ : ∀ n, |ψ n| ≤ M)
    (hr : Tendsto (fun n => discounted β r n) atTop (𝓝 V))
    (hr' : Tendsto
      (fun n => discounted β
        (fun t => a * r t + β * ψ (t + 1) - ψ t + c) n)
      atTop (𝓝 V')) :
    V' = a * V - ψ 0 + c * (1 - β)⁻¹ := by
  exact tendsto_nhds_unique hr' (shaping_tendsto β a c M V r ψ hβ hψ hr)

theorem policy_values_affine
    {P : Type*}
    (β a c M ψ0 : ℝ)
    (r ψ : P → ℕ → ℝ)
    (V V' : P → ℝ)
    (hβ : |β| < 1)
    (ha : 0 < a)
    (hψ0 : ∀ p, ψ p 0 = ψ0)
    (hψ : ∀ p n, |ψ p n| ≤ M)
    (hr : ∀ p, Tendsto (fun n => discounted β (r p) n) atTop (𝓝 (V p)))
    (hr' : ∀ p, Tendsto
      (fun n => discounted β
        (fun t => a * r p t + β * ψ p (t + 1) - ψ p t + c) n)
      atTop (𝓝 (V' p))) :
    (∀ p, V' p = a * V p - ψ0 + c * (1 - β)⁻¹) ∧
      ∀ p, IsMaximizer V' p ↔ IsMaximizer V p := by
  have hval : ∀ p, V' p = a * V p - ψ0 + c * (1 - β)⁻¹ := by
    intro p
    rw [shaping_limit_value β a c M (V p) (V' p)
      (r p) (ψ p) hβ (hψ p) (hr p) (hr' p), hψ0 p]
  refine ⟨hval, ?_⟩
  intro p
  have hfun :
      V' = fun q => a * V q + (-ψ0 + c * (1 - β)⁻¹) := by
    funext q
    rw [hval q]
    ring
  rw [hfun]
  exact positive_affine_maximizer V a (-ψ0 + c * (1 - β)⁻¹) ha p


theorem policy_values_affine_from_bounded_state_potential
    {P X : Type*} [MeasurableSpace X]
    (μ : P → ℕ → Measure X)
    [∀ p n, IsProbabilityMeasure (μ p n)]
    (ψState : X → ℝ) (x : X)
    (β a c M : ℝ)
    (r : P → ℕ → ℝ)
    (V V' : P → ℝ)
    (hβ : |β| < 1)
    (ha : 0 < a)
    (hψm : StronglyMeasurable ψState)
    (hψ : ∀ y, |ψState y| ≤ M)
    (hμ0 : ∀ p, μ p 0 = Measure.dirac x)
    (hr : ∀ p,
      Tendsto (fun n => discounted β (r p) n) atTop (𝓝 (V p)))
    (hr' : ∀ p,
      Tendsto
        (fun n => discounted β
          (fun t =>
            a * r p t
              + β * expectedPotential (μ p) ψState (t + 1)
              - expectedPotential (μ p) ψState t
              + c) n)
        atTop (𝓝 (V' p))) :
    (∀ p, V' p = a * V p - ψState x + c * (1 - β)⁻¹) ∧
      ∀ p, IsMaximizer V' p ↔ IsMaximizer V p := by
  have hbound :
      ∀ p n, |expectedPotential (μ p) ψState n| ≤ M := by
    intro p n
    exact bounded_expected_potential (μ p n) ψState M hψm hψ
  have hinit :
      ∀ p, expectedPotential (μ p) ψState 0 = ψState x := by
    intro p
    rw [expectedPotential, hμ0 p]
    exact integral_dirac' ψState x hψm
  exact policy_values_affine
    β a c M (ψState x)
    r
    (fun p n => expectedPotential (μ p) ψState n)
    V V' hβ ha hinit hbound hr hr'

end UEOT.V3.RewardInfinite
