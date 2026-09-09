import UEOT.Core.Reward
import Mathlib.Analysis.SpecificLimits.Normed

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

theorem bounded_potential_tail
    (β M : ℝ) (ψ : ℕ → ℝ)
    (hβ : |β| < 1)
    (hψ : ∀ n, |ψ n| ≤ M) :
    Tendsto (fun n => β ^ n * ψ n) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun n => |β| ^ n * M) ?_ ?_
  · exact Filter.Eventually.of_forall (fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hψ n) (pow_nonneg (abs_nonneg β) n))
  · exact
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

end UEOT.V3.RewardInfinite
