import UEOT.Core.Reward
import Mathlib.Analysis.SpecificLimits.Normed

/-!
P-TEL-01 infinite-horizon convergence layer.

The finite-horizon telescope is already proved in UEOT.Core.Reward.  The first
missing infinite-horizon obligation is to justify removal of the terminal
potential term under the source assumptions: bounded potential and discounted
factor with absolute value strictly below one.
-/

namespace UEOT.V3.RewardInfinite

open Filter Topology

theorem terminal_potential_vanishes
    (β : ℝ) (ψ : ℕ → ℝ) (C : ℝ)
    (hβ : |β| < 1)
    (hψ : ∀ n, |ψ n| ≤ C) :
    Tendsto (fun n : ℕ => β ^ n * ψ n) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun n : ℕ => |β| ^ n * C) ?_ ?_
  · exact Filter.Eventually.of_forall (fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hψ n) (pow_nonneg (abs_nonneg β) n))
  · have hpow : Tendsto (fun n : ℕ => |β| ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by
        simpa only [abs_abs] using hβ)
    simpa using hpow.mul_const C

end UEOT.V3.RewardInfinite
