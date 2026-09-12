import UEOT.V3.InformationBernoulliKL
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bernoulli KL as the sharp Fano penalty

The correctness indicator under the true law has success probability `1-e`.
Under the independent reference law with a uniform `K`-ary identity, its
success probability is `1/K`.  This module identifies the resulting two-point
KL divergence with the exact sharp Fano expression.
-/

namespace UEOT.V3.InformationBernoulliFano

open MeasureTheory InformationTheory
open UEOT.V3.InformationBernoulliKL

/-- Lift the exact real Bernoulli KL formula back to `ENNReal`. -/
theorem bernoulliLaw_klDiv_eq_ofReal {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    klDiv (bernoulliLaw p) (bernoulliLaw q) =
      ENNReal.ofReal
        (p * Real.log (p / q) +
          (1 - p) * Real.log ((1 - p) / (1 - q))) := by
  have hac : bernoulliLaw p ≪ bernoulliLaw q :=
    bernoulliLaw_ac_of_reference_interior hq0 hq1
  have hint : Integrable
      (llr (bernoulliLaw p) (bernoulliLaw q)) (bernoulliLaw p) :=
    bernoulliLaw_llr_integrable
  have hfin : klDiv (bernoulliLaw p) (bernoulliLaw q) ≠ ⊤ :=
    klDiv_ne_top hac hint
  rw [← ENNReal.ofReal_toReal hfin,
    bernoulliLaw_klDiv_toReal hp0 hp1 hq0 hq1]

/-- For `K ≥ 2`, the Bernoulli KL divergence between correctness probability
`1-e` and the independent-reference correctness probability `1/K` is exactly
`log K - h₂(e) - e log(K-1)`. -/
theorem bernoulli_correct_kl_eq_fano
    {K : ℕ} (hK : 2 ≤ K)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    klDiv (bernoulliLaw (1 - e))
        (bernoulliLaw ((K : ℝ)⁻¹)) =
      ENNReal.ofReal
        (Real.log (K : ℝ) - Real.binEntropy e -
          e * Real.log ((K : ℝ) - 1)) := by
  have hKr : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := lt_trans zero_lt_one hKr
  have hq0 : (0 : ℝ) < (K : ℝ)⁻¹ := inv_pos.mpr hK0
  have hq1 : (K : ℝ)⁻¹ < 1 := inv_lt_one₀ hKr
  rw [bernoulliLaw_klDiv_eq_ofReal
    (sub_nonneg.mpr he1) (by linarith) hq0 hq1]
  congr 1
  by_cases he_zero : e = 0
  · subst e
    simp [Real.binEntropy_zero, hK0.ne']
  by_cases he_one : e = 1
  · subst e
    have hKm1 : (0 : ℝ) < (K : ℝ) - 1 := by linarith
    rw [Real.binEntropy_one]
    simp only [sub_self, zero_mul, zero_div, one_sub_zero, one_mul, sub_zero]
    rw [show 1 - (K : ℝ)⁻¹ = ((K : ℝ) - 1) / (K : ℝ) by
      field_simp [hK0.ne']; ring]
    rw [one_div_div, Real.log_div hK0.ne' hKm1.ne']
    ring
  have he_pos : 0 < e := lt_of_le_of_ne he0 (Ne.symm he_zero)
  have he_lt : e < 1 := lt_of_le_of_ne he1 he_one
  have h1e_pos : 0 < 1 - e := sub_pos.mpr he_lt
  have hKm1 : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  have hqcomp : 1 - (K : ℝ)⁻¹ = ((K : ℝ) - 1) / (K : ℝ) := by
    field_simp [hK0.ne']
    ring
  rw [Real.binEntropy]
  rw [Real.log_div h1e_pos.ne' hq0.ne',
    Real.log_div he_pos.ne' (sub_pos.mpr hq1).ne',
    Real.log_inv,
    hqcomp,
    Real.log_div hKm1.ne' hK0.ne',
    Real.log_inv,
    Real.log_inv]
  ring

end UEOT.V3.InformationBernoulliFano
