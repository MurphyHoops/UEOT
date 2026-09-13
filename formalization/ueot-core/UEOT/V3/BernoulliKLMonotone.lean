import UEOT.V3.PathEventKL
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# P-KL-02 support — active-side Bernoulli KL monotonicity

This support layer isolates the one-dimensional inequality needed after P-KL-01:
for a fixed reference event probability `q ∈ (0,1)`, Bernoulli KL is increasing
as the constrained probability moves to the right of `q`.
-/

namespace UEOT.V3.BernoulliKLMonotone

noncomputable section

open Set InformationTheory
open UEOT.V3.InformationBernoulliKL
open UEOT.V3.PathEventKL

noncomputable def bernoulliCrossKL (x q : ℝ) : ℝ :=
  -Real.binEntropy x - x * Real.log q - (1 - x) * Real.log (1 - q)

lemma continuous_bernoulliCrossKL (q : ℝ) :
    Continuous (fun x => bernoulliCrossKL x q) := by
  unfold bernoulliCrossKL
  fun_prop

lemma hasDerivAt_bernoulliCrossKL {x q : ℝ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (fun y => bernoulliCrossKL y q)
      (Real.log x - Real.log (1 - x) - Real.log q + Real.log (1 - q)) x := by
  unfold bernoulliCrossKL
  convert!
    (((Real.hasDerivAt_binEntropy hx0 hx1).neg).sub
      ((hasDerivAt_id x).mul_const (Real.log q))).sub
        (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).mul_const
          (Real.log (1 - q))) using 1
  ring

theorem bernoulliCrossKL_strictMonoOn {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    StrictMonoOn (fun x => bernoulliCrossKL x q) (Icc q 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc q 1)
    (continuous_bernoulliCrossKL q).continuousOn ?_
  intro x hx
  rw [interior_Icc, mem_Ioo] at hx
  have hx0 : 0 < x := hq0.trans hx.1
  have hx1 : x < 1 := hx.2
  have hratio : (1 - x) / (1 - q) < x / q := by
    rw [div_lt_div_iff₀ (sub_pos.mpr hq1) hq0]
    nlinarith
  have hlog :
      Real.log ((1 - x) / (1 - q)) < Real.log (x / q) :=
    Real.log_lt_log
      (div_pos (sub_pos.mpr hx1) (sub_pos.mpr hq1)) hratio
  rw [Real.log_div (sub_pos.mpr hx1).ne' (sub_pos.mpr hq1).ne',
    Real.log_div hx0.ne' hq0.ne'] at hlog
  rw [(hasDerivAt_bernoulliCrossKL hx0.ne' hx1.ne).deriv]
  linarith

lemma bernoulliCrossKL_eq_closedForm {x q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hqx : q ≤ x) (hx1 : x ≤ 1) :
    bernoulliCrossKL x q =
      x * Real.log (x / q) +
        (1 - x) * Real.log ((1 - x) / (1 - q)) := by
  by_cases hxone : x = 1
  · subst x
    simp [bernoulliCrossKL, Real.binEntropy, Real.log_inv]
  · have hx0 : 0 < x := hq0.trans_le hqx
    have hxlt1 : x < 1 := lt_of_le_of_ne hx1 hxone
    unfold bernoulliCrossKL Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    rw [Real.log_div hx0.ne' hq0.ne',
      Real.log_div (sub_pos.mpr hxlt1).ne' (sub_pos.mpr hq1).ne']
    ring

lemma dBern_ne_top_of_reference_interior {x q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    dBern x q ≠ ⊤ := by
  unfold dBern
  exact klDiv_ne_top
    (bernoulliLaw_ac_of_reference_interior hq0 hq1)
    bernoulliLaw_llr_integrable

lemma dBern_toReal_eq_bernoulliCrossKL {x q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hqx : q ≤ x) (hx1 : x ≤ 1) :
    (dBern x q).toReal = bernoulliCrossKL x q := by
  have hx0 : 0 ≤ x := hq0.le.trans hqx
  unfold dBern
  rw [bernoulliLaw_klDiv_toReal hx0 hx1 hq0 hq1]
  exact (bernoulliCrossKL_eq_closedForm hq0 hq1 hqx hx1).symm

theorem dBern_mono_active {p r q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (hqp : q ≤ p) (hpr : p ≤ r) (hr1 : r ≤ 1) :
    dBern p q ≤ dBern r q := by
  have hp1 : p ≤ 1 := hpr.trans hr1
  have hqr : q ≤ r := hqp.trans hpr
  have hp_mem : p ∈ Icc q 1 := ⟨hqp, hp1⟩
  have hr_mem : r ∈ Icc q 1 := ⟨hqr, hr1⟩
  have hcross : bernoulliCrossKL p q ≤ bernoulliCrossKL r q := by
    rcases hpr.eq_or_lt with hEq | hLt
    · subst r
      exact le_rfl
    · exact (bernoulliCrossKL_strictMonoOn hq0 hq1 hp_mem hr_mem hLt).le
  apply (ENNReal.toReal_le_toReal
    (dBern_ne_top_of_reference_interior hq0 hq1)
    (dBern_ne_top_of_reference_interior hq0 hq1)).mp
  rw [dBern_toReal_eq_bernoulliCrossKL hq0 hq1 hqp hp1,
    dBern_toReal_eq_bernoulliCrossKL hq0 hq1 hqr hr1]
  exact hcross

end

end UEOT.V3.BernoulliKLMonotone
