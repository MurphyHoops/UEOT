import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# P-REC-02 foundation — continuous recovery differential inequality

The source theorem assumes a locally absolutely continuous expectation
m(t)=E[W(X_t)] with an almost-everywhere drift inequality coming from Dynkin's
formula.  This first layer proves the exact exponential bound under the
stronger pointwise right-derivative hypotheses accepted directly by Mathlib's
Gronwall theorem.  The AC/a.e.-derivative bridge remains a separate source
obligation and no P-ID promotion is claimed here.
-/

namespace UEOT.V3.RecoveryContinuous

open Set Real MeasureTheory

/-- Fundamental AC/a.e. comparison lemma needed by the exact source version:
an absolutely continuous scalar function whose derivative is nonpositive
almost everywhere cannot rise above its initial value. -/
theorem le_initial_of_ac_ae_deriv_nonpos
    (g : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T)
    (hg : AbsolutelyContinuousOnInterval g 0 T)
    (hderiv :
      ∀ᵐ t ∂MeasureTheory.volume.restrict (Icc 0 T),
        deriv g t ≤ 0) :
    ∀ t ∈ Icc 0 T, g t ≤ g 0 := by
  intro t ht
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    exact Icc_subset_Icc_right ht.2
  have hgt : AbsolutelyContinuousOnInterval g 0 t :=
    hg.mono hsub
  have hderiv_t :
      ∀ᵐ x ∂MeasureTheory.volume.restrict (Icc 0 t),
        deriv g x ≤ 0 := by
    exact hderiv.filter_mono
      (ae_mono (MeasureTheory.Measure.restrict_mono
        (Icc_subset_Icc_right ht.2) le_rfl))
  have hint :
      (∫ x in (0 : ℝ)..t, deriv g x) ≤
        ∫ x in (0 : ℝ)..t, (0 : ℝ) := by
    exact intervalIntegral.integral_mono_ae_restrict
      ht.1 hgt.intervalIntegrable_deriv intervalIntegrable_const hderiv_t
  have hftc := hgt.integral_deriv_eq_sub
  have hzero : (∫ _x in (0 : ℝ)..t, (0 : ℝ)) = 0 := by simp
  rw [hzero] at hint
  linarith

/-- Exact scalar Grönwall bridge at the source regularity: absolute
continuity plus an almost-everywhere differential inequality.  The proof uses
the integrating factor exp(a t), reducing the claim to the preceding
AC/a.e. monotonicity lemma. -/
theorem exponential_recovery_bound_ac_ae
    (m : ℝ → ℝ) (a b T : ℝ)
    (ha : 0 < a) (hT : 0 ≤ T)
    (hm : AbsolutelyContinuousOnInterval m 0 T)
    (hbound :
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        deriv m t ≤ -a * m t + b) :
    ∀ t ∈ Icc 0 T,
      m t ≤
        Real.exp (-a * t) * m 0 +
          (b / a) * (1 - Real.exp (-a * t)) := by
  let g : ℝ → ℝ := fun t =>
    Real.exp (a * t) * (m t - b / a)
  have hexpAC :
      AbsolutelyContinuousOnInterval (fun t : ℝ => Real.exp (a * t)) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hconstAC :
      AbsolutelyContinuousOnInterval (fun _t : ℝ => b / a) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hgAC : AbsolutelyContinuousOnInterval g 0 T := by
    exact hexpAC.mul (hm.sub hconstAC)
  have hmDiff :
      ∀ᵐ x ∂volume.restrict (Icc 0 T), DifferentiableAt ℝ m x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae hm.ae_differentiableAt] with x hx hxd
    exact hxd (by simpa [uIcc_of_le hT] using hx)
  have hgDeriv :
      ∀ᵐ x ∂volume.restrict (Icc 0 T), deriv g x ≤ 0 := by
    filter_upwards [hmDiff, hbound] with x hmd hmx
    have hexp :
        HasDerivAt (fun t : ℝ => Real.exp (a * t))
          (Real.exp (a * x) * a) x :=
      (hasDerivAt_const_mul a).exp
    have hmSub :
        HasDerivAt (fun t : ℝ => m t - b / a) (deriv m x) x :=
      hmd.hasDerivAt.sub_const (b / a)
    have hprod := hexp.mul hmSub
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hlin : a * (m x - b / a) = a * m x - b := by
      field_simp [ha0]
    have hinner : a * (m x - b / a) + deriv m x ≤ 0 := by
      rw [hlin]
      linarith
    have hform :
        deriv g x =
          Real.exp (a * x) *
            (a * (m x - b / a) + deriv m x) := by
      change
        deriv ((fun t : ℝ => Real.exp (a * t)) *
          (fun t : ℝ => m t - b / a)) x =
            Real.exp (a * x) *
              (a * (m x - b / a) + deriv m x)
      rw [hprod.deriv]
      ring
    rw [hform]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hinner
  have hmono := le_initial_of_ac_ae_deriv_nonpos g T hT hgAC hgDeriv
  intro t ht
  have hg := hmono t ht
  have hpos : 0 < Real.exp (a * t) := Real.exp_pos _
  have hdiv :
      m t - b / a ≤ (m 0 - b / a) / Real.exp (a * t) := by
    apply (le_div_iff₀ hpos).2
    simpa [g, mul_comm] using hg
  have hinv : (Real.exp (a * t))⁻¹ = Real.exp (-a * t) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  simp only [div_eq_mul_inv, hinv] at hdiv
  nlinarith
/-- Exact exponential recovery bound from the scalar differential inequality
m' <= -a m + b on a compact time interval. -/
theorem exponential_recovery_bound_core
    (m m' : ℝ → ℝ) (a b T : ℝ)
    (ha : 0 < a) (hT : 0 ≤ T)
    (hm : ContinuousOn m (Icc 0 T))
    (hm' : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt m (m' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 T,
      m' t ≤ -a * m t + b) :
    ∀ t ∈ Icc 0 T,
      m t ≤
        Real.exp (-a * t) * m 0 +
          (b / a) * (1 - Real.exp (-a * t)) := by
  intro t ht
  have hG :=
    le_gronwallBound_of_liminf_deriv_right_le
      (f := m) (f' := m')
      (δ := m 0) (K := -a) (ε := b)
      (a := 0) (b := T)
      hm
      (fun x hx r hr => (hm' x hx).liminf_right_slope_le hr)
      (le_rfl)
      (fun x hx => by simpa [neg_mul] using hbound x hx)
      t ht
  have hne : -a ≠ 0 := neg_ne_zero.mpr ha.ne'
  rw [gronwallBound_of_K_ne_0 hne] at hG
  have hraw :
      m t + (b / a) * (Real.exp (-a * t) - 1) ≤
        m 0 * Real.exp (-a * t) := by
    simpa [sub_zero, neg_mul, div_neg] using hG
  nlinarith [hraw]

/-- If a nonnegative energy dominates c times squared distance and c>0, any
upper bound on the energy immediately gives the corresponding mean-square
distance bound after division by c.  This is the deterministic algebraic
second half of P-REC-02. -/
theorem sqDistance_le_of_energy_bound
    {W d2 B c : ℝ}
    (hc : 0 < c)
    (hdom : c * d2 ≤ W)
    (hW : W ≤ B) :
    d2 ≤ B / c := by
  have h : c * d2 ≤ B := hdom.trans hW
  exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using h)

end UEOT.V3.RecoveryContinuous
