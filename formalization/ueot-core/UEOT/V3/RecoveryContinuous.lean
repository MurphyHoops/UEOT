import Mathlib.Analysis.ODE.Gronwall
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

open Set Real

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
  simpa [sub_zero, neg_mul, div_neg] using hG

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
