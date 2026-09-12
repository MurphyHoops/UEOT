import UEOT.V3.HilbertMeanUnion
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# P-STAT-06 — exact simultaneous deviation inversion

For the scalar tail `exp (-N t² / 2)`, the frozen simultaneous theorem chooses
`t = sqrt (2 log (L/alpha) / N)`. This module proves exactly that the finite
union prefactor reduces to `alpha`.
-/

namespace UEOT.V3.HilbertMeanRadius

open Real

/-- Deviation term used in frozen P-STAT-06 before adding the first-moment
`1/sqrt N` contribution. -/
noncomputable def pStat06Deviation (N L : ℕ) (alpha : ℝ) : ℝ :=
  sqrt (2 * log ((L : ℝ) / alpha) / (N : ℝ))

/-- Exact inversion of the P-STAT-06 scalar Azuma tail under a finite `L` union
bound: `L * exp (-N t²/2) = alpha`. -/
theorem raw_union_tail_eq_alpha
    {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    (L : ℝ) * exp
      (-(N : ℝ) * (pStat06Deviation N L alpha) ^ 2 / 2) = alpha := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLoneNat : 1 ≤ L := Nat.succ_le_iff.mpr hL
  have hLone : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLoneNat
  have hratio_pos : 0 < (L : ℝ) / alpha := div_pos hLreal halpha0
  have hratio_one : 1 ≤ (L : ℝ) / alpha := by
    rw [le_div_iff₀ halpha0]
    simpa using halpha1.trans hLone
  have hlog : 0 ≤ log ((L : ℝ) / alpha) := Real.log_nonneg hratio_one
  have hrad : 0 ≤ 2 * log ((L : ℝ) / alpha) / (N : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num) hlog) hNreal.le
  have hexponent :
      -(N : ℝ) * (pStat06Deviation N L alpha) ^ 2 / 2 =
        -log ((L : ℝ) / alpha) := by
    unfold pStat06Deviation
    rw [Real.sq_sqrt hrad]
    field_simp [ne_of_gt hNreal]
  rw [hexponent, Real.exp_neg, Real.exp_log hratio_pos]
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLreal
  have halphane : alpha ≠ 0 := ne_of_gt halpha0
  field_simp [hLne, halphane]

/-- The same inversion in per-channel form. -/
theorem scalar_tail_eq_alpha_div
    {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    exp (-(N : ℝ) * (pStat06Deviation N L alpha) ^ 2 / 2) =
      alpha / (L : ℝ) := by
  have h := raw_union_tail_eq_alpha hN hL halpha0 halpha1
  have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  rw [eq_div_iff (ne_of_gt hLreal)]
  simpa [mul_comm] using h

end UEOT.V3.HilbertMeanRadius
