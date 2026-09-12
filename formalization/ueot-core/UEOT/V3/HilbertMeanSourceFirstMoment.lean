import UEOT.V3.HilbertMeanFirstMoment
import Mathlib.Tactic

/-!
# P-STAT-06 — source first-moment bridge

This module connects the generic centered-Hilbert first-moment estimate to the
canonical product-law source statistic.  The first deterministic bridge records
that centering every sample coordinate by the common mean commutes exactly with
the empirical mean.
-/

namespace UEOT.V3.HilbertMeanSourceFirstMoment

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanFirstMoment

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Centering each coordinate by a common Hilbert mean commutes exactly with
finite empirical averaging. -/
theorem empiricalMean_centered_eq_sub
    {N : ℕ} (hN : 0 < N) (ω : Fin N → H) (μH : H) :
    empiricalMean (fun i => ω i - μH) = empiricalMean ω - μH := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold empiricalMean
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [smul_sub]
  rw [← Nat.cast_smul_eq_nsmul ℝ N μH]
  rw [smul_smul]
  have hscale : ((N : ℝ)⁻¹ * (N : ℝ)) = 1 := by
    field_simp [hNreal]
  rw [hscale, one_smul]

end UEOT.V3.HilbertMeanSourceFirstMoment
