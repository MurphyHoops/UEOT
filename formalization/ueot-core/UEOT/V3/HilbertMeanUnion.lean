import UEOT.V3.HilbertMeanAzuma
import Mathlib.Tactic

/-!
# P-STAT-06 — finite simultaneous union layer

This module isolates the final probability-combination step used by the frozen
P-STAT-06 theorem. Once each of `L` RKHS error statistics has failure
probability at most `alpha / L`, a finite union bound gives simultaneous control
with total failure probability at most `alpha`.

The remaining source-specific work is to instantiate the per-channel tail at
the exact radius `(1 + sqrt (2 * log (L / alpha))) / sqrt N` from the Hilbert
first-moment bound plus the Doob/Azuma layer.
-/

namespace UEOT.V3.HilbertMeanUnion

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω]

/-- Finite union wrapper in the exact `alpha / L` form needed by P-STAT-06. -/
theorem measure_exists_bad_le_alpha
    {L : ℕ} (hL : 0 < L)
    (μ : Measure Ω)
    (bad : Fin L → Set Ω)
    (alpha : ℝ)
    (h_each : ∀ j, μ.real (bad j) ≤ alpha / (L : ℝ)) :
    μ.real (⋃ j : Fin L, bad j) ≤ alpha := by
  calc
    μ.real (⋃ j : Fin L, bad j)
        ≤ ∑ j : Fin L, μ.real (bad j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin L, alpha / (L : ℝ) := by
      exact Finset.sum_le_sum fun j _ => h_each j
    _ = alpha := by
      have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      field_simp [ne_of_gt hLreal]

end UEOT.V3.HilbertMeanUnion
