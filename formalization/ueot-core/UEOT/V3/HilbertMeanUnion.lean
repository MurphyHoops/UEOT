import UEOT.V3.HilbertMeanAzuma
import Mathlib.Tactic

/-!
# P-STAT-06 — finite simultaneous union layer

This module isolates the final probability-combination step used by the frozen
P-STAT-06 theorem.  Once each of `L` RKHS error statistics has failure
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
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (h_each : ∀ j, μ.real (bad j) ≤ alpha / (L : ℝ)) :
    μ.real (⋃ j : Fin L, bad j) ≤ alpha := by
  calc
    μ.real (⋃ j : Fin L, bad j)
        ≤ ∑ j : Fin L, μ.real (bad j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin L, alpha / (L : ℝ) := by
      exact Finset.sum_le_sum fun j _ => h_each j
    _ = alpha := by
      have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp [ne_of_gt hLreal]

/-- Pointwise good-event form of the same finite union principle. -/
theorem measure_forall_good_ge_one_sub_alpha
    {L : ℕ} (hL : 0 < L)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (good : Fin L → Set Ω)
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (h_each : ∀ j, μ.real ((good j)ᶜ) ≤ alpha / (L : ℝ)) :
    1 - alpha ≤ μ.real (⋂ j : Fin L, good j) := by
  have hbad := measure_exists_bad_le_alpha hL μ (fun j => (good j)ᶜ)
    alpha halpha h_each
  have hcompl : (⋂ j : Fin L, good j)ᶜ = ⋃ j : Fin L, (good j)ᶜ := by
    ext ω
    simp
  have hprob : μ.real (⋂ j : Fin L, good j) = 1 - μ.real ((⋂ j : Fin L, good j)ᶜ) := by
    rw [measureReal_compl]
    · simp
    · exact measurableSet_iInter fun j => by
        classical
        exact MeasurableSet.compl (by
          simpa only [Set.compl_compl] using measurableSet_compl_iff.mp
            (measurableSet_compl_iff.mpr (by infer_instance)))
  rw [hprob, hcompl]
  linarith

end UEOT.V3.HilbertMeanUnion
