import UEOT.V3.PredictableOLS
import Mathlib.Tactic

/-!
# P-INV-05 — source time / finite-sample index bridge

The source theorem is naturally indexed by times `1, ..., N`, while the
finite-dimensional OLS algebra uses `Fin N`. This module makes that change of
index explicit and proves that the finite OLS score is exactly the shifted
source-time score used by the martingale concentration layer.
-/

namespace UEOT.V3.PredictableOLSSourceIndex

open UEOT.V3.PredictableOLS
open scoped BigOperators

universe uΩ

/-- Restrict a source-time design to the first `N` observations, with `Fin N`
index `t` representing source time `t+1`. -/
def finDesign {Ω : Type uΩ} {N d : ℕ}
    (phi : ℕ → Ω → Fin d → ℝ) (ω : Ω) : Fin N → Fin d → ℝ :=
  fun t j => phi (t.1 + 1) ω j

/-- Restrict source-time noise to the first `N` observations. -/
def finNoise {Ω : Type uΩ} {N : ℕ}
    (xi : ℕ → Ω → ℝ) (ω : Ω) : Fin N → ℝ :=
  fun t => xi (t.1 + 1) ω

/-- The `Fin N` OLS score is exactly the shifted source-time range sum. -/
theorem scoreVector_finSource_eq_range
    {Ω : Type uΩ} {N d : ℕ}
    (phi : ℕ → Ω → Fin d → ℝ)
    (xi : ℕ → Ω → ℝ)
    (ω : Ω) (j : Fin d) :
    scoreVector (finDesign (N := N) phi ω) (finNoise (N := N) xi ω) j =
      ∑ t ∈ Finset.range N, phi (t + 1) ω j * xi (t + 1) ω := by
  unfold scoreVector finDesign finNoise
  simpa using
    (Fin.sum_univ_eq_sum_range
      (fun t : ℕ => phi (t + 1) ω j * xi (t + 1) ω))

end UEOT.V3.PredictableOLSSourceIndex
