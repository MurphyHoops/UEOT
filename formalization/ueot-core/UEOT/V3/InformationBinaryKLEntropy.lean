import UEOT.V3.InformationFin2KL
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.Ring

/-!
# Binary KL / entropy algebra

This module isolates the scalar algebra behind the finite-binary
mutual-information identity.  For an interior reference probability `q`, the
binary KL scalar is binary entropy plus a cross-entropy term.  Boundary values
of the source probability `p` are included explicitly.
-/

namespace UEOT.V3.InformationBinaryKLEntropy

/-- Scalar Bernoulli KL written as negative binary entropy plus cross entropy.
The reference probability is interior; the source probability may be `0` or
`1`. -/
theorem binaryKLScalar_eq_negEntropy_cross
    (p q : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    p * Real.log (p / q) +
        (1 - p) * Real.log ((1 - p) / (1 - q)) =
      -Real.binEntropy p - p * Real.log q -
        (1 - p) * Real.log (1 - q) := by
  by_cases hpz : p = 0
  · subst p
    simp [Real.binEntropy, Real.log_inv]
  · by_cases hpo : p = 1
    · subst p
      simp [Real.binEntropy, Real.log_inv]
    · have hp0' : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
      have hp1' : p < 1 := lt_of_le_of_ne hp1 hpo
      have hpnz : p ≠ 0 := hpz
      have h1pnz : 1 - p ≠ 0 := sub_ne_zero.mpr hpo.symm
      have hqnz : q ≠ 0 := ne_of_gt hq0
      have h1qnz : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
      rw [Real.log_div hpnz hqnz, Real.log_div h1pnz h1qnz]
      rw [Real.binEntropy, Real.log_inv, Real.log_inv]
      ring

end UEOT.V3.InformationBinaryKLEntropy
