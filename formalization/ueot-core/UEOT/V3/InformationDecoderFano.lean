import UEOT.V3.InformationSharpFano

/-!
# P-INFO-04 — decoder-index sharp Fano foundation

The frozen source uses the error indicator of an arbitrary decoder, not the
MAP decoder.  Therefore the correct pointwise entropy lemma fixes an arbitrary
candidate output `j0` and sets the conditional error to `1 - p j0`.

For every probability vector `p` on `Fin M` and every `j0`,

`H(p) ≤ h₂(1-p j0) + (1-p j0) log(M-1)`.

Applied to `j0 = Jhat(y)` for each observation `y`, this is exactly the
pointwise conditional-entropy form of the source error-indicator argument.
-/

namespace UEOT.V3.InformationDecoderFano

open scoped BigOperators
open UEOT.V3.InformationSharpFano

/-- Sharp Fano entropy bound relative to an arbitrary decoded index, rather
than the MAP index. -/
theorem sharp_discrete_fano_at_index
    {M : ℕ} (hM : 2 ≤ M) (p : Fin M → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (j0 : Fin M) :
    ∑ j, Real.negMulLog (p j) ≤
      Real.binEntropy (1 - p j0) +
        (1 - p j0) * Real.log ((M : ℝ) - 1) := by
  classical
  have hm1 : p j0 ≤ 1 := by
    rw [← hp1]
    exact Finset.single_le_sum (fun k _ => hp0 k) (Finset.mem_univ j0)
  have hsplit :
      ∑ j, Real.negMulLog (p j) =
        Real.negMulLog (p j0) +
          ∑ j ∈ Finset.univ.erase j0, Real.negMulLog (p j) := by
    exact (Finset.add_sum_erase Finset.univ
      (fun j => Real.negMulLog (p j)) (Finset.mem_univ j0)).symm
  have hSe : ∑ j ∈ Finset.univ.erase j0, p j = 1 - p j0 := by
    have h := Finset.add_sum_erase Finset.univ p (Finset.mem_univ j0)
    rw [hp1] at h
    linarith [h]
  have hcard : (Finset.univ.erase j0).card = M - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j0),
      Finset.card_univ, Fintype.card_fin]
  have hne : (Finset.univ.erase j0).Nonempty := by
    rw [← Finset.card_pos, hcard]
    omega
  have hsub := negMulLog_sum_le_card
    (Finset.univ.erase j0) p (fun i _ => hp0 i) hne
  rw [hSe, hcard] at hsub
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast] at hsub
  have hbin :
      Real.negMulLog (p j0) + Real.negMulLog (1 - p j0) =
        Real.binEntropy (1 - p j0) := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub (1 - p j0),
      show (1 : ℝ) - (1 - p j0) = p j0 from by ring]
    ring
  rw [hsplit]
  calc
    Real.negMulLog (p j0) +
        ∑ j ∈ Finset.univ.erase j0, Real.negMulLog (p j)
      ≤ Real.negMulLog (p j0) +
          (Real.negMulLog (1 - p j0) +
            (1 - p j0) * Real.log ((M : ℝ) - 1)) := by
        linarith [hsub]
    _ = Real.binEntropy (1 - p j0) +
        (1 - p j0) * Real.log ((M : ℝ) - 1) := by
      rw [← hbin]
      ring

end UEOT.V3.InformationDecoderFano
