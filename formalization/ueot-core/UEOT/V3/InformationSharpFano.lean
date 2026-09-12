import UEOT.V3.InformationEntropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

/-!
# P-INFO-04 foundation — sharp pointwise Fano entropy inequality

The frozen P-INFO-04 target needs the sharp term

`h₂(e) + e * log (K - 1)`

rather than the commonly formalized relaxation `log 2 + e * log K`.

This module exposes the sharp finite-distribution inequality that is already
present as an intermediate step inside the Apache-2.0 StatLean proof of its
(looser) public Fano theorem:
`StatLean/Minimaxity/Fano/FanoLowerBound.lean` (StatLean, 2026).

We port only the reusable entropy lemmas needed by UEOT.  The later
conditional/error-indicator bridge to the frozen decoder statement remains a
separate obligation.
-/

namespace UEOT.V3.InformationSharpFano

open scoped BigOperators

/-- Entropy bound for a nonnegative finite sub-probability vector. -/
theorem negMulLog_sum_le_card {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hs : s.Nonempty) :
    ∑ i ∈ s, Real.negMulLog (p i)
      ≤ Real.negMulLog (∑ i ∈ s, p i) +
        (∑ i ∈ s, p i) * Real.log (s.card) := by
  classical
  have hNpos : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hNne : (s.card : ℝ) ≠ 0 := ne_of_gt hNpos
  set S := ∑ i ∈ s, p i with hS
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := s) (w := fun _ => 1 / (s.card : ℝ)) (p := p)
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun i hi => hp i hi)
  have hsum_w :
      ∑ i ∈ s, (1 / (s.card : ℝ)) • p i =
        (1 / (s.card : ℝ)) * S := by
    simp only [smul_eq_mul, ← Finset.mul_sum, ← hS]
  have hsum_L :
      ∑ i ∈ s, (1 / (s.card : ℝ)) • Real.negMulLog (p i) =
        (1 / (s.card : ℝ)) * ∑ i ∈ s, Real.negMulLog (p i) := by
    simp only [smul_eq_mul, ← Finset.mul_sum]
  rw [hsum_w, hsum_L] at hjensen
  have key :
      ∑ i ∈ s, Real.negMulLog (p i)
        ≤ (s.card : ℝ) * Real.negMulLog ((1 / (s.card : ℝ)) * S) := by
    have h2 := mul_le_mul_of_nonneg_left hjensen hNpos.le
    rwa [← mul_assoc, mul_one_div, div_self hNne, one_mul] at h2
  refine le_trans key (le_of_eq ?_)
  rcases eq_or_lt_of_le
      (Finset.sum_nonneg (fun i hi => hp i hi) : (0 : ℝ) ≤ S) with hS0 | hS0
  · rw [show S = 0 from hS0.symm]
    simp [Real.negMulLog_def]
  · have hNne' : (1 : ℝ) / (s.card : ℝ) ≠ 0 := by positivity
    simp only [Real.negMulLog_def]
    rw [Real.log_mul hNne' (ne_of_gt hS0), one_div, Real.log_inv]
    field_simp
    ring

/-- **Sharp pointwise Fano inequality.**

For a probability vector `p` on `Fin M`, let
`e = 1 - max_j p_j`.  Then

`H(p) ≤ h₂(e) + e * log(M - 1)`.

This is the sharp intermediate inequality in the classical Fano proof; no
`h₂(e) ≤ log 2` or `log(M-1) ≤ log M` relaxation is performed here. -/
theorem sharp_discrete_fano_pointwise
    {M : ℕ} (hM : 2 ≤ M) (p : Fin M → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) :
    ∑ j, Real.negMulLog (p j) ≤
      Real.binEntropy (1 - ⨆ j, p j) +
        (1 - ⨆ j, p j) * Real.log ((M : ℝ) - 1) := by
  classical
  haveI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  obtain ⟨js, hjs⟩ := Finite.exists_max p
  have hbdd : BddAbove (Set.range p) :=
    Set.Finite.bddAbove (Set.finite_range p)
  have hsup : (⨆ j, p j) = p js :=
    le_antisymm (ciSup_le hjs) (le_ciSup hbdd js)
  rw [hsup]
  set m := p js with hm
  have hm1 : m ≤ 1 := by
    rw [hm, ← hp1]
    exact Finset.single_le_sum (fun k _ => hp0 k) (Finset.mem_univ js)
  have hsplit :
      ∑ j, Real.negMulLog (p j) =
        Real.negMulLog m +
          ∑ j ∈ Finset.univ.erase js, Real.negMulLog (p j) := by
    rw [hm]
    exact (Finset.add_sum_erase Finset.univ (fun j => Real.negMulLog (p j))
      (Finset.mem_univ js)).symm
  have hSe : ∑ j ∈ Finset.univ.erase js, p j = 1 - m := by
    have h := Finset.add_sum_erase Finset.univ p (Finset.mem_univ js)
    rw [hp1] at h
    rw [hm]
    linarith [h]
  have hcard : (Finset.univ.erase js).card = M - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ js),
      Finset.card_univ, Fintype.card_fin]
  have hne : (Finset.univ.erase js).Nonempty := by
    rw [← Finset.card_pos, hcard]
    omega
  have hsub := negMulLog_sum_le_card
    (Finset.univ.erase js) p (fun i _ => hp0 i) hne
  rw [hSe, hcard] at hsub
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast] at hsub
  have hbin :
      Real.negMulLog m + Real.negMulLog (1 - m) =
        Real.binEntropy (1 - m) := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub (1 - m),
      show (1 : ℝ) - (1 - m) = m from by ring]
    ring
  rw [hsplit]
  calc
    Real.negMulLog m +
        ∑ j ∈ Finset.univ.erase js, Real.negMulLog (p j)
      ≤ Real.negMulLog m +
          (Real.negMulLog (1 - m) +
            (1 - m) * Real.log ((M : ℝ) - 1)) := by
        linarith [hsub]
    _ = Real.binEntropy (1 - m) +
        (1 - m) * Real.log ((M : ℝ) - 1) := by
      rw [← hbin]
      ring

end UEOT.V3.InformationSharpFano
