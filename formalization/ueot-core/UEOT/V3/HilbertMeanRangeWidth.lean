import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# P-STAT-06 — bounded oscillation gives a narrow centered range

A McDiarmid/Doob increment is a continuation value minus its conditional
average.  The key deterministic fact is that subtracting the same center does
not enlarge the range.  This file packages the order-theoretic part without
assuming that the infimum or supremum is attained.
-/

namespace UEOT.V3.HilbertMeanRangeWidth

open Set Real

universe uα

variable {α : Type uα}

/-- Pairwise oscillation by at most `c` makes the range bounded above. -/
theorem bddAbove_range_of_pairwise_abs_sub_le
    [Nonempty α] (q : α → ℝ) {c : ℝ}
    (hosc : ∀ x y, |q x - q y| ≤ c) :
    BddAbove (Set.range q) := by
  classical
  let x₀ : α := Classical.choice (inferInstance : Nonempty α)
  refine ⟨q x₀ + c, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : q x - q x₀ ≤ c := (abs_le.mp (hosc x x₀)).2
  linarith

/-- Pairwise oscillation by at most `c` makes the range bounded below. -/
theorem bddBelow_range_of_pairwise_abs_sub_le
    [Nonempty α] (q : α → ℝ) {c : ℝ}
    (hosc : ∀ x y, |q x - q y| ≤ c) :
    BddBelow (Set.range q) := by
  classical
  let x₀ : α := Classical.choice (inferInstance : Nonempty α)
  refine ⟨q x₀ - c, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : -c ≤ q x - q x₀ := (abs_le.mp (hosc x x₀)).1
  linarith

/-- A pointwise pairwise oscillation bound controls the exact `sSup-sInf`
width of the range, without requiring extrema to be attained. -/
theorem sSup_sub_sInf_range_le
    [Nonempty α] (q : α → ℝ) {c : ℝ}
    (hosc : ∀ x y, |q x - q y| ≤ c) :
    sSup (Set.range q) - sInf (Set.range q) ≤ c := by
  have hnon : (Set.range q).Nonempty := Set.range_nonempty q
  have hsup : sSup (Set.range q) ≤ sInf (Set.range q) + c := by
    apply csSup_le hnon
    intro z hz
    rcases hz with ⟨x, rfl⟩
    have hlower : q x - c ≤ sInf (Set.range q) := by
      apply le_csInf hnon
      intro z hz
      rcases hz with ⟨y, rfl⟩
      have hxy : q x - q y ≤ c := (abs_le.mp (hosc x y)).2
      linarith
    linarith
  linarith

/-- Every centered value lies between the centered infimum and supremum of the
uncentered continuation-value range. -/
theorem centered_mem_Icc_sInf_sSup
    [Nonempty α] (q : α → ℝ) {c m : ℝ}
    (hosc : ∀ x y, |q x - q y| ≤ c) (x : α) :
    q x - m ∈ Set.Icc
      (sInf (Set.range q) - m)
      (sSup (Set.range q) - m) := by
  have hbelow := bddBelow_range_of_pairwise_abs_sub_le q hosc
  have habove := bddAbove_range_of_pairwise_abs_sub_le q hosc
  constructor
  · have hx := csInf_le hbelow (Set.mem_range_self x)
    linarith
  · have hx := le_csSup habove (Set.mem_range_self x)
    linarith

/-- Centering leaves the interval width unchanged, so the same `c` controls the
Doob-increment support interval. -/
theorem centered_interval_width_le
    [Nonempty α] (q : α → ℝ) {c m : ℝ}
    (hosc : ∀ x y, |q x - q y| ≤ c) :
    (sSup (Set.range q) - m) - (sInf (Set.range q) - m) ≤ c := by
  have h := sSup_sub_sInf_range_le q hosc
  linarith

end UEOT.V3.HilbertMeanRangeWidth
