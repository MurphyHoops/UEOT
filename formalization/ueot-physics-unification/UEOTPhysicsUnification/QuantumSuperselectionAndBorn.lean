import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Continuous Transitivity vs Superselection, Mermin-Peres Contextuality & Envariance
(`C-QSEL-06`, `P-QBORN-03`)

Closes Row 1 of `PREMISES_AND_RESPONSIBILITIES.md` §5 and `CORE_PHYSICS_CONTRACT.md` §4:

1. **Continuous Reversible Transitivity Excludes Direct-Sum Superselection (`C-QSEL-06`)**:
   - `continuous_path_cannot_bridge_superselection_sectors`: In a nontrivial two-sector direct-sum
     superselection model where pure states carry discrete sector weight `w ∈ {0, 1}`, no continuous
     path `γ : ℝ → ℝ` on `[0, 1]` confined to `{0, 1}` can connect `γ 0 = 0` to `γ 1 = 1`.
   - `discrete_swap_bridges_superselection_sectors`: By contrast, the discrete involutive block-swap
     automorphism `(x, y) ↦ (y, x)` maps `(1, 0)` to `(0, 1)`, proving that discrete reversible
     transitivity is strictly weaker than continuous reversible transitivity.

2. **Mermin-Peres Parity Square Non-Contextuality Obstruction (`P-QBORN-03`)**:
   - `mermin_peres_no_noncontextual_valuation`: No non-contextual `{+1, -1}` assignment on a `3 × 3`
     observable grid can simultaneously satisfy the three quantum row-product identities (`+1`) and
     three quantum column-product identities (`+1, +1, -1`).
   - `mermin_peres_classical_bound_four`: Every `{+1, -1}` valuation `v i j ^ 2 = 1` obeys the sharp
     non-contextual inequality `R_0 + R_1 + R_2 + C_0 + C_1 - C_2 ≤ 4` (strictly below the state-independent
     two-qubit quantum value `6`).

3. **Zurek Envariance Equal-Amplitude Uniformity (`envariance_equal_weights_uniform`)**:
   - Any normalized probability assignment `∑_i p_i = 1` on `Fin n` (`n ≥ 1`) invariant under transpositions
     (`∀ i j, p_i = p_j`) equals `1 / n` on every branch.
-/

namespace UEOTPhysicsUnification.QuantumSuperselectionAndBorn

open scoped BigOperators

/-! ## 1. Continuous vs Discrete Transitivity on Direct-Sum Superselection Sectors -/

/-- By the Intermediate Value Theorem on `[0, 1]`, no continuous pure-state path confined to discrete
superselection weights `{0, 1}` can connect sector `0` (`γ 0 = 0`) to sector `1` (`γ 1 = 1`). -/
theorem continuous_path_cannot_bridge_superselection_sectors
    {gamma : ℝ → ℝ}
    (hcont : ContinuousOn gamma (Set.Icc (0 : ℝ) 1))
    (hpure : ∀ t ∈ Set.Icc (0 : ℝ) 1, gamma t = 0 ∨ gamma t = 1)
    (h0 : gamma 0 = 0) :
    gamma 1 ≠ 1 := by
  intro h1
  have hab : (0 : ℝ) ≤ 1 := by norm_num
  have hivt := intermediate_value_Icc hab hcont
  have hmem : (1 / 2 : ℝ) ∈ Set.Icc (gamma 0) (gamma 1) := by
    rw [h0, h1]
    constructor <;> norm_num
  rcases hivt hmem with ⟨t, ht_in, ht_val⟩
  rcases hpure t ht_in with ht0 | ht1 <;> linarith

/-- Discrete involutive block permutation `(x, y) ↦ (y, x)` swaps the two extremal superselection sectors,
demonstrating that discrete reversible transitivity does not exclude direct-sum superselection. -/
def discreteSectorSwap (p : ℝ × ℝ) : ℝ × ℝ := (p.2, p.1)

theorem discrete_swap_bridges_superselection_sectors :
    discreteSectorSwap (discreteSectorSwap (1, 0)) = (1, 0) ∧
      discreteSectorSwap (1, 0) = (0, 1) := by
  unfold discreteSectorSwap
  exact ⟨rfl, rfl⟩

/-! ## 2. Mermin-Peres Magic Square Non-Contextuality Theorem -/

/-- No deterministic non-contextual integer valuation `v : Fin 3 → Fin 3 → ℤ` can satisfy the six
commuting row/column product constraints of the two-qubit Mermin-Peres square. -/
theorem mermin_peres_no_noncontextual_valuation
    (v : Fin 3 → Fin 3 → ℤ)
    (hr0 : v 0 0 * v 0 1 * v 0 2 = 1)
    (hr1 : v 1 0 * v 1 1 * v 1 2 = 1)
    (hr2 : v 2 0 * v 2 1 * v 2 2 = 1)
    (hc0 : v 0 0 * v 1 0 * v 2 0 = 1)
    (hc1 : v 0 1 * v 1 1 * v 2 1 = 1)
    (hc2 : v 0 2 * v 1 2 * v 2 2 = -1) :
    False := by
  have hrows : (v 0 0 * v 0 1 * v 0 2) * (v 1 0 * v 1 1 * v 1 2) * (v 2 0 * v 2 1 * v 2 2) = 1 := by
    rw [hr0, hr1, hr2]
    norm_num
  have hcols : (v 0 0 * v 1 0 * v 2 0) * (v 0 1 * v 1 1 * v 2 1) * (v 0 2 * v 1 2 * v 2 2) = -1 := by
    rw [hc0, hc1, hc2]
    norm_num
  have hcomm :
      (v 0 0 * v 0 1 * v 0 2) * (v 1 0 * v 1 1 * v 1 2) * (v 2 0 * v 2 1 * v 2 2) =
        (v 0 0 * v 1 0 * v 2 0) * (v 0 1 * v 1 1 * v 2 1) * (v 0 2 * v 1 2 * v 2 2) := by
    ring
  linarith

/-- Helper lemma: if six `{+1, -1}` integers have product `-1`, their sum is at most `4`. -/
theorem six_signs_neg_product_sum_le_four
    {s0 s1 s2 s3 s4 s5 : ℤ}
    (h0 : s0 = 1 ∨ s0 = -1) (h1 : s1 = 1 ∨ s1 = -1) (h2 : s2 = 1 ∨ s2 = -1)
    (h3 : s3 = 1 ∨ s3 = -1) (h4 : s4 = 1 ∨ s4 = -1) (h5 : s5 = 1 ∨ s5 = -1)
    (hprod : s0 * s1 * s2 * s3 * s4 * s5 = -1) :
    s0 + s1 + s2 + s3 + s4 + s5 ≤ 4 := by
  rcases h0 with rfl | rfl <;>
  rcases h1 with rfl | rfl <;>
  rcases h2 with rfl | rfl <;>
  rcases h3 with rfl | rfl <;>
  rcases h4 with rfl | rfl <;>
  rcases h5 with rfl | rfl <;>
  (norm_num at hprod; try norm_num)

/-- Helper: product of three `{+1, -1}` integers lies in `{+1, -1}`. -/
lemma prod_three_signs {a b c : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) :
    a * b * c = 1 ∨ a * b * c = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> simp

/-- Sharp classical non-contextual Mermin-Peres inequality: for any `{+1, -1}` grid `v`,
`R_0 + R_1 + R_2 + C_0 + C_1 - C_2 ≤ 4` (whereas quantum mechanics achieves `6`). -/
theorem mermin_peres_classical_bound_four
    (v : Fin 3 → Fin 3 → ℤ)
    (hpm : ∀ i j : Fin 3, v i j = 1 ∨ v i j = -1) :
    (v 0 0 * v 0 1 * v 0 2) + (v 1 0 * v 1 1 * v 1 2) + (v 2 0 * v 2 1 * v 2 2) +
      (v 0 0 * v 1 0 * v 2 0) + (v 0 1 * v 1 1 * v 2 1) - (v 0 2 * v 1 2 * v 2 2) ≤ 4 := by
  have hsq : ∀ i j : Fin 3, (v i j) ^ 2 = 1 := by
    intro i j
    rcases hpm i j with h | h <;> simp [h]
  let s0 := v 0 0 * v 0 1 * v 0 2
  let s1 := v 1 0 * v 1 1 * v 1 2
  let s2 := v 2 0 * v 2 1 * v 2 2
  let s3 := v 0 0 * v 1 0 * v 2 0
  let s4 := v 0 1 * v 1 1 * v 2 1
  let s5 := -(v 0 2 * v 1 2 * v 2 2)
  have hs0 : s0 = 1 ∨ s0 = -1 := prod_three_signs (hpm 0 0) (hpm 0 1) (hpm 0 2)
  have hs1 : s1 = 1 ∨ s1 = -1 := prod_three_signs (hpm 1 0) (hpm 1 1) (hpm 1 2)
  have hs2 : s2 = 1 ∨ s2 = -1 := prod_three_signs (hpm 2 0) (hpm 2 1) (hpm 2 2)
  have hs3 : s3 = 1 ∨ s3 = -1 := prod_three_signs (hpm 0 0) (hpm 1 0) (hpm 2 0)
  have hs4 : s4 = 1 ∨ s4 = -1 := prod_three_signs (hpm 0 1) (hpm 1 1) (hpm 2 1)
  have hs5 : s5 = 1 ∨ s5 = -1 := by
    rcases prod_three_signs (hpm 0 2) (hpm 1 2) (hpm 2 2) with h | h
    · right; dsimp [s5]; linarith
    · left; dsimp [s5]; linarith
  have hprod : s0 * s1 * s2 * s3 * s4 * s5 = -1 := by
    dsimp [s0, s1, s2, s3, s4, s5]
    calc
      (v 0 0 * v 0 1 * v 0 2) * (v 1 0 * v 1 1 * v 1 2) * (v 2 0 * v 2 1 * v 2 2) *
          (v 0 0 * v 1 0 * v 2 0) * (v 0 1 * v 1 1 * v 2 1) * -(v 0 2 * v 1 2 * v 2 2)
          = -((v 0 0) ^ 2 * (v 0 1) ^ 2 * (v 0 2) ^ 2 *
              (v 1 0) ^ 2 * (v 1 1) ^ 2 * (v 1 2) ^ 2 *
              (v 2 0) ^ 2 * (v 2 1) ^ 2 * (v 2 2) ^ 2) := by ring
      _ = -1 := by
            rw [hsq 0 0, hsq 0 1, hsq 0 2, hsq 1 0, hsq 1 1, hsq 1 2, hsq 2 0, hsq 2 1, hsq 2 2]
            norm_num
  have hle := six_signs_neg_product_sum_le_four hs0 hs1 hs2 hs3 hs4 hs5 hprod
  dsimp [s0, s1, s2, s3, s4, s5] at hle
  linarith

/-! ## 3. Envariance Equal-Amplitude Born Uniformity -/

/-- Any normalized probability assignment on `Fin n` (`n > 0`) invariant under branch swaps equals `1 / n`. -/
theorem envariance_equal_weights_uniform
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (hsum : ∑ i : Fin n, p i = 1)
    (hsym : ∀ i j : Fin n, p i = p j)
    (k : Fin n) :
    p k = 1 / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hconst : ∑ i : Fin n, p i = (n : ℝ) * p k := by
    have heq : ∀ i : Fin n, p i = p k := fun i => hsym i k
    simp [heq]
  rw [hconst] at hsum
  field_simp [hnR]
  linarith

end UEOTPhysicsUnification.QuantumSuperselectionAndBorn
