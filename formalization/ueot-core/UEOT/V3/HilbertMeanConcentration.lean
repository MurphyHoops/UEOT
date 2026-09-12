import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# P-STAT-06 — Hilbert mean-embedding concentration infrastructure

The frozen source represents each response by a Bochner-integrable RKHS feature
with pointwise norm at most one.  Its McDiarmid step uses the fact that replacing
one of `N` samples changes the empirical-mean error statistic by at most `2/N`.

This module formalizes that deterministic Hilbert-space bounded-difference step
independently of the probabilistic McDiarmid layer.
-/

namespace UEOT.V3.HilbertMeanConcentration

open scoped BigOperators

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Arithmetic mean of a finite Hilbert-valued sample. -/
noncomputable def empiricalMean {N : ℕ} (x : Fin N → H) : H :=
  (N : ℝ)⁻¹ • ∑ i, x i

/-- Averages of unit-ball-valued Hilbert samples stay in the unit ball. -/
theorem norm_empiricalMean_le_one
    {N : ℕ} (hN : 0 < N)
    (x : Fin N → H) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ‖empiricalMean x‖ ≤ 1 := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hinv : 0 ≤ (N : ℝ)⁻¹ := (inv_nonneg.mpr hNreal.le)
  have hsum : ‖∑ i, x i‖ ≤ (N : ℝ) := by
    calc
      ‖∑ i, x i‖ ≤ ∑ i, ‖x i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => hx i
      _ = (N : ℝ) := by simp
  unfold empiricalMean
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNreal)]
  calc
    (N : ℝ)⁻¹ * ‖∑ i, x i‖ ≤ (N : ℝ)⁻¹ * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hsum hinv
    _ = 1 := by field_simp [ne_of_gt hNreal]

/-- If both the empirical mean and target mean are in the unit ball, the source
mean-error statistic is uniformly bounded by two. -/
theorem norm_empiricalMean_sub_le_two
    {N : ℕ} (hN : 0 < N)
    (x : Fin N → H) (hx : ∀ i, ‖x i‖ ≤ 1)
    (μ : H) (hμ : ‖μ‖ ≤ 1) :
    ‖empiricalMean x - μ‖ ≤ 2 := by
  calc
    ‖empiricalMean x - μ‖ ≤ ‖empiricalMean x‖ + ‖μ‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_empiricalMean_le_one hN x hx) hμ
    _ = 2 := by norm_num

/-- If two samples differ in at most one coordinate, the difference of their
empirical means is exactly the scaled difference at that coordinate. -/
theorem empiricalMean_sub_of_eq_off
    {N : ℕ} (x y : Fin N → H) (i : Fin N)
    (hsame : ∀ j, j ≠ i → x j = y j) :
    empiricalMean x - empiricalMean y =
      (N : ℝ)⁻¹ • (x i - y i) := by
  classical
  have hxsum :
      (∑ j, x j) = (∑ j ∈ (Finset.univ.erase i), x j) + x i := by
    symm
    exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have hysum :
      (∑ j, y j) = (∑ j ∈ (Finset.univ.erase i), y j) + y i := by
    symm
    exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have herase :
      (∑ j ∈ (Finset.univ.erase i), x j) =
        ∑ j ∈ (Finset.univ.erase i), y j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hsame j (Finset.ne_of_mem_erase hj)
  unfold empiricalMean
  rw [hxsum, hysum, herase]
  simp only [smul_add, smul_sub]
  abel

/-- Source McDiarmid sensitivity step: if both possible feature vectors have
norm at most one, changing one sample changes the empirical mean by at most
`2/N`. -/
theorem norm_empiricalMean_sub_le_two_div
    {N : ℕ} (hN : 0 < N)
    (x y : Fin N → H) (i : Fin N)
    (hsame : ∀ j, j ≠ i → x j = y j)
    (hxi : ‖x i‖ ≤ 1) (hyi : ‖y i‖ ≤ 1) :
    ‖empiricalMean x - empiricalMean y‖ ≤ 2 / (N : ℝ) := by
  rw [empiricalMean_sub_of_eq_off x y i hsame]
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hinv : 0 ≤ (N : ℝ)⁻¹ := (inv_nonneg.mpr hNreal.le)
  calc
    ‖(N : ℝ)⁻¹ • (x i - y i)‖
        = (N : ℝ)⁻¹ * ‖x i - y i‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNreal)]
    _ ≤ (N : ℝ)⁻¹ * (‖x i‖ + ‖y i‖) := by
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hinv
    _ ≤ (N : ℝ)⁻¹ * 2 := by
          gcongr
          linarith
    _ = 2 / (N : ℝ) := by
          field_simp [ne_of_gt hNreal]

/-- The norm-to-a-fixed-mean statistic inherits the same `2/N` bounded
difference constant from the reverse triangle inequality. -/
theorem abs_norm_sub_mean_diff_le_two_div
    {N : ℕ} (hN : 0 < N)
    (x y : Fin N → H) (i : Fin N)
    (hsame : ∀ j, j ≠ i → x j = y j)
    (hxi : ‖x i‖ ≤ 1) (hyi : ‖y i‖ ≤ 1)
    (μ : H) :
    |‖empiricalMean x - μ‖ - ‖empiricalMean y - μ‖| ≤ 2 / (N : ℝ) := by
  calc
    |‖empiricalMean x - μ‖ - ‖empiricalMean y - μ‖|
        ≤ ‖(empiricalMean x - μ) - (empiricalMean y - μ)‖ :=
          abs_norm_sub_norm_le _ _
    _ = ‖empiricalMean x - empiricalMean y‖ := by congr 1 <;> abel
    _ ≤ 2 / (N : ℝ) :=
      norm_empiricalMean_sub_le_two_div hN x y i hsame hxi hyi

end UEOT.V3.HilbertMeanConcentration
