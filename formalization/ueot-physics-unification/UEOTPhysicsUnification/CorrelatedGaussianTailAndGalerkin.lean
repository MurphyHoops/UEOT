import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Galerkin Boundary-Flux Duhamel Telescoping & Correlated Two-Mode Gaussian Tail Bounds
(`P-MICRO-06B`, `P-MICRO-11`)

Extends pure-kernel Lean 4 formalization to Chapters 69–71 (`PREMISES_AND_RESPONSIBILITIES.md` §5 Rows 4–5):

1. **P-MICRO-06B — Exact Multi-Step Galerkin Boundary-Flux Duhamel Identity (`galerkin_telescoping_defect`)**:
   For any noncommutative operator/matrix ring `R` with full step `U`, truncated step `U_K`, and embedding `J`,
   `U^N * J - J * U_K^N = ∑_{m ∈ range N} U^(N - 1 - m) * (U * J - J * U_K) * U_K^m`.
   This provides the exact algebraic core of Chapter 69's simultaneous-cutoff boundary-flux bound.

2. **P-MICRO-11 — Exact Bose-Einstein Geometric Partial Sum & Correlated Two-Mode Fock Tail Bound**:
   - `bose_geometric_partial_sum`: For any thermal occupation `nbar ≥ 0`, the exact Bose-Einstein geometric
     law `p_m = (1 / (nbar + 1)) * (nbar / (nbar + 1))^m` sums over `0 ≤ m ≤ K` to
     `1 - (nbar / (nbar + 1))^(K + 1)`.
   - `correlated_two_mode_fock_tail_bound`: In Chapter 71's zero-mean gauge-invariant correlated two-mode
     Gaussian bath (`N_11 = N_22 = n`, `N_12 = c`, `|c| ≤ n`), diagonalizing into normal occupations
     `n_+ = n + c ≥ 0` and `n_- = n - c ≥ 0` bounds the Fock truncation leakage outside `{0..K}^2` by
     `((n + c) / (n + c + 1))^(K + 1) + ((n - c) / (n - c + 1))^(K + 1)`.
-/

namespace UEOTPhysicsUnification.CorrelatedGaussianTailAndGalerkin

open scoped BigOperators

/-! ## 1. Discrete Duhamel Galerkin Boundary-Flux Telescoping Identity -/

/-- Exact noncommutative Duhamel telescoping identity for projected Galerkin evolution over `N` steps. -/
theorem galerkin_telescoping_defect
    {R : Type*} [Ring R] (U UK J : R) (N : ℕ) :
    U ^ N * J - J * UK ^ N =
      ∑ m ∈ Finset.range N, U ^ (N - 1 - m) * (U * J - J * UK) * UK ^ m := by
  induction N with
  | zero =>
    simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hidx : ∀ m ∈ Finset.range k, k - m = k - 1 - m + 1 := by
      intro m hm
      have hlt : m < k := Finset.mem_range.mp hm
      omega
    have hsum_shift :
        (∑ m ∈ Finset.range k, U ^ (k - m) * (U * J - J * UK) * UK ^ m) =
          U * ∑ m ∈ Finset.range k, U ^ (k - 1 - m) * (U * J - J * UK) * UK ^ m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m hm
      rw [hidx m hm, pow_succ']
      noncomm_ring
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    rw [hsum_shift, ← ih, pow_succ' U k, pow_succ' UK k]
    noncomm_ring

/-! ## 2. Exact Bose-Einstein Geometric Partial Sum & Two-Mode Correlated Tail Bound -/

/-- Exact Bose-Einstein geometric occupation weight `(1 / (nbar + 1)) * (nbar / (nbar + 1))^m`. -/
noncomputable def boseWeight (nbar : ℝ) (m : ℕ) : ℝ :=
  (1 / (nbar + 1)) * (nbar / (nbar + 1)) ^ m

/-- Exact closed-form partial sum of the Bose-Einstein occupation law through cutoff `K`. -/
theorem bose_geometric_partial_sum {nbar : ℝ} (hn : 0 ≤ nbar) (K : ℕ) :
    ∑ m ∈ Finset.range (K + 1), boseWeight nbar m =
      1 - (nbar / (nbar + 1)) ^ (K + 1) := by
  have hden : nbar + 1 ≠ 0 := by linarith
  have hcomp : 1 - 1 / (nbar + 1) = nbar / (nbar + 1) := by
    field_simp [hden]
    ring
  induction K with
  | zero =>
    simp [boseWeight]
    field_simp [hden]
    ring
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold boseWeight
    calc
      1 - (nbar / (nbar + 1)) ^ (k + 1) + 1 / (nbar + 1) * (nbar / (nbar + 1)) ^ (k + 1)
          = 1 - (1 - 1 / (nbar + 1)) * (nbar / (nbar + 1)) ^ (k + 1) := by ring
      _ = 1 - (nbar / (nbar + 1)) * (nbar / (nbar + 1)) ^ (k + 1) := by rw [hcomp]
      _ = 1 - (nbar / (nbar + 1)) ^ (k + 1 + 1) := by rw [← pow_succ']

/-- Product union-bound lemma: for `a, b ∈ [0, 1]`, `1 - (1 - a)(1 - b) = a + b - a b ≤ a + b`. -/
theorem two_mode_box_leakage_le_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 - (1 - a) * (1 - b) ≤ a + b ∧ 0 ≤ 1 - (1 - a) * (1 - b) - (a + b - a * b) := by
  constructor
  · have hab : 0 ≤ a * b := mul_nonneg ha hb
    nlinarith
  · ring_nf
    exact le_rfl

/-- Exact Chapter 71 correlated two-mode normal-basis Fock truncation tail bound (`P-MICRO-11`):
for `0 ≤ n` and `|c| ≤ n`, normal-mode occupations `n + c ≥ 0` and `n - c ≥ 0` have retained mass on
`{0..K} × {0..K}` within `((n+c)/(n+c+1))^(K+1) + ((n-c)/(n-c+1))^(K+1)` of unity. -/
theorem correlated_two_mode_fock_tail_bound
    {n c : ℝ} (hc_abs : |c| ≤ n) (K : ℕ) :
    let np := n + c
    let nm := n - c
    let tailP := (np / (np + 1)) ^ (K + 1)
    let tailM := (nm / (nm + 1)) ^ (K + 1)
    0 ≤ np ∧ 0 ≤ nm ∧
      1 - (∑ m1 ∈ Finset.range (K + 1), boseWeight np m1) *
            (∑ m2 ∈ Finset.range (K + 1), boseWeight nm m2) ≤
        tailP + tailM := by
  intro np nm tailP tailM
  have hc_bounds := abs_le.mp hc_abs
  have hnp : 0 ≤ np := by dsimp [np]; linarith
  have hnm : 0 ≤ nm := by dsimp [nm]; linarith
  have htp : 0 ≤ tailP := by
    dsimp [tailP]
    have hdiv : 0 ≤ np / (np + 1) := div_nonneg hnp (by linarith)
    exact pow_nonneg hdiv (K + 1)
  have htm : 0 ≤ tailM := by
    dsimp [tailM]
    have hdiv : 0 ≤ nm / (nm + 1) := div_nonneg hnm (by linarith)
    exact pow_nonneg hdiv (K + 1)
  refine ⟨hnp, hnm, ?_⟩
  rw [bose_geometric_partial_sum hnp K, bose_geometric_partial_sum hnm K]
  exact (two_mode_box_leakage_le_sum htp htm).1

end UEOTPhysicsUnification.CorrelatedGaussianTailAndGalerkin
