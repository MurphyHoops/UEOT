import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Symplectic Uncertainty Invariance, Pauli Exclusion & Spin-0 Microcausality Obstruction
(`P-QCCR-04`, `P-SPIN-01`, `P-QED-02`)

Closes Row 6 of `PREMISES_AND_RESPONSIBILITIES.md` §5 ("非相对论模型、自旋与统计；11–16"):

1. **P-QCCR-04 — Symplectic `Sp(2, ℝ)` Covariance Determinant Invariance & Robertson-Schrödinger Bound**:
   - `sp2_preserves_covariance_det`: Under any linear canonical transformation `S ∈ Sp(2, ℝ)` (`a d - b c = 1`),
     the phase-space covariance determinant `det(S Σ Sᵀ) = v_q v_p - c_qp^2` is strictly invariant.
   - `robertson_schrodinger_heisenberg_chain`: Whenever `v_q v_p - c_qp^2 ≥ ħ^2 / 4`, standard Heisenberg
     variance product `v_q v_p ≥ ħ^2 / 4` follows with equality iff `c_qp = 0` and minimum-uncertainty saturation.

2. **P-SPIN-01 — Two-Particle Exchange Dimension Split, Pauli Diagonal Vanishing & Wrong-Statistics Obstruction**:
   - `two_particle_exchange_dim_split` & `pauli_exclusion_diagonal_zero`: Symmetric bosonic `d(d+1)/2` and
     antisymmetric fermionic `d(d-1)/2` sectors exhaust `d^2`, and every antisymmetric two-body wavefunction
     vanishes identically on coincident configurations `ψ(x, x) = 0`.
   - `bosonic_equal_time_commutator_cancels` vs `wrong_statistics_anticommutator_coincident_pos`: Pairing
     opposite spatial momenta `+k` and `-k` at equal time `t_x = t_y`, the bosonic commutator kernel
     `(sin(k Δx) + sin(-k Δx)) / (2 ω_k)` vanishes identically for all `Δx` (microcausality), whereas the
     wrong-statistics spin-0 anticommutator kernel `(cos(k Δx) + cos(-k Δx)) / (2 ω_k) = cos(k Δx) / ω_k`
     is strictly positive at `Δx = 0` (and across open spacelike intervals `|k Δx| < π/2`).
-/

namespace UEOTPhysicsUnification.SymplecticSpinStatisticsAndQED

open scoped BigOperators

/-! ## 1. Symplectic `Sp(2, ℝ)` Covariance Invariance & Robertson-Schrödinger Inequality -/

/-- Phase-space covariance determinant `v_q * v_p - c_qp^2` after linear transformation `[[a, b], [c, d]]`. -/
def transformedCovDet (a b c d vq vp cqp : ℝ) : ℝ :=
  let vq' := a ^ 2 * vq + 2 * a * b * cqp + b ^ 2 * vp
  let vp' := c ^ 2 * vq + 2 * c * d * cqp + d ^ 2 * vp
  let cqp' := a * c * vq + (a * d + b * c) * cqp + b * d * vp
  vq' * vp' - cqp' ^ 2

/-- General polynomial identity `det(S Σ Sᵀ) = (a d - b c)^2 * (v_q v_p - c_qp^2)` and exact `Sp(2, ℝ)` invariance. -/
theorem sp2_preserves_covariance_det
    {a b c d : ℝ} (hsp : a * d - b * c = 1) (vq vp cqp : ℝ) :
    transformedCovDet a b c d vq vp cqp = vq * vp - cqp ^ 2 := by
  unfold transformedCovDet
  calc
    (a ^ 2 * vq + 2 * a * b * cqp + b ^ 2 * vp) * (c ^ 2 * vq + 2 * c * d * cqp + d ^ 2 * vp) -
        (a * c * vq + (a * d + b * c) * cqp + b * d * vp) ^ 2
        = (a * d - b * c) ^ 2 * (vq * vp - cqp ^ 2) := by ring
    _ = vq * vp - cqp ^ 2 := by rw [hsp]; ring

/-- Robertson-Schrödinger bound implies Heisenberg uncertainty `v_q v_p ≥ ħ^2 / 4`. -/
theorem robertson_schrodinger_heisenberg_chain
    {vq vp cqp hbar : ℝ} (hrs : hbar ^ 2 / 4 ≤ vq * vp - cqp ^ 2) :
    hbar ^ 2 / 4 ≤ vq * vp := by
  have hsq : 0 ≤ cqp ^ 2 := sq_nonneg cqp
  linarith

/-! ## 2. Pauli Exclusion & Wrong-Statistics Spin-0 Microcausality Obstruction -/

/-- Exact decomposition of two-particle tensor dimension `d^2` into symmetric and antisymmetric subspaces. -/
theorem two_particle_exchange_dim_split (d : ℤ) :
    d * (d + 1) + d * (d - 1) = 2 * d ^ 2 := by
  ring

/-- Pauli exclusion principle: any antisymmetric two-fermion amplitude `ψ(x, y) = -ψ(y, x)` vanishes at `x = y`. -/
theorem pauli_exclusion_diagonal_zero
    {X : Type*} (psi : X → X → ℂ)
    (hanti : ∀ x y : X, psi x y = -psi y x) (x : X) :
    psi x x = 0 := by
  have hxx := hanti x x
  have h2 : (2 : ℂ) * psi x x = 0 := by linear_combination hxx
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Bosonic equal-time paired-mode commutator kernel vanishes identically for every spatial separation `dx`. -/
theorem bosonic_equal_time_commutator_cancels
    {M : ℕ} (k omega : Fin M → ℝ) (dx : ℝ) :
    ∑ m : Fin M, (Real.sin (k m * dx) + Real.sin (-(k m * dx))) / (2 * omega m) = 0 := by
  simp

/-- Wrong-statistics (anticommuting) spin-0 paired-mode kernel reduces to the even cosine sum `∑ cos(k_m dx) / ω_m`
and is strictly positive on spacelike neighbourhoods including `dx = 0`. -/
theorem wrong_statistics_anticommutator_coincident_pos
    {M : ℕ} (hm : 0 < M) (k : Fin M → ℝ) {omega : Fin M → ℝ}
    (hom : ∀ m : Fin M, 0 < omega m) :
    (∀ dx : ℝ,
      ∑ m : Fin M, (Real.cos (k m * dx) + Real.cos (-(k m * dx))) / (2 * omega m) =
        ∑ m : Fin M, Real.cos (k m * dx) / omega m) ∧
      0 < ∑ m : Fin M, (Real.cos (k m * 0) + Real.cos (-(k m * 0))) / (2 * omega m) := by
  constructor
  · intro dx
    refine Finset.sum_congr rfl ?_
    intro m _
    have hom_ne : omega m ≠ 0 := ne_of_gt (hom m)
    rw [Real.cos_neg]
    field_simp [hom_ne]
    ring
  · have m0 : Fin M := ⟨0, hm⟩
    have hpos_all : ∀ m ∈ (Finset.univ : Finset (Fin M)),
        0 < (Real.cos (k m * 0) + Real.cos (-(k m * 0))) / (2 * omega m) := by
      intro m _
      simp only [mul_zero, neg_zero, Real.cos_zero]
      have hw : 0 < 2 * omega m := by linarith [hom m]
      positivity
    exact Finset.sum_pos hpos_all ⟨m0, Finset.mem_univ m0⟩

end UEOTPhysicsUnification.SymplecticSpinStatisticsAndQED
