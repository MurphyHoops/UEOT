import UEOTQM.QuantumPurification

/-!
# Complete convex purity in the finite complex density space

The converse is derived from a Gram decomposition of the actual positive
matrix. Neither a rank-one witness nor a restricted state space is assumed.
-/

namespace UEOTQM.QuantumPurification

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

universe u v
variable {ι : Type u} {α : Type v} [Fintype ι] [DecidableEq ι]
  [Fintype α] [DecidableEq α]

omit [Fintype ι] [DecidableEq ι] in
/-- Real scaling of a vector scales its positive outer product quadratically. -/
theorem outer_real_smul (r : ℝ) (v : ι → ℂ) :
    outer (r • v) = (r * r) • outer v := by
  ext i j
  simp [outer_apply]
  ring

omit [Fintype ι] [DecidableEq ι] [DecidableEq α] in
/-- A Gram matrix is the sum of the positive outer products of its columns. -/
theorem gram_eq_sum_outer (A : Matrix ι α ℂ) :
    A * Aᴴ = ∑ a, outer (fun i => A i a) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply]

omit [DecidableEq ι] in
/-- In an extreme density, every positive-mass positive summand has the same
normalized state. The zero remainder is handled without a fictitious posterior. -/
theorem IsPure.normalize_eq_of_positive_summand (ρ : Density ι) (hp : IsPure ρ)
    (X Y : Operator ι) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hsum : ρ.matrix = X + Y) (hx : 0 < mass X) : normalize X hX hx = ρ := by
  have hm : mass X + mass Y = 1 := by
    change X.trace.re + Y.trace.re = 1
    rw [← Complex.add_re, ← Matrix.trace_add, ← hsum, ρ.trace_one]
    rfl
  by_cases hy : mass Y = 0
  · have hY0 := (mass_eq_zero_iff hY).mp hy
    have hX1 : mass X = 1 := by linarith
    apply Density.ext
    simpa [normalize_matrix, hX1, hY0] using hsum.symm
  · have hypos : 0 < mass Y := lt_of_le_of_ne (mass_nonneg hY) (Ne.symm hy)
    have hx1 : mass X < 1 := by linarith
    apply (hp (normalize X hX hx) (normalize Y hY hypos) (mass X) hx hx1 ?_).1
    have hrem : 1 - mass X = mass Y := by linarith
    rw [normalize_matrix, normalize_matrix, hrem, smul_smul, smul_smul,
      mul_inv_cancel₀ hx.ne', mul_inv_cancel₀ hypos.ne', one_smul, one_smul]
    exact hsum

/-- Every extreme point of the entire finite complex density space has a
normalized vector representative, derived from its positive Gram columns. -/
theorem IsPure.exists_vector (ρ : Density ι) (hp : IsPure ρ) :
    ∃ v : ι → ℂ, (outer v).trace = 1 ∧ ρ.matrix = outer v := by
  obtain ⟨A, hA⟩ := exists_gram ρ
  let P : ι → Operator ι := fun a => outer (fun i => A i a)
  have hsum : ρ.matrix = ∑ a, P a := hA.trans (gram_eq_sum_outer A)
  have hmass : ∑ a, mass (P a) = 1 := by
    have h := congrArg mass hsum
    simpa [mass, Matrix.trace_sum, ρ.trace_one] using h.symm
  obtain ⟨a, ha⟩ : ∃ a, 0 < mass (P a) := by
    by_contra! h
    have hn : (∑ a, mass (P a)) ≤ 0 := Finset.sum_nonpos (fun a _ => h a)
    linarith
  let R : Operator ι := ∑ b ∈ Finset.univ.erase a, P b
  have hR : R.PosSemidef := Matrix.posSemidef_sum _ (fun b _ => outer_positive _)
  have hsplit : ρ.matrix = P a + R := by
    rw [hsum]
    exact (Finset.add_sum_erase Finset.univ P (Finset.mem_univ a)).symm
  have hn := hp.normalize_eq_of_positive_summand ρ (P a) R (outer_positive _) hR hsplit ha
  let v : ι → ℂ := (Real.sqrt (mass (P a)))⁻¹ • (fun i => A i a)
  have hscale : (Real.sqrt (mass (P a)))⁻¹ * (Real.sqrt (mass (P a)))⁻¹ =
      (mass (P a))⁻¹ := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt ha.le]
  have hv : ρ.matrix = outer v := by
    rw [← hn, normalize_matrix, show outer v = (mass (P a))⁻¹ • P a by
      dsimp only [v]
      rw [outer_real_smul, hscale]]
  exact ⟨v, by rw [← hv, ρ.trace_one], hv⟩

/-- Complete purity characterization, with the existing full-state extremality
definition on the left and a proved normalized vector representation on the right. -/
theorem isPure_iff_exists_vector (ρ : Density ι) :
    IsPure ρ ↔ ∃ v : ι → ℂ, (outer v).trace = 1 ∧ ρ.matrix = outer v := by
  constructor
  · exact IsPure.exists_vector ρ
  · rintro ⟨v, hv, hρ⟩
    have heq : ρ = vectorState v hv := Density.ext hρ
    rw [heq]
    exact vectorState_isPure v hv

end
end UEOTQM.QuantumPurification
