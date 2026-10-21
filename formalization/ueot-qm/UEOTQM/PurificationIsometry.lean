import UEOTQM.PurificationUniqueness
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Direct purification comparison in the allowed dimension direction

A finite cardinal inequality supplies a coordinate inclusion. The existing
same-carrier unitary theorem then gives a direct rectangular isometry between
two purifications. The direction and the one-sided isometry identity are
explicit; a strict enlargement is not asserted to be a coisometry.
-/

namespace UEOTQM.QuantumPurification

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

noncomputable section

universe u v w
variable {ι : Type u} {α : Type v} {β : Type w}
  [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

omit [Fintype α] [DecidableEq α] [Fintype β] in
/-- The actual coordinate inclusion associated to an injective finite label map. -/
def coordinateIsometry (e : α ↪ β) : Matrix β α ℂ :=
  fun b a => if b = e a then 1 else 0

/-- Coordinate columns are orthonormal; no nonempty-carrier assumption is needed. -/
theorem coordinateIsometry_adjoint_mul (e : α ↪ β) :
    (coordinateIsometry e)ᴴ * coordinateIsometry e = 1 := by
  classical
  ext a b
  simp [coordinateIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, e.injective.eq_iff, eq_comm]

/-- A true finite dimension inequality supplies a rectangular isometry. -/
theorem exists_matrix_isometry_of_card_le (h : Fintype.card α ≤ Fintype.card β) :
    ∃ J : Matrix β α ℂ, Jᴴ * J = 1 := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h
  exact ⟨coordinateIsometry e, coordinateIsometry_adjoint_mul e⟩

/-- The dimension direction is forced by the one-sided isometry identity. -/
theorem card_le_of_matrix_isometry (J : Matrix β α ℂ) (hJ : Jᴴ * J = 1) :
    Fintype.card α ≤ Fintype.card β := by
  calc
    Fintype.card α = (1 : Operator α).rank := Matrix.rank_one.symm
    _ = (Jᴴ * J).rank := congrArg Matrix.rank hJ.symm
    _ ≤ J.rank := Matrix.rank_mul_le_right _ _
    _ ≤ Fintype.card β := Matrix.rank_le_card_height J

/-- Rectangular isometries exist exactly in the nondecreasing dimension direction. -/
theorem exists_matrix_isometry_iff_card_le :
    (∃ J : Matrix β α ℂ, Jᴴ * J = 1) ↔ Fintype.card α ≤ Fintype.card β := by
  constructor
  · rintro ⟨J, hJ⟩
    exact card_le_of_matrix_isometry J hJ
  · exact exists_matrix_isometry_of_card_le

/-- A strict enlargement cannot also satisfy the reverse isometry identity. -/
theorem matrix_isometry_not_coisometry_of_card_lt
    (J : Matrix β α ℂ) (h : Fintype.card α < Fintype.card β) :
    J * Jᴴ ≠ 1 := by
  intro hJ
  have hh : Fintype.card β ≤ Fintype.card α :=
    card_le_of_matrix_isometry Jᴴ (by simpa using hJ)
  exact (Nat.not_le_of_lt h) hh

/-- Full tensor action respects composition of actual auxiliary matrices. -/
theorem auxiliary_tensor_mul (U : Operator β) (J : Matrix β α ℂ) :
    ((1 : Operator ι) ⊗ₖ (U * J)) =
      ((1 : Operator ι) ⊗ₖ U) * ((1 : Operator ι) ⊗ₖ J) := by
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Different auxiliary vectors with equal actual marginals are connected by
a direct isometry whenever the target auxiliary has at least the source dimension. -/
theorem exists_auxiliary_isometry_of_equal_marginal
    (ψ : ι × α → ℂ) (φ : ι × β → ℂ)
    (hcard : Fintype.card α ≤ Fintype.card β)
    (hm : (RectangularChannel.discardRight ι α).operator (outer ψ) =
      (RectangularChannel.discardRight ι β).operator (outer φ)) :
    ∃ J : Matrix β α ℂ, Jᴴ * J = 1 ∧
      φ = ((1 : Operator ι) ⊗ₖ J) *ᵥ ψ := by
  obtain ⟨J₀, hJ₀⟩ := exists_matrix_isometry_of_card_le hcard
  let χ := ((1 : Operator ι) ⊗ₖ J₀) *ᵥ ψ
  have hmχ : (RectangularChannel.discardRight ι β).operator (outer χ) =
      (RectangularChannel.discardRight ι β).operator (outer φ) := by
    rw [show outer χ =
      (auxiliaryEmbeddingChannel (ι := ι) J₀ hJ₀).operator (outer ψ) by
        rw [auxiliaryEmbeddingChannel_operator, ← outer_mulVec]]
    rw [auxiliaryEmbeddingChannel_discard_operator, hm]
  obtain ⟨U, hU, _, hφ⟩ := exists_auxiliary_unitary_of_equal_marginal χ φ hmχ
  refine ⟨U * J₀, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U J₀,
      hU, Matrix.one_mul, hJ₀]
  · rw [hφ, auxiliary_tensor_mul, Matrix.mulVec_mulVec]

/-- The direct isometry action has the same explicit index direction as the
same-carrier theorem, without silently using an adjoint or transpose instead. -/
theorem exists_auxiliary_isometry_action
    (ψ : ι × α → ℂ) (φ : ι × β → ℂ)
    (hcard : Fintype.card α ≤ Fintype.card β)
    (hm : (RectangularChannel.discardRight ι α).operator (outer ψ) =
      (RectangularChannel.discardRight ι β).operator (outer φ)) :
    ∃ J : Matrix β α ℂ, Jᴴ * J = 1 ∧
      ∀ i b, φ (i, b) = ∑ a, J b a * ψ (i, a) := by
  obtain ⟨J, hJ, hφ⟩ := exists_auxiliary_isometry_of_equal_marginal ψ φ hcard hm
  refine ⟨J, hJ, ?_⟩
  intro i b
  rw [hφ, auxiliary_action_apply]

/-- Any two full convex-pure densities with the same actual marginal have a
direct auxiliary isometry in the stated dimension direction. -/
theorem pure_states_isometrically_equivalent
    (Ψ : Density (ι × α)) (Φ : Density (ι × β))
    (hΨ : IsPure Ψ) (hΦ : IsPure Φ)
    (hcard : Fintype.card α ≤ Fintype.card β)
    (hm : (RectangularChannel.discardRight ι α).state Ψ =
      (RectangularChannel.discardRight ι β).state Φ) :
    ∃ J : Matrix β α ℂ, Jᴴ * J = 1 ∧
      Φ.matrix = ((1 : Operator ι) ⊗ₖ J) * Ψ.matrix * ((1 : Operator ι) ⊗ₖ J)ᴴ := by
  obtain ⟨ψ, _, hψ⟩ := hΨ.exists_vector Ψ
  obtain ⟨φ, _, hφ⟩ := hΦ.exists_vector Φ
  have hm' : (RectangularChannel.discardRight ι α).operator (outer ψ) =
      (RectangularChannel.discardRight ι β).operator (outer φ) := by
    have h := congrArg Density.matrix hm
    change (RectangularChannel.discardRight ι α).operator Ψ.matrix =
      (RectangularChannel.discardRight ι β).operator Φ.matrix at h
    rwa [hψ, hφ] at h
  obtain ⟨J, hJ, haction⟩ :=
    exists_auxiliary_isometry_of_equal_marginal ψ φ hcard hm'
  exact ⟨J, hJ, by rw [hψ, hφ, haction, outer_mulVec]⟩

end
end UEOTQM.QuantumPurification
