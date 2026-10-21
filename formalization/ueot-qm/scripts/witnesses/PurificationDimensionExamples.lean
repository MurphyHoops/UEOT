import UEOTQM.PurificationDimension

/-!
# Exact rank and dimension controls for finite purification

A full-rank rational mixed qubit needs two auxiliary dimensions. A pure qubit
needs one. A complex phase-sensitive 2-to-3 map is a genuine isometry, and the
reverse 3-to-2 full-space isometry is impossible.
-/

namespace UEOTQM.PurificationDimensionExamples

open Matrix QuantumPurification
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

noncomputable section

def firstFactor : Operator (Fin 2) := !![(3 / 5 : ℂ), 0; 0, (4 / 5 : ℂ)]

def secondFactor : Matrix (Fin 2) (Fin 3) ℂ :=
  !![(9 / 25 : ℂ), (12 / 25 : ℂ), 0; 16 * Complex.I / 25, -12 * Complex.I / 25, 0]

def directIsometry : Matrix (Fin 3) (Fin 2) ℂ :=
  !![(3 / 5 : ℂ), 4 * Complex.I / 5; (4 / 5 : ℂ), -3 * Complex.I / 5; 0, 0]

def marginalMatrix : Operator (Fin 2) := !![(9 / 25 : ℂ), 0; 0, (16 / 25 : ℂ)]

theorem first_gram : firstFactor * firstFactorᴴ = marginalMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [firstFactor, marginalMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      map_ofNat, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]

theorem second_gram : secondFactor * secondFactorᴴ = marginalMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [secondFactor, marginalMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      map_ofNat, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]

theorem marginal_positive : marginalMatrix.PosSemidef := by
  rw [← first_gram]
  exact Matrix.posSemidef_self_mul_conjTranspose firstFactor

theorem marginal_trace : marginalMatrix.trace = 1 := by
  norm_num [marginalMatrix, Matrix.trace, Fin.sum_univ_succ]

def mixed : Density (Fin 2) := ⟨marginalMatrix, marginal_positive, marginal_trace⟩

theorem mixed_rank_two : mixed.matrix.rank = 2 := by
  have hdet : marginalMatrix.det ≠ 0 := by
    norm_num [marginalMatrix, Matrix.det_fin_two]
  exact Matrix.rank_of_det_ne_zero hdet

theorem first_normalized : (outer (vectorize firstFactor)).trace = 1 := by
  rw [vectorize_outer_trace, first_gram, marginal_trace]

theorem second_normalized : (outer (vectorize secondFactor)).trace = 1 := by
  rw [vectorize_outer_trace, second_gram, marginal_trace]

def firstState : Density (Fin 2 × Fin 2) :=
  vectorState (vectorize firstFactor) first_normalized

def secondState : Density (Fin 2 × Fin 3) :=
  vectorState (vectorize secondFactor) second_normalized

theorem first_pure : IsPure firstState := vectorState_isPure _ _

theorem second_pure : IsPure secondState := vectorState_isPure _ _

theorem first_marginal :
    (RectangularChannel.discardRight (Fin 2) (Fin 2)).state firstState = mixed := by
  apply Density.ext
  change (RectangularChannel.discardRight (Fin 2) (Fin 2)).operator
    (outer (vectorize firstFactor)) = marginalMatrix
  rw [discard_vectorize_outer, first_gram]

theorem second_marginal :
    (RectangularChannel.discardRight (Fin 2) (Fin 3)).state secondState = mixed := by
  apply Density.ext
  change (RectangularChannel.discardRight (Fin 2) (Fin 3)).operator
    (outer (vectorize secondFactor)) = marginalMatrix
  rw [discard_vectorize_outer, second_gram]

theorem mixed_has_two_dimensional_purification :
    ∃ Ψ : Density (Fin 2 × Fin 2), IsPure Ψ ∧
      (RectangularChannel.discardRight (Fin 2) (Fin 2)).state Ψ = mixed :=
  ⟨firstState, first_pure, first_marginal⟩

theorem mixed_no_one_dimensional_purification :
    ¬ ∃ Ψ : Density (Fin 2 × Unit), IsPure Ψ ∧
      (RectangularChannel.discardRight (Fin 2) Unit).state Ψ = mixed := by
  apply no_purification_of_card_lt_rank
  rw [mixed_rank_two]
  decide

theorem mixed_exact_dimension_criterion (α : Type*) [Fintype α] [DecidableEq α] :
    (∃ Ψ : Density (Fin 2 × α), IsPure Ψ ∧
      (RectangularChannel.discardRight (Fin 2) α).state Ψ = mixed) ↔
      2 ≤ Fintype.card α := by
  rw [exists_purification_iff_rank_le, mixed_rank_two]

theorem direct_adjoint_mul : directIsometryᴴ * directIsometry = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [directIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
      map_ofNat, Fin.sum_univ_succ, Matrix.one_apply, Complex.mul_re, Complex.mul_im]

theorem direct_not_coisometry : directIsometry * directIsometryᴴ ≠ 1 := by
  intro h
  have hz (b : Fin 2) : directIsometry (2 : Fin 3) b = 0 := by
    fin_cases b <;> rfl
  have he := congrFun (congrFun h (2 : Fin 3)) (2 : Fin 3)
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hz] at he

theorem exact_rectangular_vector_action :
    ((1 : Operator (Fin 2)) ⊗ₖ directIsometry) *ᵥ vectorize firstFactor =
      vectorize secondFactor := by
  ext p
  rcases p with ⟨i, a⟩
  rw [auxiliary_action_apply]
  fin_cases i <;> fin_cases a <;> apply Complex.ext <;>
    norm_num [vectorize, firstFactor, secondFactor, directIsometry,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]

theorem exact_rectangular_density_action :
    secondState.matrix =
      ((1 : Operator (Fin 2)) ⊗ₖ directIsometry) * firstState.matrix *
        ((1 : Operator (Fin 2)) ⊗ₖ directIsometry)ᴴ := by
  change outer (vectorize secondFactor) = _
  rw [← exact_rectangular_vector_action, outer_mulVec]
  rfl

theorem generic_direct_isometry_instantiated :
    ∃ J : Matrix (Fin 3) (Fin 2) ℂ, Jᴴ * J = 1 ∧
      secondState.matrix = ((1 : Operator (Fin 2)) ⊗ₖ J) * firstState.matrix *
        ((1 : Operator (Fin 2)) ⊗ₖ J)ᴴ := by
  apply pure_states_isometrically_equivalent firstState secondState first_pure second_pure
  · decide
  · rw [first_marginal, second_marginal]

theorem reverse_full_isometry_impossible :
    ¬ ∃ J : Matrix (Fin 2) (Fin 3) ℂ, Jᴴ * J = 1 := by
  rw [exists_matrix_isometry_iff_card_le]
  decide

def pureVector : Fin 2 → ℂ := ![1, 0]

theorem pureVector_normalized : (outer pureVector).trace = 1 := by
  norm_num [outer_trace, pureVector, dotProduct, Fin.sum_univ_succ]

def pureState : Density (Fin 2) := vectorState pureVector pureVector_normalized

theorem pure_state_isPure : IsPure pureState := vectorState_isPure _ _

theorem pure_rank_one : pureState.matrix.rank = 1 := by
  have hle : pureState.matrix.rank ≤ 1 := Matrix.rank_vecMulVec_le pureVector (star pureVector)
  exact Nat.le_antisymm hle (density_rank_pos pureState)

theorem pure_has_unit_auxiliary :
    ∃ Ψ : Density (Fin 2 × Unit), IsPure Ψ ∧
      (RectangularChannel.discardRight (Fin 2) Unit).state Ψ = pureState := by
  apply exists_purification_of_rank_le
  rw [pure_rank_one]
  decide

theorem pure_no_empty_auxiliary :
    ¬ ∃ Ψ : Density (Fin 2 × Fin 0), IsPure Ψ ∧
      (RectangularChannel.discardRight (Fin 2) (Fin 0)).state Ψ = pureState :=
  no_purification_empty_auxiliary pureState

end
end UEOTQM.PurificationDimensionExamples

#print axioms UEOTQM.PurificationDimensionExamples.firstFactor
#print axioms UEOTQM.PurificationDimensionExamples.secondFactor
#print axioms UEOTQM.PurificationDimensionExamples.directIsometry
#print axioms UEOTQM.PurificationDimensionExamples.marginalMatrix
#print axioms UEOTQM.PurificationDimensionExamples.first_gram
#print axioms UEOTQM.PurificationDimensionExamples.second_gram
#print axioms UEOTQM.PurificationDimensionExamples.marginal_positive
#print axioms UEOTQM.PurificationDimensionExamples.marginal_trace
#print axioms UEOTQM.PurificationDimensionExamples.mixed
#print axioms UEOTQM.PurificationDimensionExamples.mixed_rank_two
#print axioms UEOTQM.PurificationDimensionExamples.first_normalized
#print axioms UEOTQM.PurificationDimensionExamples.second_normalized
#print axioms UEOTQM.PurificationDimensionExamples.firstState
#print axioms UEOTQM.PurificationDimensionExamples.secondState
#print axioms UEOTQM.PurificationDimensionExamples.first_pure
#print axioms UEOTQM.PurificationDimensionExamples.second_pure
#print axioms UEOTQM.PurificationDimensionExamples.first_marginal
#print axioms UEOTQM.PurificationDimensionExamples.second_marginal
#print axioms UEOTQM.PurificationDimensionExamples.mixed_has_two_dimensional_purification
#print axioms UEOTQM.PurificationDimensionExamples.mixed_no_one_dimensional_purification
#print axioms UEOTQM.PurificationDimensionExamples.mixed_exact_dimension_criterion
#print axioms UEOTQM.PurificationDimensionExamples.direct_adjoint_mul
#print axioms UEOTQM.PurificationDimensionExamples.direct_not_coisometry
#print axioms UEOTQM.PurificationDimensionExamples.exact_rectangular_vector_action
#print axioms UEOTQM.PurificationDimensionExamples.exact_rectangular_density_action
#print axioms UEOTQM.PurificationDimensionExamples.generic_direct_isometry_instantiated
#print axioms UEOTQM.PurificationDimensionExamples.reverse_full_isometry_impossible
#print axioms UEOTQM.PurificationDimensionExamples.pureVector
#print axioms UEOTQM.PurificationDimensionExamples.pureVector_normalized
#print axioms UEOTQM.PurificationDimensionExamples.pureState
#print axioms UEOTQM.PurificationDimensionExamples.pure_state_isPure
#print axioms UEOTQM.PurificationDimensionExamples.pure_rank_one
#print axioms UEOTQM.PurificationDimensionExamples.pure_has_unit_auxiliary
#print axioms UEOTQM.PurificationDimensionExamples.pure_no_empty_auxiliary
