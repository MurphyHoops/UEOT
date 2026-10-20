import UEOTQM.ComplexLocalTomography

/-!
# Concrete controls for full-effect separation and complex local tomography

Both real and imaginary coherences are invisible to every diagonal effect.
Legal off-diagonal effects distinguish the corresponding states perfectly.
The real-model obstruction, empty carrier, singleton carrier and unequal
local dimensions retain their exact scopes. These are formal finite controls,
not laboratory measurements or a completeness claim for a restricted library.
-/

namespace UEOTQM.QuantumSeparationExamples

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

noncomputable section

abbrev Qubit := Fin 2

def pauliX : Operator Qubit := !![0, 1; 1, 0]

theorem pauliX_hermitian : pauliXᴴ = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]

theorem pauliX_square : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliX_trace : pauliX.trace = 0 := by
  simp [pauliX, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

def xPlus : Density Qubit where
  matrix := RealLocalTomography.plusProjector pauliX
  positive := RealLocalTomography.plusProjector_posSemidef pauliX pauliX_hermitian pauliX_square
  trace_one := by
    norm_num [RealLocalTomography.plusProjector, Matrix.trace_smul, Matrix.trace_add,
      pauliX_trace, Matrix.trace_one]

def xMinus : Density Qubit where
  matrix := RealLocalTomography.minusProjector pauliX
  positive := RealLocalTomography.minusProjector_posSemidef pauliX pauliX_hermitian pauliX_square
  trace_one := by
    norm_num [RealLocalTomography.minusProjector, Matrix.trace_smul, Matrix.trace_sub,
      pauliX_trace, Matrix.trace_one]

def yPlus : Density Qubit where
  matrix := RealLocalTomography.plusProjector RealLocalTomography.pauliY
  positive := RealLocalTomography.plusProjector_posSemidef _
    RealLocalTomography.pauliY_hermitian RealLocalTomography.pauliY_square
  trace_one := by
    norm_num [RealLocalTomography.plusProjector, Matrix.trace_smul, Matrix.trace_add,
      RealLocalTomography.pauliY_trace, Matrix.trace_one]

def yMinus : Density Qubit where
  matrix := RealLocalTomography.minusProjector RealLocalTomography.pauliY
  positive := RealLocalTomography.minusProjector_posSemidef _
    RealLocalTomography.pauliY_hermitian RealLocalTomography.pauliY_square
  trace_one := by
    norm_num [RealLocalTomography.minusProjector, Matrix.trace_smul, Matrix.trace_sub,
      RealLocalTomography.pauliY_trace, Matrix.trace_one]

def xTest : Effect Qubit :=
  RealLocalTomography.involutionEffect pauliX pauliX_hermitian pauliX_square

def yTest : Effect Qubit := RealLocalTomography.complexLocalTest

def IsDiagonal (E : Effect Qubit) : Prop := ∀ i j, i ≠ j → E.matrix i j = 0

theorem diagonal_effect_pairing_eq (E : Effect Qubit) (hE : IsDiagonal E)
    (X Y : Operator Qubit) (hdiag : ∀ i, X i i = Y i i) :
    pairing E.matrix X = pairing E.matrix Y := by
  apply congrArg Complex.re
  change (E.matrix * X).trace = (E.matrix * Y).trace
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    rw [hdiag i]
  · rw [hE i j hij]
    simp

theorem all_diagonal_effects_agree_x (E : Effect Qubit) (hE : IsDiagonal E) :
    E.probability xPlus = E.probability xMinus := by
  apply diagonal_effect_pairing_eq E hE
  intro i
  fin_cases i <;> norm_num [xPlus, xMinus, RealLocalTomography.plusProjector,
    RealLocalTomography.minusProjector, pauliX]

theorem all_diagonal_effects_agree_y (E : Effect Qubit) (hE : IsDiagonal E) :
    E.probability yPlus = E.probability yMinus := by
  apply diagonal_effect_pairing_eq E hE
  intro i
  fin_cases i <;> norm_num [yPlus, yMinus, RealLocalTomography.plusProjector,
    RealLocalTomography.minusProjector, RealLocalTomography.pauliY]

theorem xTest_probability_plus : xTest.probability xPlus = 1 := by
  change mass (RealLocalTomography.plusProjector pauliX *
    RealLocalTomography.plusProjector pauliX) = 1
  rw [RealLocalTomography.plusProjector_square _ pauliX_square]
  exact xPlus.mass_one

theorem xTest_probability_minus : xTest.probability xMinus = 0 := by
  change mass (RealLocalTomography.plusProjector pauliX *
    RealLocalTomography.minusProjector pauliX) = 0
  rw [RealLocalTomography.plusProjector_mul_minusProjector _ pauliX_square]
  simp [mass]

theorem yTest_probability_plus : yTest.probability yPlus = 1 := by
  change mass (RealLocalTomography.plusProjector RealLocalTomography.pauliY *
    RealLocalTomography.plusProjector RealLocalTomography.pauliY) = 1
  rw [RealLocalTomography.plusProjector_square _ RealLocalTomography.pauliY_square]
  exact yPlus.mass_one

theorem yTest_probability_minus : yTest.probability yMinus = 0 := by
  change mass (RealLocalTomography.plusProjector RealLocalTomography.pauliY *
    RealLocalTomography.minusProjector RealLocalTomography.pauliY) = 0
  rw [RealLocalTomography.plusProjector_mul_minusProjector _ RealLocalTomography.pauliY_square]
  simp [mass]

theorem xPlus_ne_xMinus : xPlus ≠ xMinus := by
  intro h
  have heq := congrArg xTest.probability h
  rw [xTest_probability_plus, xTest_probability_minus] at heq
  norm_num at heq

theorem yPlus_ne_yMinus : yPlus ≠ yMinus := by
  intro h
  have heq := congrArg yTest.probability h
  rw [yTest_probability_plus, yTest_probability_minus] at heq
  norm_num at heq

theorem x_effectDistance_exact : effectDistance xPlus xMinus = 1 := by
  apply le_antisymm (effectDistance_le_one _ _)
  have h := xTest.probability_sub_le_effectDistance xPlus xMinus
  simpa [xTest_probability_plus, xTest_probability_minus] using h

theorem y_effectDistance_exact : effectDistance yPlus yMinus = 1 := by
  apply le_antisymm (effectDistance_le_one _ _)
  have h := yTest.probability_sub_le_effectDistance yPlus yMinus
  simpa [yTest_probability_plus, yTest_probability_minus] using h

theorem empty_carrier_has_no_density (ρ : Density (Fin 0)) : False :=
  QuantumPurification.density_empty_elim ρ

theorem singleton_densities_equal (ρ σ : Density (Fin 1)) : ρ = σ := by
  apply Density.ext
  funext i j
  have hρ : ρ.matrix 0 0 = 1 := by simpa [Matrix.trace, Matrix.diag] using ρ.trace_one
  have hσ : σ.matrix 0 0 = 1 := by simpa [Matrix.trace, Matrix.diag] using σ.trace_one
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  simpa only [hi, hj] using hρ.trans hσ.symm

theorem unequal_local_dimensions_tomography (ρ σ : Density (Qubit × Fin 3))
    (h : ∀ (E : Effect Qubit) (F : Effect (Fin 3)),
      (RealLocalTomography.productEffect E F).probability ρ =
        (RealLocalTomography.productEffect E F).probability σ) : ρ = σ :=
  ComplexLocalTomography.density_eq_of_all_product_effect_probabilities_eq ρ σ h

theorem full_complex_model_localTomography :
    OperationalSystems.LocalTomography OperationalSystems.complexModel :=
  ComplexLocalTomography.complex_localTomography

theorem full_real_model_not_localTomography :
    ¬ OperationalSystems.LocalTomography OperationalSystems.realModel :=
  OperationalSystems.real_not_localTomography

end

end UEOTQM.QuantumSeparationExamples

/- Every witness declaration is audited in its actual source order. -/
#print axioms UEOTQM.QuantumSeparationExamples.Qubit
#print axioms UEOTQM.QuantumSeparationExamples.pauliX
#print axioms UEOTQM.QuantumSeparationExamples.pauliX_hermitian
#print axioms UEOTQM.QuantumSeparationExamples.pauliX_square
#print axioms UEOTQM.QuantumSeparationExamples.pauliX_trace
#print axioms UEOTQM.QuantumSeparationExamples.xPlus
#print axioms UEOTQM.QuantumSeparationExamples.xMinus
#print axioms UEOTQM.QuantumSeparationExamples.yPlus
#print axioms UEOTQM.QuantumSeparationExamples.yMinus
#print axioms UEOTQM.QuantumSeparationExamples.xTest
#print axioms UEOTQM.QuantumSeparationExamples.yTest
#print axioms UEOTQM.QuantumSeparationExamples.IsDiagonal
#print axioms UEOTQM.QuantumSeparationExamples.diagonal_effect_pairing_eq
#print axioms UEOTQM.QuantumSeparationExamples.all_diagonal_effects_agree_x
#print axioms UEOTQM.QuantumSeparationExamples.all_diagonal_effects_agree_y
#print axioms UEOTQM.QuantumSeparationExamples.xTest_probability_plus
#print axioms UEOTQM.QuantumSeparationExamples.xTest_probability_minus
#print axioms UEOTQM.QuantumSeparationExamples.yTest_probability_plus
#print axioms UEOTQM.QuantumSeparationExamples.yTest_probability_minus
#print axioms UEOTQM.QuantumSeparationExamples.xPlus_ne_xMinus
#print axioms UEOTQM.QuantumSeparationExamples.yPlus_ne_yMinus
#print axioms UEOTQM.QuantumSeparationExamples.x_effectDistance_exact
#print axioms UEOTQM.QuantumSeparationExamples.y_effectDistance_exact
#print axioms UEOTQM.QuantumSeparationExamples.empty_carrier_has_no_density
#print axioms UEOTQM.QuantumSeparationExamples.singleton_densities_equal
#print axioms UEOTQM.QuantumSeparationExamples.unequal_local_dimensions_tomography
#print axioms UEOTQM.QuantumSeparationExamples.full_complex_model_localTomography
#print axioms UEOTQM.QuantumSeparationExamples.full_real_model_not_localTomography
