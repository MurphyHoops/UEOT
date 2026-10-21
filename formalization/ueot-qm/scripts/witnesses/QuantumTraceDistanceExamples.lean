import UEOTQM.BinaryDiscrimination
import UEOTQM.RealLocalTomography

/-!
# Exact controls for trace distance, optimal decisions and matrix certificates

The mixed pair is noncommuting and rational. Separate phase controls retain
imaginary coherence. The negative controls remove the zero-trace or support
condition and prove that the corresponding stronger formula fails. These are
finite formal controls, with no laboratory data or numerical solver claim.
-/

namespace UEOTQM.QuantumTraceDistanceExamples

open Matrix QuantumTraceDistance BinaryDiscrimination
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

abbrev Qubit := Fin 2

def rho : Density Qubit where
  matrix := !![(4 / 5 : ℂ), 1 / 5; 1 / 5, 1 / 5]
  positive := by
    have hD : (Matrix.diagonal ![(1 : ℂ), 0]).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun i => by fin_cases i <;> norm_num)
    have hV := Matrix.posSemidef_vecMulVec_self_star ![(1 : ℂ), 1]
    have h := (hD.smul (show (0 : ℝ) ≤ 3 / 5 by norm_num)).add
      (hV.smul (show (0 : ℝ) ≤ 1 / 5 by norm_num))
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [Matrix.vecMulVec, Matrix.diagonal, Complex.mul_re, Complex.mul_im]
  trace_one := by norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

def sigma : Density Qubit where
  matrix := !![(1 / 2 : ℂ), -1 / 5; -1 / 5, 1 / 2]
  positive := by
    have hV := Matrix.posSemidef_vecMulVec_self_star ![(1 : ℂ), -1]
    have h := (Matrix.PosSemidef.one.smul (show (0 : ℝ) ≤ 3 / 10 by norm_num)).add
      (hV.smul (show (0 : ℝ) ≤ 1 / 5 by norm_num))
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [Matrix.vecMulVec, Complex.mul_re, Complex.mul_im]
  trace_one := by norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

def rationalInvolution : Operator Qubit := !![(3 / 5 : ℂ), 4 / 5; 4 / 5, -3 / 5]

theorem rationalInvolution_hermitian : rationalInvolutionᴴ = rationalInvolution := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [rationalInvolution, Matrix.conjTranspose_apply]

theorem rationalInvolution_square : rationalInvolution * rationalInvolution = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [rationalInvolution, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im]

def rationalTest : Effect Qubit :=
  RealLocalTomography.involutionEffect rationalInvolution
    rationalInvolution_hermitian rationalInvolution_square

theorem rationalTest_matrix : rationalTest.matrix = !![(4 / 5 : ℂ), 2 / 5; 2 / 5, 1 / 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [rationalTest, RealLocalTomography.involutionEffect,
      RealLocalTomography.plusProjector, rationalInvolution]

theorem rationalTest_square : rationalTest.matrix * rationalTest.matrix = rationalTest.matrix :=
  RealLocalTomography.plusProjector_square rationalInvolution rationalInvolution_square

def rationalPositive : Operator Qubit := (1 / 2 : ℝ) • rationalTest.matrix

def rationalNegative : Operator Qubit := (1 / 2 : ℝ) • rationalTest.complement.matrix

theorem rationalPositive_psd : rationalPositive.PosSemidef :=
  rationalTest.positive.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem rationalNegative_psd : rationalNegative.PosSemidef :=
  rationalTest.complement.positive.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem rational_difference_split : rho.matrix - sigma.matrix = rationalPositive - rationalNegative := by
  rw [rationalPositive, rationalNegative, Effect.complement_matrix, rationalTest_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> norm_num [rho, sigma]

theorem rational_support_positive : rationalTest.matrix * rationalPositive = rationalPositive := by
  rw [rationalPositive, Matrix.mul_smul, rationalTest_square]

theorem rational_support_negative : rationalTest.matrix * rationalNegative = 0 := by
  rw [rationalNegative, Matrix.mul_smul, Effect.complement_matrix,
    Matrix.mul_sub, Matrix.mul_one, rationalTest_square, sub_self, smul_zero]

theorem rational_positive_mass : mass rationalPositive = 1 / 2 := by
  rw [rationalPositive, mass_smul, rationalTest_matrix]
  norm_num [mass, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem rational_effectDistance : effectDistance rho sigma = 1 / 2 := by
  rw [effectDistance_eq_mass_of_support_certificate rho sigma rationalPositive rationalNegative
    rationalTest rationalPositive_psd rationalNegative_psd rational_difference_split
    rational_support_positive rational_support_negative, rational_positive_mass]

theorem rational_test_probability_rho : rationalTest.probability rho = 21 / 25 := by
  rw [Effect.probability, pairing, rationalTest_matrix]
  norm_num [rho, mass, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im]

theorem rational_test_probability_sigma : rationalTest.probability sigma = 17 / 50 := by
  rw [Effect.probability, pairing, rationalTest_matrix]
  norm_num [sigma, mass, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im]

theorem mixed_states_noncommute : rho.matrix * sigma.matrix ≠ sigma.matrix * rho.matrix := by
  intro h
  have he := congrArg (fun M : Operator Qubit => (M 0 1).re) h
  norm_num [rho, sigma, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] at he

theorem rational_traceAbsolute : traceAbsolute (rho.matrix - sigma.matrix) = 1 := by
  have h := effectDistance_eq_half_traceAbsolute rho sigma
  rw [rational_effectDistance] at h
  linarith

theorem rational_optimal_success : equalPriorSuccess rationalTest rho sigma = 3 / 4 := by
  rw [equalPriorSuccess_eq, rational_test_probability_rho, rational_test_probability_sigma]
  norm_num

theorem rational_all_decisions_le (E : Effect Qubit) : equalPriorSuccess E rho sigma ≤ 3 / 4 := by
  have h := equalPriorSuccess_le E rho sigma
  rw [rational_effectDistance] at h
  norm_num at h ⊢
  exact h

def phasePlus : Density Qubit where
  matrix := RealLocalTomography.plusProjector RealLocalTomography.pauliY
  positive := RealLocalTomography.plusProjector_posSemidef _
    RealLocalTomography.pauliY_hermitian RealLocalTomography.pauliY_square
  trace_one := by
    norm_num [RealLocalTomography.plusProjector, Matrix.trace_smul, Matrix.trace_add,
      RealLocalTomography.pauliY_trace, Matrix.trace_one]

def phaseMinus : Density Qubit where
  matrix := RealLocalTomography.minusProjector RealLocalTomography.pauliY
  positive := RealLocalTomography.minusProjector_posSemidef _
    RealLocalTomography.pauliY_hermitian RealLocalTomography.pauliY_square
  trace_one := by
    norm_num [RealLocalTomography.minusProjector, Matrix.trace_smul, Matrix.trace_sub,
      RealLocalTomography.pauliY_trace, Matrix.trace_one]

def phaseTest : Effect Qubit := RealLocalTomography.complexLocalTest

theorem phase_support_plus : phaseTest.matrix * phasePlus.matrix = phasePlus.matrix :=
  RealLocalTomography.plusProjector_square _ RealLocalTomography.pauliY_square

theorem phase_support_minus : phaseTest.matrix * phaseMinus.matrix = 0 :=
  RealLocalTomography.plusProjector_mul_minusProjector _ RealLocalTomography.pauliY_square

theorem phase_effectDistance : effectDistance phasePlus phaseMinus = 1 := by
  rw [effectDistance_eq_mass_of_support_certificate phasePlus phaseMinus _ _ phaseTest
    phasePlus.positive phaseMinus.positive rfl phase_support_plus phase_support_minus,
    phasePlus.mass_one]

theorem phase_traceAbsolute : traceAbsolute (phasePlus.matrix - phaseMinus.matrix) = 2 := by
  have h := effectDistance_eq_half_traceAbsolute phasePlus phaseMinus
  rw [phase_effectDistance] at h
  linarith

theorem phase_optimal_success : equalPriorSuccess phaseTest phasePlus phaseMinus = 1 := by
  rw [success_eq_optimum_of_support_certificate phasePlus phaseMinus _ _ phaseTest
    phasePlus.positive phaseMinus.positive rfl phase_support_plus phase_support_minus,
    phase_effectDistance]
  norm_num

theorem phase_difference : phasePlus.matrix - phaseMinus.matrix = RealLocalTomography.pauliY := by
  change RealLocalTomography.plusProjector _ - RealLocalTomography.minusProjector _ = _
  unfold RealLocalTomography.plusProjector RealLocalTomography.minusProjector
  module

theorem all_real_effects_miss_phase (E : Effect Qubit) (hR : RealLocalTomography.IsReal E.matrix) :
    E.probability phasePlus = E.probability phaseMinus := by
  apply sub_eq_zero.mp
  simp only [Effect.probability]
  rw [← QuantumSeparation.pairing_sub_right, phase_difference, pairing, mass,
    RealLocalTomography.trace_mul_pauliY_zero E.matrix hR E.positive.isHermitian]
  rfl

theorem all_diagonal_effects_miss_phase (E : Effect Qubit)
    (hdiag : ∀ i j, i ≠ j → E.matrix i j = 0) :
    E.probability phasePlus = E.probability phaseMinus := by
  apply all_real_effects_miss_phase E
  intro i j
  by_cases hij : i = j
  · subst j
    exact (Complex.nonneg_iff.mp (E.positive.diag_nonneg (i := i))).2.symm
  · rw [hdiag i j hij]
    rfl

theorem equal_states_traceAbsolute_zero : traceAbsolute (rho.matrix - rho.matrix) = 0 := by
  simp [traceAbsolute, mass]

def singletonState : Density (Fin 1) where
  matrix := 1
  positive := Matrix.PosSemidef.one
  trace_one := by simp

theorem singleton_nonzero_trace : mass (1 : Operator (Fin 1)) = 1 := by
  simp [mass]

/-- A legal effect already exceeds the false half-trace bound when trace is nonzero. -/
theorem nonzero_trace_half_formula_fails :
    traceAbsolute (1 : Operator (Fin 1)) / 2 <
      |pairing (Effect.one : Effect (Fin 1)).matrix (1 : Operator (Fin 1))| := by
  norm_num [traceAbsolute, CFC.abs_one, pairing, mass]

def overlappingPart : Operator (Fin 1) := (1 / 2 : ℝ) • 1

theorem overlappingPart_psd : overlappingPart.PosSemidef :=
  Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem overlappingParts_are_a_difference_split :
    singletonState.matrix - singletonState.matrix = overlappingPart - overlappingPart := by simp

theorem arbitrary_psd_split_is_not_exact :
    effectDistance singletonState singletonState < mass overlappingPart := by
  norm_num [overlappingPart, mass]

theorem overlappingParts_have_no_support_effect :
    ¬ ∃ E : Effect (Fin 1), E.matrix * overlappingPart = overlappingPart ∧
      E.matrix * overlappingPart = 0 := by
  rintro ⟨E, hp, hn⟩
  have he := hp.symm.trans hn
  have hz := congrArg (fun M : Operator (Fin 1) => (M 0 0).re) he
  norm_num [overlappingPart] at hz

/-- Exact complex unitary input for the independent finite spectral certificate. -/
def certificateMatrix : Operator Qubit :=
  !![(3 / 5 : ℂ), 4 * Complex.I / 5; 4 / 5, -3 * Complex.I / 5]

theorem certificateMatrix_adjoint_mul : certificateMatrixᴴ * certificateMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [certificateMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      map_ofNat, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]

def certificateUnitary : Matrix.unitaryGroup Qubit ℂ :=
  ⟨certificateMatrix, Matrix.mem_unitaryGroup_iff'.mpr certificateMatrix_adjoint_mul⟩

def spectralRho : Density Qubit where
  matrix := unitaryDiagonal certificateUnitary ![(3 / 4 : ℝ), 1 / 4]
  positive := unitaryDiagonal_posSemidef _ _ (fun i => by fin_cases i <;> norm_num)
  trace_one := by
    apply Complex.ext
    · change mass (unitaryDiagonal certificateUnitary ![(3 / 4 : ℝ), 1 / 4]) = 1
      rw [mass_unitaryDiagonal]
      norm_num [Fin.sum_univ_two]
    · exact trace_im_eq_zero
        (unitaryDiagonal_posSemidef certificateUnitary ![(3 / 4 : ℝ), 1 / 4]
          (fun i => by fin_cases i <;> norm_num))

def spectralSigma : Density Qubit where
  matrix := unitaryDiagonal certificateUnitary ![(1 / 4 : ℝ), 3 / 4]
  positive := unitaryDiagonal_posSemidef _ _ (fun i => by fin_cases i <;> norm_num)
  trace_one := by
    apply Complex.ext
    · change mass (unitaryDiagonal certificateUnitary ![(1 / 4 : ℝ), 3 / 4]) = 1
      rw [mass_unitaryDiagonal]
      norm_num [Fin.sum_univ_two]
    · exact trace_im_eq_zero
        (unitaryDiagonal_posSemidef certificateUnitary ![(1 / 4 : ℝ), 3 / 4]
          (fun i => by fin_cases i <;> norm_num))

theorem exact_supplied_diagonalization : spectralRho.matrix - spectralSigma.matrix =
    unitaryDiagonal certificateUnitary ![(1 / 2 : ℝ), -1 / 2] := by
  change unitaryDiagonal certificateUnitary _ - unitaryDiagonal certificateUnitary _ = _
  rw [← unitaryDiagonal_sub]
  congr 1
  funext i
  fin_cases i <;> norm_num

theorem exact_unitary_certificate_distance : effectDistance spectralRho spectralSigma = 1 / 2 := by
  rw [effectDistance_eq_half_sum_abs_of_unitary_data spectralRho spectralSigma
    certificateUnitary _ exact_supplied_diagonalization]
  norm_num [Fin.sum_univ_two]

end

end UEOTQM.QuantumTraceDistanceExamples

/- Every concrete declaration is audited at its actual full name. -/
#print axioms UEOTQM.QuantumTraceDistanceExamples.Qubit
#print axioms UEOTQM.QuantumTraceDistanceExamples.rho
#print axioms UEOTQM.QuantumTraceDistanceExamples.sigma
#print axioms UEOTQM.QuantumTraceDistanceExamples.rationalInvolution
#print axioms UEOTQM.QuantumTraceDistanceExamples.rationalInvolution_hermitian
#print axioms UEOTQM.QuantumTraceDistanceExamples.rationalInvolution_square
#print axioms UEOTQM.QuantumTraceDistanceExamples.rationalTest
#print axioms UEOTQM.QuantumTraceDistanceExamples.rationalTest_matrix
#print axioms UEOTQM.QuantumTraceDistanceExamples.rationalTest_square
#print axioms UEOTQM.QuantumTraceDistanceExamples.rationalPositive
#print axioms UEOTQM.QuantumTraceDistanceExamples.rationalNegative
#print axioms UEOTQM.QuantumTraceDistanceExamples.rationalPositive_psd
#print axioms UEOTQM.QuantumTraceDistanceExamples.rationalNegative_psd
#print axioms UEOTQM.QuantumTraceDistanceExamples.rational_difference_split
#print axioms UEOTQM.QuantumTraceDistanceExamples.rational_support_positive
#print axioms UEOTQM.QuantumTraceDistanceExamples.rational_support_negative
#print axioms UEOTQM.QuantumTraceDistanceExamples.rational_positive_mass
#print axioms UEOTQM.QuantumTraceDistanceExamples.rational_effectDistance
#print axioms UEOTQM.QuantumTraceDistanceExamples.rational_test_probability_rho
#print axioms UEOTQM.QuantumTraceDistanceExamples.rational_test_probability_sigma
#print axioms UEOTQM.QuantumTraceDistanceExamples.mixed_states_noncommute
#print axioms UEOTQM.QuantumTraceDistanceExamples.rational_traceAbsolute
#print axioms UEOTQM.QuantumTraceDistanceExamples.rational_optimal_success
#print axioms UEOTQM.QuantumTraceDistanceExamples.rational_all_decisions_le
#print axioms UEOTQM.QuantumTraceDistanceExamples.phasePlus
#print axioms UEOTQM.QuantumTraceDistanceExamples.phaseMinus
#print axioms UEOTQM.QuantumTraceDistanceExamples.phaseTest
#print axioms UEOTQM.QuantumTraceDistanceExamples.phase_support_plus
#print axioms UEOTQM.QuantumTraceDistanceExamples.phase_support_minus
#print axioms UEOTQM.QuantumTraceDistanceExamples.phase_effectDistance
#print axioms UEOTQM.QuantumTraceDistanceExamples.phase_traceAbsolute
#print axioms UEOTQM.QuantumTraceDistanceExamples.phase_optimal_success
#print axioms UEOTQM.QuantumTraceDistanceExamples.phase_difference
#print axioms UEOTQM.QuantumTraceDistanceExamples.all_real_effects_miss_phase
#print axioms UEOTQM.QuantumTraceDistanceExamples.all_diagonal_effects_miss_phase
#print axioms UEOTQM.QuantumTraceDistanceExamples.equal_states_traceAbsolute_zero
#print axioms UEOTQM.QuantumTraceDistanceExamples.singletonState
#print axioms UEOTQM.QuantumTraceDistanceExamples.singleton_nonzero_trace
#print axioms UEOTQM.QuantumTraceDistanceExamples.nonzero_trace_half_formula_fails
#print axioms UEOTQM.QuantumTraceDistanceExamples.overlappingPart
#print axioms UEOTQM.QuantumTraceDistanceExamples.overlappingPart_psd
#print axioms UEOTQM.QuantumTraceDistanceExamples.overlappingParts_are_a_difference_split
#print axioms UEOTQM.QuantumTraceDistanceExamples.arbitrary_psd_split_is_not_exact
#print axioms UEOTQM.QuantumTraceDistanceExamples.overlappingParts_have_no_support_effect
#print axioms UEOTQM.QuantumTraceDistanceExamples.certificateMatrix
#print axioms UEOTQM.QuantumTraceDistanceExamples.certificateMatrix_adjoint_mul
#print axioms UEOTQM.QuantumTraceDistanceExamples.certificateUnitary
#print axioms UEOTQM.QuantumTraceDistanceExamples.spectralRho
#print axioms UEOTQM.QuantumTraceDistanceExamples.spectralSigma
#print axioms UEOTQM.QuantumTraceDistanceExamples.exact_supplied_diagonalization
#print axioms UEOTQM.QuantumTraceDistanceExamples.exact_unitary_certificate_distance
