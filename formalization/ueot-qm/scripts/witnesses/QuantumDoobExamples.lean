import UEOTQM.QuantumDoob

/-!
# A rational quantum survival example with noncommuting Kraus operators

The source has a nonzero identity Kraus term and two noncommuting reset Kraus
terms. It retains a nonzero multiple of an off-diagonal matrix unit. Its complete failure
branch, both spectral equations, the nontrivial filter, and the resulting
ordinary Doob instrument are checked explicitly. The source survival law and
the transformed finite dynamics are obtained from the general proved theorems.
-/

namespace UEOTQM.QuantumDoobExamples

open Matrix
open UEOTQM.QuantumDoob
open scoped BigOperators ComplexOrder

noncomputable section

def successK : Fin 4 → Operator (Fin 2) :=
  ![!![1/4, 0; 0, 1/4], !![1/4, 0; 1/2, 0],
    !![0, 1/8; 0, 1/4], 0]

def failureK : Fin 4 → Operator (Fin 2) :=
  ![!![3/4, 0; 0, 7/8], !![1/4, 0; 0, 1/4],
    !![0, 0; 0, 1/8], !![0, 0; 0, 1/8]]

theorem success_gram : (∑ k, (successK k)ᴴ * successK k) =
    (!![3/8, 0; 0, 9/64] : Operator (Fin 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [successK, Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem failure_gram : (∑ k, (failureK k)ᴴ * failureK k) =
    (!![5/8, 0; 0, 55/64] : Operator (Fin 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [failureK, Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

def sourceK (o : Bool) : Fin 4 → Operator (Fin 2) :=
  if o then successK else failureK

theorem source_complete : (∑ o, ∑ k, (sourceK o k)ᴴ * sourceK o k) =
    (1 : Operator (Fin 2)) := by
  simp only [Fintype.sum_bool, sourceK, Bool.false_eq_true, ↓reduceIte]
  rw [success_gram, failure_gram]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

def sourceInstrument : Instrument (Fin 2) Bool (Fin 4) where
  kraus := sourceK
  complete := source_complete

/-- The source acts on every complex matrix, retaining the input coherences. -/
theorem source_branch_formula (X : Operator (Fin 2)) :
    sourceInstrument.branch true X =
      !![X 0 0 / 8 + X 1 1 / 64,
         X 0 1 / 16 + X 0 0 / 8 + X 1 1 / 32;
         X 1 0 / 16 + X 0 0 / 8 + X 1 1 / 32,
         X 0 0 / 4 + X 1 1 / 8] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Instrument.branch, krausMap, sourceInstrument, sourceK, successK,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> ring

def rhoMatrix : Operator (Fin 2) := !![1/5, 2/5; 2/5, 4/5]

theorem rhoMatrix_positive : rhoMatrix.PosSemidef := by
  have h : rhoMatrix = (1/5 : ℝ) •
      ((!![1, 2; 0, 0] : Operator (Fin 2))ᴴ * !![1, 2; 0, 0]) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rhoMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat, Matrix.conjTranspose_apply,
        Fin.sum_univ_succ, Complex.real_smul]
  rw [h]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).smul (by norm_num)

theorem rhoMatrix_trace : rhoMatrix.trace = 1 := by
  norm_num [rhoMatrix, Matrix.trace, Fin.sum_univ_succ]

def rho : Density (Fin 2) where
  matrix := rhoMatrix
  positive := rhoMatrix_positive
  trace_one := rhoMatrix_trace

def S : Operator (Fin 2) := !![2, 0; 0, 1]
def T : Operator (Fin 2) := !![1/2, 0; 0, 1]

theorem inverse_mul : T * S = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [S, T, Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat, Fin.sum_univ_succ]

theorem mul_inverse : S * T = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [S, T, Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat, Fin.sum_univ_succ]

def filter : InvertibleFilter (Fin 2) where
  matrix := S
  inverse := T
  inverse_mul := inverse_mul
  mul_inverse := mul_inverse

theorem metric_exact : filter.metric = (!![4, 0; 0, 1] : Operator (Fin 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InvertibleFilter.metric, filter, S, Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem source_right_eigen :
    sourceInstrument.branch true rho.matrix = (3/16 : ℝ) • rho.matrix := by
  rw [source_branch_formula]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rho, rhoMatrix, Complex.real_smul]

theorem source_left_eigen :
    heisenberg (sourceInstrument.kraus true) filter.metric =
      (3/16 : ℝ) • filter.metric := by
  simp only [metric_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heisenberg, sourceInstrument, sourceK, successK,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Complex.real_smul]

theorem filtered_mass_exact : mass (filter.apply rho.matrix) = 8/5 := by
  norm_num [InvertibleFilter.apply, filter, S, rho, rhoMatrix,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat, Matrix.conjTranspose_apply, mass, Matrix.trace,
    Fin.sum_univ_succ]

def plusMatrix : Operator (Fin 2) := !![1/2, 1/2; 1/2, 1/2]

theorem filtered_state_exact : (filter.state rho).matrix = plusMatrix := by
  rw [InvertibleFilter.state_matrix, filtered_mass_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InvertibleFilter.apply, filter, S, rho, rhoMatrix, plusMatrix,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Complex.real_smul]

theorem survival_exact (n : ℕ) : successMass sourceInstrument true rho n =
    (3/16 : ℝ) ^ n :=
  eigen_successMass sourceInstrument true rho (3/16) source_right_eigen n

theorem survival_positive (n : ℕ) : 0 < successMass sourceInstrument true rho n :=
  eigen_successMass_pos sourceInstrument true rho (3/16) (by norm_num)
    source_right_eigen n

theorem qsd_conditional_fixed (n : ℕ)
    (hp : 0 < successMass sourceInstrument true rho n) :
    conditionalState sourceInstrument true rho n hp = rho :=
  eigen_conditionalState sourceInstrument true rho (3/16) (by norm_num)
    source_right_eigen n hp

def transformedInstrument : Instrument (Fin 2) Unit (Fin 4) :=
  doobInstrument filter sourceInstrument true (3/16) (by norm_num) source_left_eigen

/-- The all-operator formula uses the complex trace, so it also covers
non-Hermitian inputs. On densities the second term is two thirds reset to plus. -/
theorem transformed_branch_formula (X : Operator (Fin 2)) :
    transformedInstrument.branch () X =
      (1/3 : ℝ) • X + (X.trace / 3) • (!![1, 1; 1, 1] : Operator (Fin 2)) := by
  rw [transformedInstrument, doob_branch, source_branch_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InvertibleFilter.apply, InvertibleFilter.unapply, filter, S, T,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.trace, Complex.real_smul] <;> ring

theorem transformed_stationary :
    transformedInstrument.channelState (filter.state rho) = filter.state rho :=
  doob_channelState filter sourceInstrument true (3/16) (by norm_num)
    source_left_eigen rho source_right_eigen

theorem transformed_records (n : ℕ) :
    successOperator transformedInstrument () n (filter.state rho).matrix = plusMatrix := by
  rw [transformedInstrument, doob_successOperator_state filter sourceInstrument true
    (3/16) (by norm_num) source_left_eigen rho source_right_eigen n, filtered_state_exact]

theorem transformed_record_mass (n : ℕ) :
    successMass transformedInstrument () (filter.state rho) n = 1 :=
  doob_successMass_state filter sourceInstrument true (3/16) (by norm_num)
    source_left_eigen rho source_right_eigen n

theorem arbitrary_initial_survival_positive (τ : Density (Fin 2)) (n : ℕ) :
    0 < successMass sourceInstrument true τ n :=
  eigenmetric_successMass_pos filter sourceInstrument true (3/16) (by norm_num)
    source_left_eigen τ n

theorem arbitrary_initial_finite_conditioning (τ : Density (Fin 2)) (n : ℕ)
    (hp : 0 < successMass sourceInstrument true τ n) :
    (filter.state (conditionalState sourceInstrument true τ n hp)).matrix =
      successOperator transformedInstrument () n (filter.state τ).matrix :=
  doob_finite_conditioning filter sourceInstrument true (3/16) (by norm_num)
    source_left_eigen τ n hp

/-- Removing the failure Kraus terms destroys completeness. -/
theorem failure_completion_necessary :
    (∑ k, (successK k)ᴴ * successK k) ≠ (1 : Operator (Fin 2)) := by
  rw [success_gram]
  intro h
  have h00 := congrArg (fun X : Operator (Fin 2) => X 0 0) h
  norm_num at h00

theorem success_kraus_noncommuting : successK 1 * successK 2 ≠ successK 2 * successK 1 := by
  change ((!![1/4, 0; 1/2, 0] : Operator (Fin 2)) * !![0, 1/8; 0, 1/4]) ≠
    !![0, 1/8; 0, 1/4] * !![1/4, 0; 1/2, 0]
  intro h
  have h01 := congrArg (fun X : Operator (Fin 2) => X 0 1) h
  norm_num [successK, Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat, Fin.sum_univ_succ] at h01

/-- The source does not erase every off-diagonal input as a diagonal embedding does. -/
theorem input_coherence_retained :
    sourceInstrument.branch true (!![0, 1; 0, 0] : Operator (Fin 2)) =
      (!![0, 1/16; 0, 0] : Operator (Fin 2)) := by
  rw [source_branch_formula]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem qsd_ne_filtered_state : rho ≠ filter.state rho := by
  intro h
  have h01 := congrArg (fun τ : Density (Fin 2) => τ.matrix 0 1) h
  rw [filtered_state_exact] at h01
  norm_num [rho, rhoMatrix, plusMatrix] at h01

def uniformDensity : Density (Fin 2) where
  matrix := (1/2 : ℝ) • (1 : Operator (Fin 2))
  positive := Matrix.PosSemidef.one.smul (by norm_num)
  trace_one := by norm_num [Matrix.trace, Fin.sum_univ_succ, Complex.real_smul]

theorem uniform_probability_exact : sourceInstrument.probability uniformDensity true =
    (33/128 : ℝ) := by
  rw [Instrument.probability, source_branch_formula]
  norm_num [uniformDensity, mass, Matrix.trace, Fin.sum_univ_succ, Complex.real_smul]

/-- The QSD exponent is not the one-step probability from an arbitrary initial state. -/
theorem uniform_probability_ne_qsd : sourceInstrument.probability uniformDensity true ≠
    (3/16 : ℝ) := by
  rw [uniform_probability_exact]
  norm_num

end
end UEOTQM.QuantumDoobExamples

/-! All explicit witness definitions and theorems; generated helper constants excluded. -/
#print axioms UEOTQM.QuantumDoobExamples.successK
#print axioms UEOTQM.QuantumDoobExamples.failureK
#print axioms UEOTQM.QuantumDoobExamples.success_gram
#print axioms UEOTQM.QuantumDoobExamples.failure_gram
#print axioms UEOTQM.QuantumDoobExamples.sourceK
#print axioms UEOTQM.QuantumDoobExamples.source_complete
#print axioms UEOTQM.QuantumDoobExamples.sourceInstrument
#print axioms UEOTQM.QuantumDoobExamples.source_branch_formula
#print axioms UEOTQM.QuantumDoobExamples.rhoMatrix
#print axioms UEOTQM.QuantumDoobExamples.rhoMatrix_positive
#print axioms UEOTQM.QuantumDoobExamples.rhoMatrix_trace
#print axioms UEOTQM.QuantumDoobExamples.rho
#print axioms UEOTQM.QuantumDoobExamples.S
#print axioms UEOTQM.QuantumDoobExamples.T
#print axioms UEOTQM.QuantumDoobExamples.inverse_mul
#print axioms UEOTQM.QuantumDoobExamples.mul_inverse
#print axioms UEOTQM.QuantumDoobExamples.filter
#print axioms UEOTQM.QuantumDoobExamples.metric_exact
#print axioms UEOTQM.QuantumDoobExamples.source_right_eigen
#print axioms UEOTQM.QuantumDoobExamples.source_left_eigen
#print axioms UEOTQM.QuantumDoobExamples.filtered_mass_exact
#print axioms UEOTQM.QuantumDoobExamples.plusMatrix
#print axioms UEOTQM.QuantumDoobExamples.filtered_state_exact
#print axioms UEOTQM.QuantumDoobExamples.survival_exact
#print axioms UEOTQM.QuantumDoobExamples.survival_positive
#print axioms UEOTQM.QuantumDoobExamples.qsd_conditional_fixed
#print axioms UEOTQM.QuantumDoobExamples.transformedInstrument
#print axioms UEOTQM.QuantumDoobExamples.transformed_branch_formula
#print axioms UEOTQM.QuantumDoobExamples.transformed_stationary
#print axioms UEOTQM.QuantumDoobExamples.transformed_records
#print axioms UEOTQM.QuantumDoobExamples.transformed_record_mass
#print axioms UEOTQM.QuantumDoobExamples.arbitrary_initial_survival_positive
#print axioms UEOTQM.QuantumDoobExamples.arbitrary_initial_finite_conditioning
#print axioms UEOTQM.QuantumDoobExamples.failure_completion_necessary
#print axioms UEOTQM.QuantumDoobExamples.success_kraus_noncommuting
#print axioms UEOTQM.QuantumDoobExamples.input_coherence_retained
#print axioms UEOTQM.QuantumDoobExamples.qsd_ne_filtered_state
#print axioms UEOTQM.QuantumDoobExamples.uniformDensity
#print axioms UEOTQM.QuantumDoobExamples.uniform_probability_exact
#print axioms UEOTQM.QuantumDoobExamples.uniform_probability_ne_qsd
