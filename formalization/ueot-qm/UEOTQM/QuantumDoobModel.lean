import UEOTQM.QuantumDoob

/-!
# The fixed rational noncommutative survival model

This public model reproduces the explicit Kraus, density and filter data from the
frozen v31.6 dedicated witness. The old witness remains unchanged. The main
package imports this module rather than any file under scripts/witnesses.
Completeness and the two eigenrelations are proved from the actual matrices.
The model retains nonzero input coherence and has noncommuting success Kraus.
This extraction is infrastructure for new dynamics, not a new physical model.
-/

namespace UEOTQM.QuantumDoobModel

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

/-- The filtered density is the normalized plus state; no positivity is assumed. -/
def plus : Density (Fin 2) := filter.state rho

@[simp] theorem plus_matrix : plus.matrix = plusMatrix := filtered_state_exact

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


end
end UEOTQM.QuantumDoobModel
