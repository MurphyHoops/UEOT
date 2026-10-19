import UEOTQM.Weighted

/-!
# Exact Gaussian-rational matrix data

`MatrixData` stores real and imaginary parts as rational matrices.  Its
computable operations use complex multiplication and conjugate transpose.
The interpretation into actual complex matrices is injective and preserves
the operations needed by finite weighted quantum certificates.

No completeness or closure equation is a field of `MatrixData`: concrete
equations are separate propositions, decidable for finite index types.
The examples use `decide +kernel`, which checks rational arithmetic directly
in the Lean kernel even when rational operations are marked irreducible to
the elaborator. No native evaluation proof shortcut is used.
-/

namespace UEOTQM.Exact

open Matrix
open scoped BigOperators

/-- A matrix whose real and imaginary entries are rational. -/
structure MatrixData (m n : Type*) where
  re : Matrix m n ℚ
  im : Matrix m n ℚ

/-- Square exact matrix data. -/
abbrev OperatorData (ι : Type*) := MatrixData ι ι

namespace MatrixData

variable {m n p α : Type*}

@[ext] theorem ext {A B : MatrixData m n}
    (hre : A.re = B.re) (him : A.im = B.im) : A = B := by
  cases A
  cases B
  cases hre
  cases him
  rfl

/-- Computable equality for finite rational matrix tables. -/
instance instDecidableEq [Fintype m] [Fintype n] : DecidableEq (MatrixData m n) :=
  fun A B =>
    if hr : A.re = B.re then
      if hi : A.im = B.im then isTrue (ext hr hi)
      else isFalse (fun h => hi (congrArg MatrixData.im h))
    else isFalse (fun h => hr (congrArg MatrixData.re h))

def zero : MatrixData m n := ⟨0, 0⟩

def one [DecidableEq n] : MatrixData n n := ⟨1, 0⟩

def add (A B : MatrixData m n) : MatrixData m n :=
  ⟨A.re + B.re, A.im + B.im⟩

def neg (A : MatrixData m n) : MatrixData m n := ⟨-A.re, -A.im⟩

def sub (A B : MatrixData m n) : MatrixData m n :=
  ⟨A.re - B.re, A.im - B.im⟩

/-- Complex matrix multiplication `(A+iB)(C+iD)=(AC-BD)+i(AD+BC)`. -/
def mul [Fintype n] (A : MatrixData m n) (B : MatrixData n p) : MatrixData m p :=
  ⟨A.re * B.re - A.im * B.im, A.re * B.im + A.im * B.re⟩

/-- Transpose followed by conjugation, including the imaginary sign. -/
def adjoint (A : MatrixData m n) : MatrixData n m :=
  ⟨A.reᵀ, -A.imᵀ⟩

def scale (q : ℚ) (A : MatrixData m n) : MatrixData m n :=
  ⟨q • A.re, q • A.im⟩

def sum (s : Finset α) (f : α → MatrixData m n) : MatrixData m n :=
  ⟨∑ a ∈ s, (f a).re, ∑ a ∈ s, (f a).im⟩

/-- Interpret exact table entries in the actual complex field. -/
noncomputable def toMatrix (A : MatrixData m n) : Matrix m n ℂ :=
  fun i j => ⟨(A.re i j : ℝ), (A.im i j : ℝ)⟩

@[simp] theorem toMatrix_re (A : MatrixData m n) (i : m) (j : n) :
    (A.toMatrix i j).re = (A.re i j : ℝ) := rfl

@[simp] theorem toMatrix_im (A : MatrixData m n) (i : m) (j : n) :
    (A.toMatrix i j).im = (A.im i j : ℝ) := rfl

/-- Exact table equality is equivalent to equality after complex interpretation. -/
theorem toMatrix_injective : Function.Injective (toMatrix (m := m) (n := n)) := by
  intro A B h
  apply ext
  · ext i j
    have hij := congrArg (fun M : Matrix m n ℂ => (M i j).re) h
    simpa only [toMatrix_re, Rat.cast_inj] using hij
  · ext i j
    have hij := congrArg (fun M : Matrix m n ℂ => (M i j).im) h
    simpa only [toMatrix_im, Rat.cast_inj] using hij

@[simp] theorem toMatrix_eq_iff (A B : MatrixData m n) :
    A.toMatrix = B.toMatrix ↔ A = B := toMatrix_injective.eq_iff

@[simp] theorem toMatrix_zero : (zero (m := m) (n := n)).toMatrix = 0 := by
  ext i j
  apply Complex.ext <;> simp [toMatrix, zero]

@[simp] theorem toMatrix_one [DecidableEq n] :
    (one (n := n)).toMatrix = 1 := by
  ext i j
  apply Complex.ext <;>
    by_cases h : i = j <;> simp [toMatrix, one, Matrix.one_apply, h]

@[simp] theorem toMatrix_add (A B : MatrixData m n) :
    (add A B).toMatrix = A.toMatrix + B.toMatrix := by
  ext i j
  apply Complex.ext <;> simp [toMatrix, add]

@[simp] theorem toMatrix_neg (A : MatrixData m n) :
    (neg A).toMatrix = -A.toMatrix := by
  ext i j
  apply Complex.ext <;> simp [toMatrix, neg]

@[simp] theorem toMatrix_sub (A B : MatrixData m n) :
    (sub A B).toMatrix = A.toMatrix - B.toMatrix := by
  ext i j
  apply Complex.ext <;> simp [toMatrix, sub]

@[simp] theorem toMatrix_mul [Fintype n] (A : MatrixData m n) (B : MatrixData n p) :
    (mul A B).toMatrix = A.toMatrix * B.toMatrix := by
  ext i j
  apply Complex.ext <;>
    simp [toMatrix, mul, Matrix.mul_apply, Complex.mul_re, Complex.mul_im,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]

@[simp] theorem toMatrix_adjoint (A : MatrixData m n) :
    (adjoint A).toMatrix = A.toMatrixᴴ := by
  ext i j
  apply Complex.ext <;> simp [toMatrix, adjoint, Matrix.conjTranspose_apply]

@[simp] theorem toMatrix_scale (q : ℚ) (A : MatrixData m n) :
    (scale q A).toMatrix = (q : ℝ) • A.toMatrix := by
  ext i j
  apply Complex.ext <;> simp [toMatrix, scale, smul_eq_mul]

@[simp] theorem toMatrix_sum (s : Finset α) (f : α → MatrixData m n) :
    (sum s f).toMatrix = ∑ a ∈ s, (f a).toMatrix := by
  ext i j
  apply Complex.ext <;> simp [toMatrix, sum, Matrix.sum_apply]

end MatrixData

/-- Square-matrix specialization of the exact interpretation. -/
noncomputable abbrev toOperator {ι : Type*} (A : OperatorData ι) : Operator ι :=
  A.toMatrix

variable {ι κ : Type*} [Fintype ι]

/-- An exact weighted Schrödinger sum. Weights are unrestricted in this algebraic definition. -/
def weightedBranch (s : Finset κ) (w : κ → ℚ) (K : κ → OperatorData ι)
    (X : OperatorData ι) : OperatorData ι :=
  MatrixData.sum s fun k =>
    MatrixData.scale (w k) (MatrixData.mul (MatrixData.mul (K k) X)
      (MatrixData.adjoint (K k)))

/-- An exact weighted Heisenberg sum, with conjugation on the left. -/
def weightedPullback (s : Finset κ) (w : κ → ℚ) (K : κ → OperatorData ι)
    (E : OperatorData ι) : OperatorData ι :=
  MatrixData.sum s fun k =>
    MatrixData.scale (w k) (MatrixData.mul (MatrixData.mul
      (MatrixData.adjoint (K k)) E) (K k))

/-- The weighted sum of Kraus Gram matrices, before any equality to identity is asserted. -/
def weightedCompleteness (s : Finset κ) (w : κ → ℚ)
    (K : κ → OperatorData ι) : OperatorData ι :=
  MatrixData.sum s fun k =>
    MatrixData.scale (w k) (MatrixData.mul (MatrixData.adjoint (K k)) (K k))

@[simp] theorem toMatrix_weightedBranch (s : Finset κ) (w : κ → ℚ)
    (K : κ → OperatorData ι) (X : OperatorData ι) :
    (weightedBranch s w K X).toMatrix =
      ∑ k ∈ s, (w k : ℝ) • ((K k).toMatrix * X.toMatrix * (K k).toMatrixᴴ) := by
  simp only [weightedBranch, MatrixData.toMatrix_sum, MatrixData.toMatrix_scale,
    MatrixData.toMatrix_mul, MatrixData.toMatrix_adjoint]

@[simp] theorem toMatrix_weightedPullback (s : Finset κ) (w : κ → ℚ)
    (K : κ → OperatorData ι) (E : OperatorData ι) :
    (weightedPullback s w K E).toMatrix =
      ∑ k ∈ s, (w k : ℝ) • ((K k).toMatrixᴴ * E.toMatrix * (K k).toMatrix) := by
  simp only [weightedPullback, MatrixData.toMatrix_sum, MatrixData.toMatrix_scale,
    MatrixData.toMatrix_mul, MatrixData.toMatrix_adjoint]

@[simp] theorem toMatrix_weightedCompleteness (s : Finset κ) (w : κ → ℚ)
    (K : κ → OperatorData ι) :
    (weightedCompleteness s w K).toMatrix =
      ∑ k ∈ s, (w k : ℝ) • ((K k).toMatrixᴴ * (K k).toMatrix) := by
  simp only [weightedCompleteness, MatrixData.toMatrix_sum, MatrixData.toMatrix_scale,
    MatrixData.toMatrix_mul, MatrixData.toMatrix_adjoint]

/-- The full finite exact branch interprets as the ordinary real-weighted formula. -/
theorem toMatrix_weightedBranch_univ [Fintype κ] (w : κ → ℚ)
    (K : κ → OperatorData ι) (X : OperatorData ι) :
    (weightedBranch Finset.univ w K X).toMatrix =
      weightedKrausMap (fun k => (w k : ℝ)) (fun k => (K k).toMatrix) X.toMatrix := by
  simp only [toMatrix_weightedBranch, weightedKrausMap]

/-- The full finite exact pullback interprets as the ordinary real-weighted formula. -/
theorem toMatrix_weightedPullback_univ [Fintype κ] (w : κ → ℚ)
    (K : κ → OperatorData ι) (E : OperatorData ι) :
    (weightedPullback Finset.univ w K E).toMatrix =
      weightedHeisenberg (fun k => (w k : ℝ)) (fun k => (K k).toMatrix) E.toMatrix := by
  simp only [toMatrix_weightedPullback, weightedHeisenberg]

namespace Examples

/-- A genuinely imaginary entry exercises conjugation and the `i² = -1` sign. -/
def imaginaryUnit : OperatorData (Fin 1) :=
  ⟨fun _ _ => 0, fun _ _ => 1⟩

theorem imaginaryUnit_square_exact :
    MatrixData.mul imaginaryUnit imaginaryUnit = MatrixData.neg MatrixData.one := by
  decide +kernel

theorem imaginaryUnit_adjoint_exact :
    MatrixData.adjoint imaginaryUnit = MatrixData.neg imaginaryUnit := by
  decide +kernel

theorem imaginaryUnit_square_complex :
    imaginaryUnit.toMatrix * imaginaryUnit.toMatrix = -(1 : Operator (Fin 1)) := by
  have h := congrArg MatrixData.toMatrix imaginaryUnit_square_exact
  simpa only [MatrixData.toMatrix_mul, MatrixData.toMatrix_neg, MatrixData.toMatrix_one] using h

/-- The unnormalised Hadamard table; the square root belongs to the later ordinary instrument. -/
def hadamardNumerator : OperatorData (Fin 2) :=
  ⟨fun i j => if i = 1 ∧ j = 1 then -1 else 1, fun _ _ => 0⟩

theorem hadamard_complete_exact :
    weightedCompleteness Finset.univ (fun _ : Fin 1 => (1 / 2 : ℚ))
      (fun _ => hadamardNumerator) = MatrixData.one := by
  decide +kernel

theorem hadamard_complete_complex :
    (1 / 2 : ℝ) • (hadamardNumerator.toMatrixᴴ * hadamardNumerator.toMatrix) = 1 := by
  have h := congrArg MatrixData.toMatrix hadamard_complete_exact
  simpa only [toMatrix_weightedCompleteness, MatrixData.toMatrix_one, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat, Fin.sum_univ_one] using h

end Examples

end UEOTQM.Exact
