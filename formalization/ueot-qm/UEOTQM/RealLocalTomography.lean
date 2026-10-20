import UEOTQM.Effects

/-!
# A concrete failure of local tomography in the finite real quantum sector

Two distinct real density operators on two rebits agree on every product of
real local effects. An actual real joint effect distinguishes them perfectly.
The same states are distinguished by a complex local product test when the
reality restriction is removed. Positivity and upper bounds use the existing
Density, Effect, trace pairing, and actual Kronecker product.

This is a finite sector-separation theorem. Reality, real local effects, and
the chosen product-system rule are explicit model inputs. No full real OPT,
purification theorem, or unconditional UEOT-to-complex-QM reconstruction is
claimed by this module.
-/

namespace UEOTQM.RealLocalTomography

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

noncomputable section

variable {ι ν : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ν] [DecidableEq ν]

/-- The real matrix subspace in the existing complex representation. -/
def IsReal (A : Operator ι) : Prop := ∀ i j, (A i j).im = 0

omit [Fintype ι] [DecidableEq ι] in
theorem symmetric_of_real_hermitian {A : Operator ι}
    (hR : IsReal A) (hH : A.IsHermitian) (i j : ι) : A i j = A j i := by
  apply Complex.ext
  · have h := congrArg Complex.re (hH.apply i j)
    simpa using h.symm
  · rw [hR i j, hR j i]

/-- The actual tensor product of two quantum effects. -/
def productEffect (E : Effect ι) (F : Effect ν) : Effect (ι × ν) where
  matrix := E.matrix ⊗ₖ F.matrix
  positive := E.positive.kronecker F.positive
  complement_positive := by
    have h : (1 : Operator (ι × ν)) - E.matrix ⊗ₖ F.matrix =
        ((1 : Operator ι) - E.matrix) ⊗ₖ (1 : Operator ν) +
          E.matrix ⊗ₖ ((1 : Operator ν) - F.matrix) := by
      rw [← Matrix.one_kronecker_one (m := ι) (n := ν)]
      ext ⟨i, u⟩ ⟨j, v⟩
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.kronecker_apply]
      ring
    rw [h]
    exact (E.complement_positive.kronecker Matrix.PosSemidef.one).add
      (E.positive.kronecker F.complement_positive)

@[simp] theorem productEffect_matrix (E : Effect ι) (F : Effect ν) :
    (productEffect E F).matrix = E.matrix ⊗ₖ F.matrix := rfl

/-- The positive spectral projector of a Hermitian involution. -/
def plusProjector (A : Operator ι) : Operator ι := (1 / 2 : ℝ) • (1 + A)

/-- The negative spectral projector of a Hermitian involution. -/
def minusProjector (A : Operator ι) : Operator ι := (1 / 2 : ℝ) • (1 - A)

omit [Fintype ι] in
theorem plusProjector_hermitian (A : Operator ι) (hA : Aᴴ = A) :
    (plusProjector A)ᴴ = plusProjector A := by
  simp [plusProjector, hA]

omit [Fintype ι] in
theorem minusProjector_hermitian (A : Operator ι) (hA : Aᴴ = A) :
    (minusProjector A)ᴴ = minusProjector A := by
  simp [minusProjector, hA]

theorem plusProjector_square (A : Operator ι) (hA : A * A = 1) :
    plusProjector A * plusProjector A = plusProjector A := by
  unfold plusProjector
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hA]
  module

theorem minusProjector_square (A : Operator ι) (hA : A * A = 1) :
    minusProjector A * minusProjector A = minusProjector A := by
  unfold minusProjector
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hA]
  module

theorem plusProjector_mul_minusProjector (A : Operator ι) (hA : A * A = 1) :
    plusProjector A * minusProjector A = 0 := by
  unfold plusProjector minusProjector
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hA]
  module

omit [Fintype ι] in
theorem one_sub_plusProjector (A : Operator ι) :
    1 - plusProjector A = minusProjector A := by
  unfold plusProjector minusProjector
  module

theorem plusProjector_posSemidef (A : Operator ι) (hH : Aᴴ = A)
    (hA : A * A = 1) : (plusProjector A).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (plusProjector A)
  rw [plusProjector_hermitian A hH, plusProjector_square A hA] at h
  exact h

theorem minusProjector_posSemidef (A : Operator ι) (hH : Aᴴ = A)
    (hA : A * A = 1) : (minusProjector A).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (minusProjector A)
  rw [minusProjector_hermitian A hH, minusProjector_square A hA] at h
  exact h

/-- An actual effect, with both cone bounds derived from the involution. -/
def involutionEffect (A : Operator ι) (hH : Aᴴ = A) (hA : A * A = 1) : Effect ι where
  matrix := plusProjector A
  positive := plusProjector_posSemidef A hH hA
  complement_positive := by
    rw [one_sub_plusProjector]
    exact minusProjector_posSemidef A hH hA

abbrev Qubit := Fin 2
abbrev TwoQubit := Qubit × Qubit

def pauliY : Operator Qubit := !![0, -Complex.I; Complex.I, 0]
def parity : Operator TwoQubit := pauliY ⊗ₖ pauliY

theorem pauliY_hermitian : pauliYᴴ = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.conjTranspose_apply]

theorem pauliY_square : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

theorem parity_hermitian : parityᴴ = parity := by
  simp only [parity, Matrix.conjTranspose_kronecker, pauliY_hermitian]

theorem parity_square : parity * parity = 1 := by
  rw [parity, ← Matrix.mul_kronecker_mul, pauliY_square, Matrix.one_kronecker_one]

theorem pauliY_trace : pauliY.trace = 0 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, pauliY]

theorem parity_trace : parity.trace = 0 := by
  simp [parity, Matrix.trace_kronecker, pauliY_trace]

theorem parity_isReal : IsReal parity := by
  rintro ⟨i, u⟩ ⟨j, v⟩
  fin_cases i <;> fin_cases u <;> fin_cases j <;> fin_cases v <;>
    simp [parity, pauliY]


/-- The two-rebit state supported on the +1 eigenspace of Y tensor Y. -/
def rhoPlus : Density TwoQubit where
  matrix := (1 / 2 : ℝ) • plusProjector parity
  positive := (plusProjector_posSemidef parity parity_hermitian parity_square).smul
    (by norm_num)
  trace_one := by
    norm_num [plusProjector, Matrix.trace_smul, Matrix.trace_add,
      parity_trace, Matrix.trace_one, Fintype.card_prod]

/-- The two-rebit state supported on the -1 eigenspace of Y tensor Y. -/
def rhoMinus : Density TwoQubit where
  matrix := (1 / 2 : ℝ) • minusProjector parity
  positive := (minusProjector_posSemidef parity parity_hermitian parity_square).smul
    (by norm_num)
  trace_one := by
    norm_num [minusProjector, Matrix.trace_smul, Matrix.trace_sub,
      parity_trace, Matrix.trace_one, Fintype.card_prod]

@[simp] theorem rhoPlus_matrix :
    rhoPlus.matrix = (1 / 4 : ℝ) • (1 + parity) := by
  simp only [rhoPlus, plusProjector, smul_smul]
  norm_num

@[simp] theorem rhoMinus_matrix :
    rhoMinus.matrix = (1 / 4 : ℝ) • (1 - parity) := by
  simp only [rhoMinus, minusProjector, smul_smul]
  norm_num

theorem rhoPlus_isReal : IsReal rhoPlus.matrix := by
  intro i j
  by_cases h : i = j
  · subst j
    simp [rhoPlus_matrix, Matrix.add_apply, parity_isReal i i]
  · simp [rhoPlus_matrix, Matrix.add_apply, h, parity_isReal i j]

theorem rhoMinus_isReal : IsReal rhoMinus.matrix := by
  intro i j
  by_cases h : i = j
  · subst j
    simp [rhoMinus_matrix, Matrix.sub_apply, parity_isReal i i]
  · simp [rhoMinus_matrix, Matrix.sub_apply, h, parity_isReal i j]

theorem rhoPlus_symmetric (i j : TwoQubit) :
    rhoPlus.matrix i j = rhoPlus.matrix j i :=
  symmetric_of_real_hermitian rhoPlus_isReal rhoPlus.positive.isHermitian i j

theorem rhoMinus_symmetric (i j : TwoQubit) :
    rhoMinus.matrix i j = rhoMinus.matrix j i :=
  symmetric_of_real_hermitian rhoMinus_isReal rhoMinus.positive.isHermitian i j

theorem density_difference :
    rhoPlus.matrix - rhoMinus.matrix = (1 / 2 : ℝ) • parity := by
  rw [rhoPlus_matrix, rhoMinus_matrix]
  module

/-- Every real symmetric local operator is trace-orthogonal to Pauli Y.
There is no finite sampling of a test family in this statement. -/
theorem trace_mul_pauliY_zero (A : Operator Qubit)
    (hR : IsReal A) (hH : A.IsHermitian) : (A * pauliY).trace = 0 := by
  have h := symmetric_of_real_hermitian hR hH 0 1
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, pauliY, h]

/-- The hidden component is invisible to every pair of real Hermitian local
operators, even before imposing the effect order interval. -/
theorem trace_product_density_difference_zero (E F : Operator Qubit)
    (hER : IsReal E) (hEH : E.IsHermitian)
    (hFR : IsReal F) (hFH : F.IsHermitian) :
    ((E ⊗ₖ F) * (rhoPlus.matrix - rhoMinus.matrix)).trace = 0 := by
  rw [density_difference, Matrix.mul_smul, Matrix.trace_smul]
  rw [parity, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  have h := congrArg₂ (fun a b : ℂ => a * b)
    (trace_mul_pauliY_zero E hER hEH) (trace_mul_pauliY_zero F hFR hFH)
  rw [h, zero_mul, smul_zero]

/-- ALL real local effects give the same actual Born response. -/
theorem all_real_product_probabilities_equal (E F : Effect Qubit)
    (hE : IsReal E.matrix) (hF : IsReal F.matrix) :
    (productEffect E F).probability rhoPlus =
      (productEffect E F).probability rhoMinus := by
  have h := congrArg Complex.re
    (trace_product_density_difference_zero E.matrix F.matrix hE E.positive.isHermitian
      hF F.positive.isHermitian)
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Complex.zero_re] at h
  exact sub_eq_zero.mp h

/-- The real joint projector separating the two states. -/
def jointTest : Effect TwoQubit :=
  involutionEffect parity parity_hermitian parity_square

@[simp] theorem jointTest_matrix : jointTest.matrix = plusProjector parity := rfl

theorem jointTest_isReal : IsReal jointTest.matrix := by
  intro i j
  by_cases h : i = j
  · subst j
    simp [jointTest_matrix, plusProjector, Matrix.add_apply, parity_isReal i i]
  · simp [jointTest_matrix, plusProjector, Matrix.add_apply, h, parity_isReal i j]

theorem jointTest_probability_plus : jointTest.probability rhoPlus = 1 := by
  change mass (plusProjector parity * ((1 / 2 : ℝ) • plusProjector parity)) = 1
  rw [Matrix.mul_smul, plusProjector_square parity parity_square]
  norm_num [mass, plusProjector, Matrix.trace_smul, Matrix.trace_add,
    parity_trace, Matrix.trace_one, Fintype.card_prod]

theorem jointTest_probability_minus : jointTest.probability rhoMinus = 0 := by
  change mass (plusProjector parity * ((1 / 2 : ℝ) • minusProjector parity)) = 0
  rw [Matrix.mul_smul, plusProjector_mul_minusProjector parity parity_square, smul_zero]
  simp [mass]

theorem rhoPlus_ne_rhoMinus : rhoPlus ≠ rhoMinus := by
  intro h
  have hp := congrArg jointTest.probability h
  rw [jointTest_probability_plus, jointTest_probability_minus] at hp
  norm_num at hp

/-- A precise two-rebit failure of state separation by all real product effects. -/
theorem real_local_tomography_fails :
    ∃ ρ σ : Density TwoQubit,
      IsReal ρ.matrix ∧ IsReal σ.matrix ∧ ρ ≠ σ ∧
      (∀ E F : Effect Qubit, IsReal E.matrix → IsReal F.matrix →
        (productEffect E F).probability ρ = (productEffect E F).probability σ) ∧
      ∃ G : Effect TwoQubit, IsReal G.matrix ∧ G.probability ρ = 1 ∧
        G.probability σ = 0 := by
  exact ⟨rhoPlus, rhoMinus, rhoPlus_isReal, rhoMinus_isReal, rhoPlus_ne_rhoMinus,
    all_real_product_probabilities_equal, jointTest, jointTest_isReal,
    jointTest_probability_plus, jointTest_probability_minus⟩

/-- The complex +Y local test, admissible in the surrounding complex sector. -/
def complexLocalTest : Effect Qubit :=
  involutionEffect pauliY pauliY_hermitian pauliY_square

theorem complexLocalTest_not_real : ¬ IsReal complexLocalTest.matrix := by
  intro h
  have h01 := h 0 1
  norm_num [complexLocalTest, involutionEffect, plusProjector, pauliY,
    Matrix.one_apply, Complex.smul_im] at h01

/-- Deleting the real-local restriction restores a product distinction for
this pair. This is a single explicit test, not a general complex reconstruction. -/
theorem complex_product_probability_plus :
    (productEffect complexLocalTest complexLocalTest).probability rhoPlus = 1 / 2 := by
  norm_num [Effect.probability, productEffect, pairing, mass, rhoPlus,
    complexLocalTest, involutionEffect, plusProjector, parity, pauliY,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.kronecker_apply, Matrix.one_apply]

theorem complex_product_probability_minus :
    (productEffect complexLocalTest complexLocalTest).probability rhoMinus = 0 := by
  norm_num [Effect.probability, productEffect, pairing, mass, rhoMinus,
    complexLocalTest, involutionEffect, plusProjector, minusProjector, parity, pauliY,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.kronecker_apply, Matrix.one_apply]

theorem complex_product_distinguishes :
    (productEffect complexLocalTest complexLocalTest).probability rhoPlus ≠
      (productEffect complexLocalTest complexLocalTest).probability rhoMinus := by
  rw [complex_product_probability_plus, complex_product_probability_minus]
  norm_num


end
end UEOTQM.RealLocalTomography
