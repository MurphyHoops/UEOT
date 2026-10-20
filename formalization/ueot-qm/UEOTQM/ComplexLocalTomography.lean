import UEOTQM.QuantumSeparation
import UEOTQM.OperationalSystems

/-!
# Local tomography of the full finite complex matrix model

All legal local product effects determine every entry of an arbitrary joint
density matrix. Local Hermitian tests are obtained by real affine effect
expansion, and explicit real and imaginary matrix units recover the joint
entries. No product-state or separability premise is imposed on the input.
The final theorem uses the existing complex operational presentation, while
the independently proved real-model counterexample is left unchanged.
-/

namespace UEOTQM.ComplexLocalTomography

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

noncomputable section

variable {ι ν : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ν] [DecidableEq ν]

/-- The real Hermitian matrix unit, defined also when the indices coincide. -/
def symmetricUnit (i j : ι) : Operator ι :=
  Matrix.single i j 1 + Matrix.single j i 1

/-- The imaginary Hermitian matrix unit i(e_ij-e_ji). -/
def imaginaryUnit (i j : ι) : Operator ι :=
  Matrix.single i j Complex.I - Matrix.single j i Complex.I

theorem symmetricUnit_hermitian (i j : ι) : (symmetricUnit i j).IsHermitian := by
  simp [symmetricUnit, Matrix.IsHermitian, Matrix.conjTranspose_single, add_comm]

theorem imaginaryUnit_hermitian (i j : ι) : (imaginaryUnit i j).IsHermitian := by
  simp [imaginaryUnit, Matrix.IsHermitian, Matrix.conjTranspose_single,
    ← Matrix.single_neg, sub_eq_add_neg, add_comm]

theorem sub_kronecker (H K : Operator ι) (L : Operator ν) :
    (H - K) ⊗ₖ L = H ⊗ₖ L - K ⊗ₖ L := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.kronecker_apply, Matrix.sub_apply]
  ring

theorem kronecker_sub (H : Operator ι) (K L : Operator ν) :
    H ⊗ₖ (K - L) = H ⊗ₖ K - H ⊗ₖ L := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.kronecker_apply, Matrix.sub_apply]
  ring

/-- Real trace probability pairing reads twice the real entry of a Hermitian input. -/
theorem pairing_symmetricUnit (X : Operator ι) (hX : X.IsHermitian) (i j : ι) :
    pairing (symmetricUnit i j) X = 2 * (X i j).re := by
  have hre := congrArg Complex.re (hX.apply i j)
  simp only [Complex.star_def, Complex.conj_re] at hre
  simp only [pairing, mass, symmetricUnit, Matrix.add_mul, Matrix.trace_add,
    Matrix.trace_single_mul, smul_eq_mul, one_mul, Complex.add_re]
  linarith

/-- The sign is positive for i(e_ij-e_ji); the Hermitian premise is essential. -/
theorem pairing_imaginaryUnit (X : Operator ι) (hX : X.IsHermitian) (i j : ι) :
    pairing (imaginaryUnit i j) X = 2 * (X i j).im := by
  have him := congrArg Complex.im (hX.apply i j)
  simp only [Complex.star_def, Complex.conj_im] at him
  simp only [pairing, mass, imaginaryUnit, Matrix.sub_mul, Matrix.trace_sub,
    Matrix.trace_single_mul, smul_eq_mul, Complex.sub_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  linarith

/-- A joint real matrix unit is a real combination of local Hermitian products. -/
theorem symmetricUnit_product (i j : ι) (a b : ν) :
    symmetricUnit (i, a) (j, b) = (1 / 2 : ℝ) •
      (symmetricUnit i j ⊗ₖ symmetricUnit a b -
        imaginaryUnit i j ⊗ₖ imaginaryUnit a b) := by
  simp only [symmetricUnit, imaginaryUnit, Matrix.add_kronecker, Matrix.kronecker_add,
    sub_kronecker, kronecker_sub, Matrix.single_kronecker_single,
    one_mul, Complex.I_mul_I, ← Matrix.single_neg]
  module

/-- A joint imaginary matrix unit is a real combination of local Hermitian products. -/
theorem imaginaryUnit_product (i j : ι) (a b : ν) :
    imaginaryUnit (i, a) (j, b) = (1 / 2 : ℝ) •
      (imaginaryUnit i j ⊗ₖ symmetricUnit a b +
        symmetricUnit i j ⊗ₖ imaginaryUnit a b) := by
  simp only [symmetricUnit, imaginaryUnit, Matrix.add_kronecker, Matrix.kronecker_add,
    sub_kronecker, kronecker_sub, Matrix.single_kronecker_single,
    one_mul, mul_one]
  module

/-- All product-effect agreement extends only by real, not complex, probability linearity. -/
theorem hermitian_product_pairing_eq (ρ σ : Density (ι × ν))
    (h : ∀ (E : Effect ι) (F : Effect ν),
      (RealLocalTomography.productEffect E F).probability ρ =
        (RealLocalTomography.productEffect E F).probability σ)
    (H : Operator ι) (K : Operator ν) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    pairing (H ⊗ₖ K) ρ.matrix = pairing (H ⊗ₖ K) σ.matrix := by
  obtain ⟨r, E, _, hE⟩ := QuantumSeparation.exists_effect_affine_of_hermitian H hH
  obtain ⟨s, F, _, hF⟩ := QuantumSeparation.exists_effect_affine_of_hermitian K hK
  have hp (E : Effect ι) (F : Effect ν) :
      pairing (E.matrix ⊗ₖ F.matrix) ρ.matrix = pairing (E.matrix ⊗ₖ F.matrix) σ.matrix :=
    h E F
  have hEF := hp E F
  have hE1 : pairing (E.matrix ⊗ₖ (1 : Operator ν)) ρ.matrix =
      pairing (E.matrix ⊗ₖ (1 : Operator ν)) σ.matrix := hp E Effect.one
  have h1F : pairing ((1 : Operator ι) ⊗ₖ F.matrix) ρ.matrix =
      pairing ((1 : Operator ι) ⊗ₖ F.matrix) σ.matrix := hp Effect.one F
  have h11 : pairing ((1 : Operator ι) ⊗ₖ (1 : Operator ν)) ρ.matrix =
      pairing ((1 : Operator ι) ⊗ₖ (1 : Operator ν)) σ.matrix := hp Effect.one Effect.one
  rw [hE, hF]
  simp only [sub_kronecker, kronecker_sub, Matrix.smul_kronecker,
    Matrix.kronecker_smul, pairing_sub_left, pairing_smul_left, hEF, hE1, h1F, h11]

/-- Complete local tomography: the two joint density inputs are arbitrary. -/
theorem density_eq_of_all_product_effect_probabilities_eq (ρ σ : Density (ι × ν))
    (h : ∀ (E : Effect ι) (F : Effect ν),
      (RealLocalTomography.productEffect E F).probability ρ =
        (RealLocalTomography.productEffect E F).probability σ) : ρ = σ := by
  have hp := hermitian_product_pairing_eq ρ σ h
  apply Density.ext
  ext ⟨i, a⟩ ⟨j, b⟩
  apply Complex.ext
  · have hs : pairing (symmetricUnit (i, a) (j, b)) ρ.matrix =
        pairing (symmetricUnit (i, a) (j, b)) σ.matrix := by
      rw [symmetricUnit_product, pairing_smul_left, pairing_smul_left,
        pairing_sub_left, pairing_sub_left,
        hp _ _ (symmetricUnit_hermitian i j) (symmetricUnit_hermitian a b),
        hp _ _ (imaginaryUnit_hermitian i j) (imaginaryUnit_hermitian a b)]
    rw [pairing_symmetricUnit _ ρ.positive.isHermitian,
      pairing_symmetricUnit _ σ.positive.isHermitian] at hs
    linarith
  · have hs : pairing (imaginaryUnit (i, a) (j, b)) ρ.matrix =
        pairing (imaginaryUnit (i, a) (j, b)) σ.matrix := by
      rw [imaginaryUnit_product, pairing_smul_left, pairing_smul_left,
        pairing_add_left, pairing_add_left,
        hp _ _ (imaginaryUnit_hermitian i j) (symmetricUnit_hermitian a b),
        hp _ _ (symmetricUnit_hermitian i j) (imaginaryUnit_hermitian a b)]
    rw [pairing_imaginaryUnit _ ρ.positive.isHermitian,
      pairing_imaginaryUnit _ σ.positive.isHermitian] at hs
    linarith

/-- The same existing presentation satisfies the full local-tomography principle. -/
theorem complex_localTomography :
    OperationalSystems.LocalTomography OperationalSystems.complexModel := by
  intro A B ρ σ h
  exact density_eq_of_all_product_effect_probabilities_eq ρ σ h

end

end UEOTQM.ComplexLocalTomography
