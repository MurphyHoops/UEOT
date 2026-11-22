import UEOTQM.RealLocalTomography
import UEOT.V3.Compression.QuotientDescent
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Real-vs-Complex Quantum Selection Trichotomy & UEOT Core Quotient Descent Bridge (`C-QSEL-05`)

This module closes the foundational real-simulation loopholes opened by Chapter 71 and
`operational_closure` (`Hoffreumon–Woods` shared skew-symmetric reference `τ` and
`Barrios Hita et al.` phase-relocated real quotient tensor product), connecting them
directly to `UEOT.V3.Compression.QuotientDescent` and `UEOTQM.RealLocalTomography`:

1. **Holonomic Dimension Gap (`real_holonomic_gap_identity`, `real_holonomic_gap_pos`)**:
   Standard real symmetric composite spaces carry a strictly positive holonomic dimension
   excess `d_A(d_A - 1) d_B(d_B - 1) / 4 > 0` for all `d_A, d_B ≥ 2`, violating Local Tomography,
   whereas complex Hermitian composite dimension factorizes identically `(d_A d_B)^2 = d_A^2 d_B^2`.

2. **Two-Copy Real-Symmetric Exclusion of Fresh Hoffreumon–Woods Sources (`hwTau`)**:
   While `hwTau = (1/4)(I_4 - J ⊗ J)` matches `(1/4) I_4` on all single-copy real symmetric
   product observables (`single_copy_real_product_blind`), the local two-copy operator
   `localTwoCopyObs = J ⊗ J` is *real symmetric* (`localTwoCopyObs_transpose`) and involutive
   (`localTwoCopyObs_sq`). Every real symmetric single-rebit state `ρ` satisfies `(realJ * ρ).trace = 0`,
   forcing zero expectation across any finite classical mixture of shot-correlated real symmetric
   product states, whereas two copies of `hwTau` achieve unit squared expectation `+1`.
   Moreover, embedded into `ℂ`, `hwTau` coincides entrywise with `UEOTQM.RealLocalTomography.rhoPlus`.

3. **Barrios Hita Phase-Quotient Isomorphism & UEOT Core Quotient Descent (`phaseQuotientEquiv`)**:
   For arbitrary complex vector spaces `U, V`, quotienting the real tensor product `U ⊗[ℝ] V`
   by the Barrios Hita phase-relocation submodule `span_ℝ { (i • u) ⊗ₜ v - u ⊗ₜ (i • v) }`
   yields a canonical `ℝ`-linear isomorphism `(U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V ≃ₗ[ℝ] U ⊗[ℂ] V`.
   Combined with `UEOT.V3.Compression.QuotientDescent.existsUnique_descend`, every observable
   functional invariant under phase relocation descends uniquely to standard complex tensor space.
-/

namespace UEOTPhysicsUnification.RealQuotientSelection

open Matrix Function
open scoped BigOperators Kronecker TensorProduct

/-! ## 1. Exact Holonomic Dimension Gap between Real and Complex Composite State Spaces -/

/-- Twice the composite real symmetric dimension minus the product of twice the local dimensions:
`2 * (dA*dB*(dA*dB + 1)/2) * 2 - (dA*(dA+1)) * (dB*(dB+1)) = dA*(dA-1)*dB*(dB-1)`. -/
theorem real_holonomic_gap_identity (dA dB : ℤ) :
    2 * (dA * dB * (dA * dB + 1)) - (dA * (dA + 1)) * (dB * (dB + 1)) =
      dA * (dA - 1) * (dB * (dB - 1)) := by
  ring

/-- Exact natural-number form of the real symmetric composite dimension excess:
`dA*dB*(dA*dB + 1)/2 = (dA*(dA+1)/2)*(dB*(dB+1)/2) + (dA*(dA-1)/2)*(dB*(dB-1)/2)`
cleared of denominators by `4`. -/
theorem real_holonomic_gap_pos {dA dB : ℕ} (hA : 2 ≤ dA) (hB : 2 ≤ dB) :
    (dA * (dA + 1)) * (dB * (dB + 1)) < 2 * (dA * dB * (dA * dB + 1)) := by
  have h1 : 1 ≤ dA - 1 := by omega
  have h2 : 1 ≤ dB - 1 := by omega
  have hpos : 0 < (dA : ℤ) * ((dA : ℤ) - 1) * ((dB : ℤ) * ((dB : ℤ) - 1)) := by
    have hdA : (0 : ℤ) < dA := by omega
    have hdA1 : (0 : ℤ) < (dA : ℤ) - 1 := by omega
    have hdB : (0 : ℤ) < dB := by omega
    have hdB1 : (0 : ℤ) < (dB : ℤ) - 1 := by omega
    positivity
  have hid := real_holonomic_gap_identity (dA : ℤ) (dB : ℤ)
  have hltZ : ((dA : ℤ) * ((dA : ℤ) + 1)) * ((dB : ℤ) * ((dB : ℤ) + 1)) <
      2 * ((dA : ℤ) * (dB : ℤ) * ((dA : ℤ) * (dB : ℤ) + 1)) := by
    linarith
  exact_mod_cast hltZ

/-- Complex Hermitian composite dimension has zero holonomic gap for all dimensions. -/
theorem complex_hermitian_dim_factorizes (dA dB : ℕ) :
    (dA * dB) ^ 2 = dA ^ 2 * dB ^ 2 := by
  ring

/-! ## 2. Two-Copy Real-Symmetric Witness Excluding Fresh Hoffreumon–Woods Reference States -/

abbrev Rebit := Fin 2
abbrev TwoRebit := Rebit × Rebit

/-- The real skew-symmetric complex-structure generator `J = [[0, -1], [1, 0]]`. -/
def realJ : Matrix Rebit Rebit ℝ := !![0, -1; 1, 0]

theorem realJ_transpose : realJᵀ = -realJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realJ]

theorem realJ_sq : realJ * realJ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem realJ_trace : realJ.trace = 0 := by
  simp [realJ, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Crucial orthogonality: EVERY real symmetric `2 × 2` matrix has zero trace against `realJ`. -/
theorem trace_realJ_mul_symm_zero (ρ : Matrix Rebit Rebit ℝ) (hSym : ρᵀ = ρ) :
    (realJ * ρ).trace = 0 := by
  have h01 : ρ 0 1 = ρ 1 0 := by
    have := congrFun (congrFun hSym 1) 0
    simpa [Matrix.transpose_apply] using this
  simp [realJ, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, h01]

theorem trace_symm_mul_realJ_zero (M : Matrix Rebit Rebit ℝ) (hSym : Mᵀ = M) :
    (M * realJ).trace = 0 := by
  rw [Matrix.trace_mul_comm]
  exact trace_realJ_mul_symm_zero M hSym

/-- Two-copy local observable `O^{(2)} = J ⊗ J` on a pair of rebits in one laboratory. -/
def localTwoCopyObs : Matrix TwoRebit TwoRebit ℝ := realJ ⊗ₖ realJ

/-- Although `J` is skew-symmetric, `J ⊗ J` is GENUINELY REAL SYMMETRIC: `(-J) ⊗ (-J) = J ⊗ J`. -/
theorem localTwoCopyObs_transpose : localTwoCopyObsᵀ = localTwoCopyObs := by
  unfold localTwoCopyObs
  rw [← Matrix.kroneckerMap_transpose, realJ_transpose]
  ext ⟨i, u⟩ ⟨j, v⟩
  simp [Matrix.kroneckerMap_apply]

/-- `J ⊗ J` is an involution with spectrum in `{-1, +1}`. -/
theorem localTwoCopyObs_sq : localTwoCopyObs * localTwoCopyObs = 1 := by
  unfold localTwoCopyObs
  rw [← Matrix.mul_kronecker_mul, realJ_sq]
  ext ⟨i, u⟩ ⟨j, v⟩
  fin_cases i <;> fin_cases u <;> fin_cases j <;> fin_cases v <;>
    simp [Matrix.kroneckerMap_apply]

theorem localTwoCopyObs_trace : localTwoCopyObs.trace = 0 := by
  simp [localTwoCopyObs, Matrix.trace_kronecker, realJ_trace]

/-- The Hoffreumon–Woods real reference state `τ = (1/4)(I_4 - J ⊗ J)`. -/
noncomputable def hwTau : Matrix TwoRebit TwoRebit ℝ :=
  (1 / 4 : ℝ) • (1 - localTwoCopyObs)

theorem hwTau_transpose : hwTauᵀ = hwTau := by
  simp [hwTau, Matrix.transpose_sub, localTwoCopyObs_transpose]

theorem hwTau_trace : hwTau.trace = 1 := by
  norm_num [hwTau, Matrix.trace_smul, Matrix.trace_sub, localTwoCopyObs_trace,
    Matrix.trace_one, Fintype.card_prod]

theorem hwTau_sq : hwTau * hwTau = (1 / 2 : ℝ) • hwTau := by
  unfold hwTau
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h1 : (1 - localTwoCopyObs) * (1 - localTwoCopyObs) =
      (2 : ℝ) • (1 - localTwoCopyObs) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      localTwoCopyObs_sq]
    ext a b
    simp [Matrix.smul_apply]
    ring
  rw [h1, smul_smul, smul_smul]
  norm_num

/-- Exact bridge to `UEOTQM.RealLocalTomography.rhoPlus`: since `pauliY = i • realJ`,
`pauliY ⊗ pauliY = -(realJ ⊗ realJ)`, so `hwTau` lifted to `ℂ` equals `rhoPlus.matrix`. -/
theorem hwTau_complex_eq_rhoPlus (a b : TwoRebit) :
    ((hwTau a b : ℝ) : ℂ) = UEOTQM.RealLocalTomography.rhoPlus.matrix a b := by
  rcases a with ⟨i, u⟩
  rcases b with ⟨j, v⟩
  fin_cases i <;> fin_cases u <;> fin_cases j <;> fin_cases v <;>
    norm_num [hwTau, localTwoCopyObs, realJ, UEOTQM.RealLocalTomography.rhoPlus_matrix,
      UEOTQM.RealLocalTomography.parity, UEOTQM.RealLocalTomography.pauliY,
      Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Single-copy operational independence illusion: `hwTau` factorizes identically as `(1/4) Tr(M_A) Tr(M_B)`
whenever at least one side (`M_A`) is a real symmetric local observable. -/
theorem single_copy_real_product_blind
    (MA MB : Matrix Rebit Rebit ℝ) (hA : MAᵀ = MA) :
    ((MA ⊗ₖ MB) * hwTau).trace = (1 / 4 : ℝ) * MA.trace * MB.trace := by
  unfold hwTau localTwoCopyObs
  rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_sub]
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, Matrix.trace_kronecker]
  rw [trace_symm_mul_realJ_zero MA hA, zero_mul, sub_zero, smul_eq_mul]
  ring

/-- Pairing of `hwTau` against `J ⊗ J` equals `-1`. -/
theorem trace_localTwoCopyObs_hwTau :
    (localTwoCopyObs * hwTau).trace = -1 := by
  unfold hwTau
  rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, localTwoCopyObs_sq,
    Matrix.trace_smul, Matrix.trace_sub, localTwoCopyObs_trace]
  norm_num [Matrix.trace_one, Fintype.card_prod]

/-- Across two independent preparations `hwTau ⊗ hwTau` (rearranged to `(A1,A2) × (B1,B2)`),
the joint expectation of local real symmetric `O_A^{(2)} ⊗ O_B^{(2)}` equals `+1`. -/
theorem two_copy_hwTau_witness_one :
    ((localTwoCopyObs * hwTau).trace) * ((localTwoCopyObs * hwTau).trace) = 1 := by
  rw [trace_localTwoCopyObs_hwTau]
  norm_num

/-- Conversely, for ANY classically correlated ensemble `λ ∈ ι` of two-shot real symmetric
product states `(ρ_{A1,λ}, ρ_{A2,λ}, σ_{B1,λ}, σ_{B2,λ})`, the local two-copy real symmetric
witness `O_A^{(2)} ⊗ O_B^{(2)}` vanishes identically on every branch and in weighted sum! -/
theorem two_copy_real_separable_witness_zero
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (ρA1 ρA2 σB1 σB2 : ι → Matrix Rebit Rebit ℝ)
    (hA1 : ∀ k ∈ s, (ρA1 k)ᵀ = ρA1 k) :
    ∑ k ∈ s, w k *
      (((localTwoCopyObs * (ρA1 k ⊗ₖ ρA2 k)).trace) *
       ((localTwoCopyObs * (σB1 k ⊗ₖ σB2 k)).trace)) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  unfold localTwoCopyObs
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  rw [trace_realJ_mul_symm_zero (ρA1 k) (hA1 k hk)]
  ring

/-! ## 3. Barrios Hita Phase-Relocation Quotient & UEOT Core Quotient Descent Isomorphism -/

section PhaseQuotient

variable (U V : Type*) [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

/-- The Barrios Hita / Stueckelberg real phase-relocation submodule in `U ⊗[ℝ] V`,
generated by `(i • u) ⊗ₜ[ℝ] v - u ⊗ₜ[ℝ] (i • v)`. -/
def phaseRelocationSubmodule : Submodule ℝ (U ⊗[ℝ] V) :=
  Submodule.span ℝ
    { x : U ⊗[ℝ] V | ∃ (u : U) (v : V),
        x = (Complex.I • u) ⊗ₜ[ℝ] v - u ⊗ₜ[ℝ] (Complex.I • v) }

/-- Canonical `ℝ`-linear projection `q_{ℝ→ℂ} : U ⊗[ℝ] V →ₗ[ℝ] U ⊗[ℂ] V`. -/
noncomputable def realToComplexTensor : (U ⊗[ℝ] V) →ₗ[ℝ] (U ⊗[ℂ] V) :=
  TensorProduct.lift
    { toFun := fun u =>
        { toFun := fun v => u ⊗ₜ[ℂ] v
          map_add' := fun v₁ v₂ => TensorProduct.tmul_add u v₁ v₂
          map_smul' := fun (r : ℝ) v => by
            change u ⊗ₜ[ℂ] ((r : ℂ) • v) = (r : ℂ) • (u ⊗ₜ[ℂ] v)
            rw [TensorProduct.tmul_smul] }
      map_add' := fun u₁ u₂ => by
        ext v
        exact TensorProduct.add_tmul u₁ u₂ v
      map_smul' := fun (r : ℝ) u => by
        ext v
        change ((r : ℂ) • u) ⊗ₜ[ℂ] v = (r : ℂ) • (u ⊗ₜ[ℂ] v)
        rw [TensorProduct.smul_tmul'] }

@[simp] theorem realToComplexTensor_tmul (u : U) (v : V) :
    realToComplexTensor U V (u ⊗ₜ[ℝ] v) = u ⊗ₜ[ℂ] v := rfl

theorem realToComplexTensor_surjective : Surjective (realToComplexTensor U V) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul u v => exact ⟨u ⊗ₜ[ℝ] v, rfl⟩
  | add x y hx hy =>
    rcases hx with ⟨x₀, rfl⟩
    rcases hy with ⟨y₀, rfl⟩
    exact ⟨x₀ + y₀, map_add _ x₀ y₀⟩

theorem phaseRelocation_le_ker :
    phaseRelocationSubmodule U V ≤ LinearMap.ker (realToComplexTensor U V) := by
  rw [phaseRelocationSubmodule, Submodule.span_le]
  rintro x ⟨u, v, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, realToComplexTensor_tmul]
  rw [TensorProduct.smul_tmul]
  exact sub_self _

/-- Forward `ℝ`-linear map from the Barrios Hita real quotient `(U ⊗[ℝ] V) ⧸ S_{UV}` to `U ⊗[ℂ] V`. -/
noncomputable def phaseQuotientToComplex :
    ((U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V) →ₗ[ℝ] (U ⊗[ℂ] V) :=
  Submodule.liftQ (phaseRelocationSubmodule U V) (realToComplexTensor U V)
    (phaseRelocation_le_ker U V)

/-- Left multiplication by `i` on `U ⊗[ℝ] V`, descending to the complex structure on the quotient. -/
noncomputable def leftComplexStructure : (U ⊗[ℝ] V) →ₗ[ℝ] (U ⊗[ℝ] V) :=
  TensorProduct.map
    { toFun := fun u => Complex.I • u
      map_add' := fun x y => smul_add Complex.I x y
      map_smul' := fun (r : ℝ) x => by
        change Complex.I • ((r : ℂ) • x) = (r : ℂ) • (Complex.I • x)
        rw [smul_comm] }
    LinearMap.id

@[simp] theorem leftComplexStructure_tmul (u : U) (v : V) :
    leftComplexStructure U V (u ⊗ₜ[ℝ] v) = (Complex.I • u) ⊗ₜ[ℝ] v := rfl

theorem leftComplexStructure_sq (x : U ⊗[ℝ] V) :
    leftComplexStructure U V (leftComplexStructure U V x) = -x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    simp only [leftComplexStructure_tmul, smul_smul, Complex.I_mul_I, neg_one_smul,
      TensorProduct.neg_tmul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, neg_add]

theorem generator_mem_phaseRelocation (u : U) (v : V) :
    (Complex.I • u) ⊗ₜ[ℝ] v - u ⊗ₜ[ℝ] (Complex.I • v) ∈ phaseRelocationSubmodule U V :=
  Submodule.subset_span ⟨u, v, rfl⟩

theorem quotient_tmul_I (u : U) (v : V) :
    Submodule.Quotient.mk ((Complex.I • u) ⊗ₜ[ℝ] v) =
      (Submodule.Quotient.mk (u ⊗ₜ[ℝ] (Complex.I • v)) :
        (U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V) := by
  rw [Submodule.Quotient.eq]
  exact generator_mem_phaseRelocation U V u v

theorem leftComplexStructure_maps_submodule
    {x : U ⊗[ℝ] V} (hx : x ∈ phaseRelocationSubmodule U V) :
    leftComplexStructure U V x ∈ phaseRelocationSubmodule U V := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨u, v, rfl⟩
    simp only [map_sub, leftComplexStructure_tmul, smul_smul, Complex.I_mul_I,
      neg_one_smul, TensorProduct.neg_tmul]
    have h := generator_mem_phaseRelocation U V u (Complex.I • v)
    simp only [smul_smul, Complex.I_mul_I, neg_one_smul, TensorProduct.tmul_neg] at h
    have hneg := (phaseRelocationSubmodule U V).neg_mem h
    convert hneg using 1
    abel
  · simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact (phaseRelocationSubmodule U V).add_mem ha hb
  · intro r a _ ha
    rw [map_smul]
    exact (phaseRelocationSubmodule U V).smul_mem r ha

/-- Descended complex structure `J_Q` on `(U ⊗[ℝ] V) ⧸ S_{UV}`. -/
noncomputable def quotientJ :
    ((U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V) →ₗ[ℝ]
      ((U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V) :=
  Submodule.mapQ (phaseRelocationSubmodule U V) (phaseRelocationSubmodule U V)
    (leftComplexStructure U V)
    (fun _ hx => leftComplexStructure_maps_submodule U V hx)

theorem quotientJ_sq (q : (U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V) :
    quotientJ U V (quotientJ U V q) = -q := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change Submodule.Quotient.mk (leftComplexStructure U V (leftComplexStructure U V x)) = _
  rw [leftComplexStructure_sq, Submodule.Quotient.mk_neg]

/-- Complex scalar action `z •_Q q := z.re • q + z.im • quotientJ q` on the quotient. -/
noncomputable def cSmulQuot (z : ℂ)
    (q : (U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V) :
    (U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V :=
  z.re • q + z.im • quotientJ U V q

theorem cSmulQuot_tmul_left (z : ℂ) (u : U) (v : V) :
    cSmulQuot U V z (Submodule.Quotient.mk (u ⊗ₜ[ℝ] v)) =
      Submodule.Quotient.mk ((z • u) ⊗ₜ[ℝ] v) := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  conv_rhs => rw [hz, add_smul, mul_smul]
  change z.re • Submodule.Quotient.mk (u ⊗ₜ[ℝ] v) +
      z.im • Submodule.Quotient.mk ((Complex.I • u) ⊗ₜ[ℝ] v) =
    Submodule.Quotient.mk (((z.re : ℂ) • u + (z.im : ℂ) • (Complex.I • u)) ⊗ₜ[ℝ] v)
  have hre : ((z.re : ℂ) • u) ⊗ₜ[ℝ] v = z.re • (u ⊗ₜ[ℝ] v) := rfl
  have him : ((z.im : ℂ) • (Complex.I • u)) ⊗ₜ[ℝ] v =
      z.im • ((Complex.I • u) ⊗ₜ[ℝ] v) := rfl
  rw [TensorProduct.add_tmul, hre, him, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]

theorem cSmulQuot_tmul_right (z : ℂ) (u : U) (v : V) :
    cSmulQuot U V z (Submodule.Quotient.mk (u ⊗ₜ[ℝ] v)) =
      Submodule.Quotient.mk (u ⊗ₜ[ℝ] (z • v)) := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  conv_rhs => rw [hz, add_smul, mul_smul]
  change z.re • Submodule.Quotient.mk (u ⊗ₜ[ℝ] v) +
      z.im • Submodule.Quotient.mk ((Complex.I • u) ⊗ₜ[ℝ] v) =
    Submodule.Quotient.mk (u ⊗ₜ[ℝ] ((z.re : ℂ) • v + (z.im : ℂ) • (Complex.I • v)))
  rw [quotient_tmul_I]
  have hre : u ⊗ₜ[ℝ] ((z.re : ℂ) • v) = z.re • (u ⊗ₜ[ℝ] v) := by
    rw [← TensorProduct.tmul_smul]; rfl
  have him : u ⊗ₜ[ℝ] ((z.im : ℂ) • (Complex.I • v)) =
      z.im • (u ⊗ₜ[ℝ] (Complex.I • v)) := by
    rw [← TensorProduct.tmul_smul]; rfl
  rw [TensorProduct.tmul_add, hre, him, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]

/-- Inverse `ℝ`-linear map `U ⊗[ℂ] V →ₗ[ℝ] (U ⊗[ℝ] V) ⧸ S_{UV}` constructed by equipping
the quotient locally with its `ℂ`-module structure and applying `TensorProduct.lift`. -/
noncomputable def complexToPhaseQuotient :
    (U ⊗[ℂ] V) →ₗ[ℝ] ((U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V) := by
  let Q := (U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V
  letI : Module ℂ Q :=
    { smul := cSmulQuot U V
      one_smul := fun q => by
        change (1 : ℂ).re • q + (1 : ℂ).im • quotientJ U V q = q
        simp
      mul_smul := fun w z q => by
        change (w * z).re • q + (w * z).im • quotientJ U V q =
          w.re • (z.re • q + z.im • quotientJ U V q) +
            w.im • quotientJ U V (z.re • q + z.im • quotientJ U V q)
        simp only [Complex.mul_re, Complex.mul_im, map_add, map_smul,
          quotientJ_sq, smul_add, smul_neg, smul_smul]
        module
      smul_zero := fun z => by
        change z.re • (0 : Q) + z.im • quotientJ U V 0 = 0
        simp
      smul_add := fun z q₁ q₂ => by
        change z.re • (q₁ + q₂) + z.im • quotientJ U V (q₁ + q₂) =
          (z.re • q₁ + z.im • quotientJ U V q₁) + (z.re • q₂ + z.im • quotientJ U V q₂)
        simp only [map_add, smul_add]
        abel
      add_smul := fun w z q => by
        change (w + z).re • q + (w + z).im • quotientJ U V q =
          (w.re • q + w.im • quotientJ U V q) + (z.re • q + z.im • quotientJ U V q)
        simp only [Complex.add_re, Complex.add_im, add_smul]
        abel
      zero_smul := fun q => by
        change (0 : ℂ).re • q + (0 : ℂ).im • quotientJ U V q = 0
        simp }
  let fC : (U ⊗[ℂ] V) →ₗ[ℂ] Q :=
    TensorProduct.lift
      { toFun := fun u =>
          { toFun := fun v => (Submodule.Quotient.mk (u ⊗ₜ[ℝ] v) : Q)
            map_add' := fun v₁ v₂ => by
              rw [TensorProduct.tmul_add, Submodule.Quotient.mk_add]
            map_smul' := fun z v => (cSmulQuot_tmul_right U V z u v).symm }
        map_add' := fun u₁ u₂ => by
          ext v
          change (Submodule.Quotient.mk ((u₁ + u₂) ⊗ₜ[ℝ] v) : Q) =
            (Submodule.Quotient.mk (u₁ ⊗ₜ[ℝ] v) : Q) +
              (Submodule.Quotient.mk (u₂ ⊗ₜ[ℝ] v) : Q)
          rw [TensorProduct.add_tmul, Submodule.Quotient.mk_add]
        map_smul' := fun z u => by
          ext v
          exact (cSmulQuot_tmul_left U V z u v).symm }
  exact
    { toFun := fC.toFun
      map_add' := fC.map_add'
      map_smul' := fun (r : ℝ) x => by
        dsimp only [RingHom.id_apply]
        induction x using TensorProduct.induction_on with
        | zero =>
          have h0 : (r : ℝ) • (0 : U ⊗[ℂ] V) = 0 := smul_zero r
          rw [h0]
          change fC (0 : U ⊗[ℂ] V) = r • fC 0
          rw [map_zero, smul_zero]
        | tmul u v =>
          have hsmul : (r : ℝ) • (u ⊗ₜ[ℂ] v) = ((r : ℂ) • u) ⊗ₜ[ℂ] v := by
            rw [← TensorProduct.smul_tmul']
            rfl
          change fC ((r : ℝ) • (u ⊗ₜ[ℂ] v)) = r • fC (u ⊗ₜ[ℂ] v)
          rw [hsmul]
          exact Submodule.Quotient.mk_smul (phaseRelocationSubmodule U V) r (u ⊗ₜ[ℝ] v)
        | add x y hx hy =>
          have hadd_in : (r : ℝ) • (x + y) = (r : ℝ) • x + (r : ℝ) • y :=
            DistribSMul.smul_add r x y
          rw [hadd_in, fC.map_add', fC.map_add', hx, hy]
          exact (DistribSMul.smul_add r (fC.toFun x) (fC.toFun y)).symm }

@[simp] theorem complexToPhaseQuotient_tmul (u : U) (v : V) :
    complexToPhaseQuotient U V (u ⊗ₜ[ℂ] v) = Submodule.Quotient.mk (u ⊗ₜ[ℝ] v) := rfl

@[simp] theorem phaseQuotientToComplex_mk_tmul (u : U) (v : V) :
    phaseQuotientToComplex U V (Submodule.Quotient.mk (u ⊗ₜ[ℝ] v)) = u ⊗ₜ[ℂ] v := rfl

/-- **Main Theorem (`phaseQuotientEquiv`)**: The Barrios Hita real phase-relocation quotient
`(U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V` is canonically `ℝ`-linearly isomorphic to the
standard complex tensor product `U ⊗[ℂ] V`. -/
noncomputable def phaseQuotientEquiv :
    ((U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V) ≃ₗ[ℝ] (U ⊗[ℂ] V) where
  toLinearMap := phaseQuotientToComplex U V
  invFun := complexToPhaseQuotient U V
  left_inv q := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    induction x using TensorProduct.induction_on with
    | zero =>
      change complexToPhaseQuotient U V (phaseQuotientToComplex U V 0) = 0
      simp
    | tmul u v => rfl
    | add x y hx hy =>
      change complexToPhaseQuotient U V
          (phaseQuotientToComplex U V (Submodule.Quotient.mk (x + y))) =
        Submodule.Quotient.mk (x + y)
      rw [Submodule.Quotient.mk_add, map_add, map_add]
      exact congrArg₂ (· + ·) hx hy
  right_inv z := by
    induction z using TensorProduct.induction_on with
    | zero =>
      change phaseQuotientToComplex U V (complexToPhaseQuotient U V 0) = 0
      simp
    | tmul u v => rfl
    | add x y hx hy =>
      change phaseQuotientToComplex U V (complexToPhaseQuotient U V (x + y)) = x + y
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hx hy

/-- Exact kernel identification: `ker(U ⊗[ℝ] V → U ⊗[ℂ] V) = phaseRelocationSubmodule U V`. -/
theorem ker_realToComplexTensor_eq_phaseRelocation :
    LinearMap.ker (realToComplexTensor U V) = phaseRelocationSubmodule U V := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hzero : phaseQuotientEquiv U V (Submodule.Quotient.mk x) = 0 := hx
    have hinj := (phaseQuotientEquiv U V).injective
    have hmk : (Submodule.Quotient.mk x : (U ⊗[ℝ] V) ⧸ phaseRelocationSubmodule U V) = 0 :=
      hinj (by rw [map_zero]; exact hzero)
    exact (Submodule.Quotient.mk_eq_zero _).mp hmk
  · intro hx
    exact phaseRelocation_le_ker U V hx

/-- **Direct Bridge to UEOT Core Generator 1 (`QuotientDescent`)**:
Any observable response functional `g : (U ⊗[ℝ] V) → Z` that is invariant under
Barrios Hita phase relocation (`x - x' ∈ phaseRelocationSubmodule U V → g x = g x'`)
satisfies `UEOT.V3.Compression.QuotientDescent.FiberCompatible` with respect to
`realToComplexTensor`, and therefore descends *uniquely* to a functional `gbar : (U ⊗[ℂ] V) → Z`
on standard complex tensor space! -/
theorem phase_invariant_observable_existsUnique_complex_descent
    {Z : Type*} (g : (U ⊗[ℝ] V) → Z)
    (hInv : ∀ x x' : U ⊗[ℝ] V, x - x' ∈ phaseRelocationSubmodule U V → g x = g x') :
    ∃! gbar : (U ⊗[ℂ] V) → Z, gbar ∘ realToComplexTensor U V = g := by
  apply UEOT.V3.Compression.QuotientDescent.existsUnique_descend
    (realToComplexTensor U V) g (realToComplexTensor_surjective U V)
  intro x x' hq
  apply hInv
  rw [← ker_realToComplexTensor_eq_phaseRelocation U V, LinearMap.mem_ker, map_sub, sub_eq_zero]
  exact hq

end PhaseQuotient

end UEOTPhysicsUnification.RealQuotientSelection
