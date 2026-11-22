import UEOT.V3.Compression.QuotientDescent
import UEOTQM.CorePurificationBoundary
import UEOTQM.OperationalSystems
import UEOTQM.ComplexLocalTomography
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Deep Bridge 2: UEOT `QuotientDescent` → Finite-Dimensional GPT Self-Dual Cone, Jordan Selection & Born Rule
(`C-GPT-RECON-02`)

Establishes the complete machine-checked reconstruction chain connecting UEOT Core's first compression
generator (`UEOT.V3.Compression.QuotientDescent`) and `UEOTQM`'s operational boundary modules to the
complex Hermitian PSD cone `Herm(ℂ^d)_+` and the Born trace rule:

1. **Canonical Operational GPT Quotient State-Effect Duality from Core `QuotientDescent`**:
   - `operational_gpt_minimal_separating_quotient`: Applies `existsUnique_twoSidedDescend` to quotient
     raw laboratory preparations `P` and measurement outcomes `M` under `p : P → M → ℝ`, yielding the
     unique minimal separating GPT state-effect pairing `p_bar : StateQuot p → EffectQuot p → ℝ`
     where states separate effects and effects separate states.

2. **Exact Self-Duality (`C = C*`) of the Hermitian Positive-Semidefinite Cone**:
   - `hermitian_psd_cone_self_dual`: Proves both directions of Koecher-Vinberg self-duality on
     `UEOTQM.Operator ι`: for any Hermitian matrix `X`, `X.PosSemidef ↔ ∀ Y, Y.PosSemidef → 0 ≤ pairing Y X`.

3. **Constructive Gleason-Busch / Born Trace Representation & Uniqueness Theorem**:
   - `gleason_busch_born_density_existsUnique`: Any normalized (`Λ 1 = 1`), PSD-nonnegative
     real-linear valuation `Λ : Operator ι →ₗ[ℝ] ℝ` is represented by a *unique* positive-semidefinite
     unit-trace quantum density matrix `ρ : UEOTQM.Density ι` satisfying
     `∀ E : UEOTQM.Effect ι, Λ E.matrix = E.probability ρ`.

4. **Euclidean Jordan Algebra Composite Dimension Identity & Hurwitz `r = 2` (`ℂ`) Selection**:
   - `jordan_composite_dim_defect_identity` & `hurwitz_jordan_local_tomography_uniquely_selects_complex`:
     For formally real simple Jordan matrix algebras `𝔥_d(𝕂)` of rank `d` and division-ring real
     dimension `r ∈ {1, 2, 4, 8}` (`ℝ, ℂ, ℍ, 𝕆`), single-system state dimension `D_1(d, r) = d + r d(d-1)/2`
     obeys `4 * (D_1(d_A, r) * D_1(d_B, r) - D_1(d_A * d_B, r)) = d_A * d_B * r * (r - 2) * (d_A - 1) * (d_B - 1)`.
     Over all `d_A, d_B ≥ 2` and `r ≥ 1`, local tomographic tensor closure holds **iff `r = 2` (`ℂ`-QM)**.

5. **End-to-End UEOT Core → `UEOTQM` Three-Model Operational Classification**:
   - `ueot_core_to_complex_qm_three_model_bridge`: Unites `CorePurificationBoundary.FiniteCoreSlice`
     (classical failure of purification on Core's actual `survivalMicroKernel` terminal quotient),
     `realModel` failure of local tomography, and `complexModel` joint satisfaction of `Laws`,
     `PurificationExistence`, and `LocalTomography`.
-/

namespace UEOTPhysicsUnification.GPTSelfDualConeReconstruction

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open UEOT.V3.Compression.QuotientDescent

/-! ## 1. Operational GPT Minimal Separating State-Effect Quotient via Core `QuotientDescent` -/

/-- Canonical preparation equivalence induced by an operational probability table `p : P → M → ℝ`. -/
def prepSetoid {P M : Type*} (p : P → M → ℝ) : Setoid P where
  r x x' := ∀ m : M, p x m = p x' m
  iseqv := ⟨fun _ _ => rfl, fun h m => (h m).symm, fun h1 h2 m => (h1 m).trans (h2 m)⟩

/-- Canonical measurement-effect equivalence induced by `p : P → M → ℝ`. -/
def measSetoid {P M : Type*} (p : P → M → ℝ) : Setoid M where
  r m m' := ∀ x : P, p x m = p x m'
  iseqv := ⟨fun _ _ => rfl, fun h x => (h x).symm, fun h1 h2 x => (h1 x).trans (h2 x)⟩

abbrev StateQuot {P M : Type*} (p : P → M → ℝ) := Quotient (prepSetoid p)
abbrev EffectQuot {P M : Type*} (p : P → M → ℝ) := Quotient (measSetoid p)

/-- Core's `existsUnique_twoSidedDescend` produces the unique minimal separating GPT state-effect
pairing where quotient states separate quotient effects and quotient effects separate quotient states. -/
theorem operational_gpt_minimal_separating_quotient
    {P M : Type*} (p : P → M → ℝ) :
    ∃! pbar : StateQuot p → EffectQuot p → ℝ,
      (∀ (x : P) (m : M), pbar ⟦x⟧ ⟦m⟧ = p x m) ∧
      (∀ s1 s2 : StateQuot p, (∀ e : EffectQuot p, pbar s1 e = pbar s2 e) ↔ s1 = s2) ∧
      (∀ e1 e2 : EffectQuot p, (∀ s : StateQuot p, pbar s e1 = pbar s e2) ↔ e1 = e2) := by
  let F : Unit → P → M → ℝ := fun _ x m => p x m
  let qP : P → StateQuot p := Quotient.mk (prepSetoid p)
  let qM : M → EffectQuot p := Quotient.mk (measSetoid p)
  have hP : Function.Surjective qP := Quotient.mk_surjective
  have hM : Function.Surjective qM := Quotient.mk_surjective
  have hcompat : TwoSidedCompatible qP qM F := by
    constructor
    · intro _ m x x' hxx
      exact Quotient.exact hxx m
    · intro _ x m m' hmm
      exact Quotient.exact hmm x
  rcases existsUnique_twoSidedDescend qP qM F hP hM hcompat with ⟨Q, hQ, huniq⟩
  refine ⟨Q (), ⟨fun x m => hQ () x m, ?_, ?_⟩, ?_⟩
  · intro s1 s2
    constructor
    · intro hall
      rcases hP s1 with ⟨x1, rfl⟩
      rcases hP s2 with ⟨x2, rfl⟩
      apply Quotient.sound
      intro m
      have hm := hall (qM m)
      rw [hQ () x1 m, hQ () x2 m] at hm
      exact hm
    · rintro rfl _
      rfl
  · intro e1 e2
    constructor
    · intro hall
      rcases hM e1 with ⟨m1, rfl⟩
      rcases hM e2 with ⟨m2, rfl⟩
      apply Quotient.sound
      intro x
      have hx := hall (qP x)
      rw [hQ () x m1, hQ () x m2] at hx
      exact hx
    · rintro rfl _
      rfl
  · intro pbar hpbar
    have hQeq : (fun _ : Unit => pbar) = Q := by
      apply huniq
      intro u x m
      cases u
      exact hpbar.1 x m
    exact congrFun hQeq ()

/-! ## 2. Exact Self-Duality (`C = C*`) of the Hermitian Positive-Semidefinite Cone -/

section SelfDualAndBorn

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Outer-product rank-one positive semidefinite test operator `|v⟩⟨v|` written as `R_vᴴ * R_v`. -/
def rankOneRow (v : ι → ℂ) : Matrix (Fin 1) ι ℂ :=
  Matrix.of (fun _ j => star (v j))

def rankOneTest (v : ι → ℂ) : UEOTQM.Operator ι :=
  (rankOneRow v)ᴴ * rankOneRow v

omit [DecidableEq ι] in
theorem rankOneTest_posSemidef (v : ι → ℂ) : (rankOneTest v).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self (rankOneRow v)

omit [DecidableEq ι] in
/-- Exact evaluation of the trace pairing `Re Tr(|v⟩⟨v| X) = Re ⟨v, X v⟩`. -/
theorem pairing_rankOneTest (v : ι → ℂ) (X : UEOTQM.Operator ι) :
    UEOTQM.pairing (rankOneTest v) X = (star v ⬝ᵥ X *ᵥ v).re := by
  unfold UEOTQM.pairing UEOTQM.mass rankOneTest rankOneRow
  have htr : (((Matrix.of fun (_ : Fin 1) j => star (v j))ᴴ *
      Matrix.of fun (_ : Fin 1) j => star (v j)) * X).trace =
      star v ⬝ᵥ X *ᵥ v := by
    unfold Matrix.trace Matrix.diag
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fin.sum_univ_one, dotProduct, mulVec, star_star, Pi.star_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [htr]

/-- Exact Koecher-Vinberg self-duality (`C = C*`) of the Hermitian PSD cone:
a Hermitian operator `X` is positive semidefinite iff its Hilbert-Schmidt pairing with every
positive semidefinite operator `Y` is nonnegative. -/
theorem hermitian_psd_cone_self_dual {X : UEOTQM.Operator ι} (hX : X.IsHermitian) :
    X.PosSemidef ↔ ∀ Y : UEOTQM.Operator ι, Y.PosSemidef → 0 ≤ UEOTQM.pairing Y X := by
  constructor
  · intro hXpos Y hYpos
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hYpos.nonneg
    unfold UEOTQM.pairing UEOTQM.mass
    rw [hB]
    change 0 ≤ ((Bᴴ * B * X).trace).re
    rw [← Matrix.trace_mul_cycle B X Bᴴ]
    have hpsd : (B * X * Bᴴ).PosSemidef := hXpos.mul_mul_conjTranspose_same B
    have hnn : (0 : ℂ) ≤ (B * X * Bᴴ).trace := hpsd.trace_nonneg
    exact (Complex.nonneg_iff.mp hnn).1
  · intro hdual
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hX, ?_⟩
    intro v
    have hre : 0 ≤ (star v ⬝ᵥ X *ᵥ v).re := by
      rw [← pairing_rankOneTest v X]
      exact hdual (rankOneTest v) (rankOneTest_posSemidef v)
    have him : (star v ⬝ᵥ X *ᵥ v).im = 0 := by
      have hconj : star (star v ⬝ᵥ X *ᵥ v) = star v ⬝ᵥ X *ᵥ v := by
        calc
          star (star v ⬝ᵥ X *ᵥ v) = star (X *ᵥ v) ⬝ᵥ v := (star_dotProduct (X *ᵥ v) v).symm
          _ = (star v ᵥ* Xᴴ) ⬝ᵥ v := by rw [Matrix.star_mulVec]
          _ = (star v ᵥ* X) ⬝ᵥ v := by rw [hX.eq]
          _ = star v ⬝ᵥ X *ᵥ v := (Matrix.dotProduct_mulVec (star v) X v).symm
      have him_neg := congrArg Complex.im hconj
      simp only [Complex.star_def, Complex.conj_im] at him_neg
      linarith
    exact Complex.nonneg_iff.mpr ⟨hre, him.symm⟩

/-! ## 3. Constructive Gleason-Busch / Born-Rule Representation & Uniqueness -/

/-- Any Hermitian matrix `H` expands identically into real-linear combinations of
`ComplexLocalTomography.symmetricUnit` and `imaginaryUnit`. -/
theorem hermitian_basis_expansion (H : UEOTQM.Operator ι) (hH : H.IsHermitian) :
    H = ∑ i : ι, ∑ j : ι,
      (((H i j).re / 2 : ℝ) • UEOTQM.ComplexLocalTomography.symmetricUnit i j +
       ((H i j).im / 2 : ℝ) • UEOTQM.ComplexLocalTomography.imaginaryUnit i j) := by
  ext a b
  have hsym_ba : (H b a).re = (H a b).re := by
    have h := congrArg Complex.re (hH.apply b a)
    simpa [Complex.star_def, Complex.conj_re] using h.symm
  have him_ba : (H b a).im = -(H a b).im := by
    have h := congrArg Complex.im (hH.apply b a)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have hs1 : (∑ i : ι, ∑ j : ι, ((H i j).re / 2 : ℝ) •
      (Matrix.single i j (1 : ℂ)) a b) = (((H a b).re / 2 : ℝ) : ℂ) := by
    simp [Matrix.single_apply, ite_and, Complex.real_smul]
  have hs2 : (∑ i : ι, ∑ j : ι, ((H i j).re / 2 : ℝ) •
      (Matrix.single j i (1 : ℂ)) a b) = (((H b a).re / 2 : ℝ) : ℂ) := by
    rw [Finset.sum_comm]
    simp [Matrix.single_apply, ite_and, Complex.real_smul]
  have hi1 : (∑ i : ι, ∑ j : ι, ((H i j).im / 2 : ℝ) •
      (Matrix.single i j Complex.I) a b) = (((H a b).im / 2 : ℝ) : ℂ) * Complex.I := by
    simp [Matrix.single_apply, ite_and, Complex.real_smul]
  have hi2 : (∑ i : ι, ∑ j : ι, ((H i j).im / 2 : ℝ) •
      (Matrix.single j i Complex.I) a b) = (((H b a).im / 2 : ℝ) : ℂ) * Complex.I := by
    rw [Finset.sum_comm]
    simp [Matrix.single_apply, ite_and, Complex.real_smul]
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply,
    UEOTQM.ComplexLocalTomography.symmetricUnit,
    UEOTQM.ComplexLocalTomography.imaginaryUnit,
    Matrix.sub_apply, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hs1, hs2, hi1, hi2, hsym_ba, him_ba]
  calc
    H a b = ((H a b).re : ℂ) + ((H a b).im : ℂ) * Complex.I := (Complex.re_add_im (H a b)).symm
    _ = _ := by push_cast; ring

/-- Constructive Gleason-Busch matrix extracted from any real-linear valuation `Λ` on `Operator ι`. -/
noncomputable def bornMatrixOfLinear (Lambda : UEOTQM.Operator ι →ₗ[ℝ] ℝ) : UEOTQM.Operator ι :=
  Matrix.of fun i j =>
    ((Lambda (UEOTQM.ComplexLocalTomography.symmetricUnit i j) / 2 : ℝ) : ℂ) +
    ((Lambda (UEOTQM.ComplexLocalTomography.imaginaryUnit i j) / 2 : ℝ) : ℂ) * Complex.I

omit [Fintype ι] in
theorem bornMatrixOfLinear_hermitian (Lambda : UEOTQM.Operator ι →ₗ[ℝ] ℝ) :
    (bornMatrixOfLinear Lambda).IsHermitian := by
  ext i j
  have hsym_comm : UEOTQM.ComplexLocalTomography.symmetricUnit j i =
      UEOTQM.ComplexLocalTomography.symmetricUnit i j := by
    ext a b
    simp [UEOTQM.ComplexLocalTomography.symmetricUnit, add_comm]
  have him_anticomm : UEOTQM.ComplexLocalTomography.imaginaryUnit j i =
      -UEOTQM.ComplexLocalTomography.imaginaryUnit i j := by
    ext a b
    simp [UEOTQM.ComplexLocalTomography.imaginaryUnit]
  simp only [Matrix.conjTranspose_apply, bornMatrixOfLinear, Matrix.of_apply,
    hsym_comm, him_anticomm, map_neg]
  apply Complex.ext
  · simp
  · simp; ring

/-- Every real-linear valuation `Λ` on `Operator ι` agrees on all Hermitian matrices with
the Born trace pairing `H ↦ Re Tr(H * bornMatrixOfLinear Λ)`. -/
theorem bornMatrixOfLinear_reproduces_hermitian
    (Lambda : UEOTQM.Operator ι →ₗ[ℝ] ℝ)
    (H : UEOTQM.Operator ι) (hH : H.IsHermitian) :
    UEOTQM.pairing H (bornMatrixOfLinear Lambda) = Lambda H := by
  have hW : (bornMatrixOfLinear Lambda).IsHermitian := bornMatrixOfLinear_hermitian Lambda
  have hexp := hermitian_basis_expansion H hH
  conv_lhs => rw [hexp]
  conv_rhs => rw [hexp]
  have hpair_sum : ∀ f : ι → UEOTQM.Operator ι,
      UEOTQM.pairing (∑ i : ι, f i) (bornMatrixOfLinear Lambda) =
        ∑ i : ι, UEOTQM.pairing (f i) (bornMatrixOfLinear Lambda) := by
    intro f
    simp [UEOTQM.pairing, UEOTQM.mass, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  rw [hpair_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hpair_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hps := UEOTQM.ComplexLocalTomography.pairing_symmetricUnit (bornMatrixOfLinear Lambda) hW i j
  have hpi := UEOTQM.ComplexLocalTomography.pairing_imaginaryUnit (bornMatrixOfLinear Lambda) hW i j
  have hre_ij : (bornMatrixOfLinear Lambda i j).re =
      Lambda (UEOTQM.ComplexLocalTomography.symmetricUnit i j) / 2 := by
    simp [bornMatrixOfLinear]
  have him_ij : (bornMatrixOfLinear Lambda i j).im =
      Lambda (UEOTQM.ComplexLocalTomography.imaginaryUnit i j) / 2 := by
    simp [bornMatrixOfLinear]
  simp only [UEOTQM.pairing_add_left, UEOTQM.pairing_smul_left, map_add, map_smul, smul_eq_mul]
  rw [hps, hpi, hre_ij, him_ij]
  ring

/-- Complete Finite-Dimensional Gleason-Busch / Born-Rule Representation & Uniqueness Theorem:
Every normalized (`Λ 1 = 1`), PSD-nonnegative real-linear functional `Λ : Operator ι →ₗ[ℝ] ℝ`
is represented by a *unique* quantum density matrix `ρ : Density ι` (`ρ ⪰ 0`, `Tr ρ = 1`) via
`Λ(E.matrix) = E.probability ρ = Re Tr(E * ρ)` for all quantum effects `E`. -/
theorem gleason_busch_born_density_existsUnique
    (Lambda : UEOTQM.Operator ι →ₗ[ℝ] ℝ)
    (hpos : ∀ Y : UEOTQM.Operator ι, Y.PosSemidef → 0 ≤ Lambda Y)
    (hnorm : Lambda (1 : UEOTQM.Operator ι) = 1) :
    ∃! rho : UEOTQM.Density ι, ∀ E : UEOTQM.Effect ι, E.probability rho = Lambda E.matrix := by
  let W : UEOTQM.Operator ι := bornMatrixOfLinear Lambda
  have hWherm : W.IsHermitian := bornMatrixOfLinear_hermitian Lambda
  have hWpos : W.PosSemidef := by
    refine (hermitian_psd_cone_self_dual hWherm).mpr ?_
    intro Y hY
    rw [bornMatrixOfLinear_reproduces_hermitian Lambda Y hY.isHermitian]
    exact hpos Y hY
  have hWtrace_re : W.trace.re = 1 := by
    have h1 : UEOTQM.pairing (1 : UEOTQM.Operator ι) W = Lambda 1 :=
      bornMatrixOfLinear_reproduces_hermitian Lambda 1 Matrix.isHermitian_one
    unfold UEOTQM.pairing UEOTQM.mass at h1
    rw [Matrix.one_mul, hnorm] at h1
    exact h1
  have hWtrace : W.trace = 1 := by
    apply Complex.ext
    · simpa using hWtrace_re
    · simpa using UEOTQM.trace_im_eq_zero hWpos
  let rho0 : UEOTQM.Density ι := ⟨W, hWpos, hWtrace⟩
  refine ⟨rho0, ?_, ?_⟩
  · intro E
    exact bornMatrixOfLinear_reproduces_hermitian Lambda E.matrix E.positive.isHermitian
  · intro sigma hsigma
    apply UEOTQM.QuantumSeparation.density_eq_of_all_effect_probabilities_eq
    intro E
    rw [hsigma E]
    exact (bornMatrixOfLinear_reproduces_hermitian Lambda E.matrix E.positive.isHermitian).symm

end SelfDualAndBorn

/-! ## 4. Euclidean Jordan Algebra Composite Dimension Identity & Hurwitz `r = 2` (`ℂ`) Selection -/

/-- Single-system real state-space dimension `D_1(d, r) = d + r * d * (d - 1) / 2` of the simple
formally real Jordan algebra `𝔥_d(𝕂)` over a division algebra of real dimension `r`. -/
noncomputable def jordanStateDim (d r : ℝ) : ℝ :=
  d + r * d * (d - 1) / 2

/-- Universal Jordan Tensor-Composite Defect Identity:
`4 * (D_1(d_A, r) * D_1(d_B, r) - D_1(d_A * d_B, r)) = d_A * d_B * r * (r - 2) * (d_A - 1) * (d_B - 1)`. -/
theorem jordan_composite_dim_defect_identity (dA dB r : ℝ) :
    4 * (jordanStateDim dA r * jordanStateDim dB r - jordanStateDim (dA * dB) r) =
      dA * dB * r * (r - 2) * (dA - 1) * (dB - 1) := by
  unfold jordanStateDim
  ring

/-- Complete Hurwitz / Jordan Local-Tomography Selection Theorem:
For all nontrivial subsystem ranks `dA ≥ 2`, `dB ≥ 2` and positive division-ring dimensions `r > 0`
(in particular across all four Hurwitz normed division algebras `r ∈ {1, 2, 4, 8}` for `ℝ, ℂ, ℍ, 𝕆`):
1. Local tomographic composite closure `D_1(dA, r) * D_1(dB, r) = D_1(dA * dB, r)` holds **iff `r = 2` (`ℂ`)**;
2. Real symmetric Jordan cones (`r = 1`) strictly under-span (`D_1(dA, 1) * D_1(dB, 1) < D_1(dA * dB, 1)`);
3. Quaternionic (`r = 4`) and octonionic (`r = 8`) cones strictly over-span (`D_1(dA, r) * D_1(dB, r) > D_1(dA * dB, r)`). -/
theorem hurwitz_jordan_local_tomography_uniquely_selects_complex
    {dA dB r : ℝ} (hdA : 2 ≤ dA) (hdB : 2 ≤ dB) (hr : 0 < r) :
    (jordanStateDim dA r * jordanStateDim dB r = jordanStateDim (dA * dB) r ↔ r = 2) ∧
      jordanStateDim dA 1 * jordanStateDim dB 1 < jordanStateDim (dA * dB) 1 ∧
      jordanStateDim (dA * dB) 4 < jordanStateDim dA 4 * jordanStateDim dB 4 ∧
      jordanStateDim (dA * dB) 8 < jordanStateDim dA 8 * jordanStateDim dB 8 := by
  have hdA_pos : 0 < dA := by linarith
  have hdB_pos : 0 < dB := by linarith
  have hdA1_pos : 0 < dA - 1 := by linarith
  have hdB1_pos : 0 < dB - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro heq
      have hid := jordan_composite_dim_defect_identity dA dB r
      have hzero : dA * dB * r * (r - 2) * (dA - 1) * (dB - 1) = 0 := by linarith
      have hfac_pos : 0 < dA * dB * r * (dA - 1) * (dB - 1) := by positivity
      have hfac_ne : dA * dB * r * (dA - 1) * (dB - 1) ≠ 0 := ne_of_gt hfac_pos
      have hrew : (dA * dB * r * (dA - 1) * (dB - 1)) * (r - 2) = 0 := by linarith
      have hr2 : r - 2 = 0 := (mul_eq_zero.mp hrew).resolve_left hfac_ne
      linarith
    · rintro rfl
      have hid := jordan_composite_dim_defect_identity dA dB 2
      linarith
  · have hid1 := jordan_composite_dim_defect_identity dA dB 1
    have hneg : dA * dB * 1 * ((1 : ℝ) - 2) * (dA - 1) * (dB - 1) < 0 := by
      have hp : 0 < dA * dB * (dA - 1) * (dB - 1) := by positivity
      linarith
    linarith
  · have hid4 := jordan_composite_dim_defect_identity dA dB 4
    have hpos4 : 0 < dA * dB * 4 * ((4 : ℝ) - 2) * (dA - 1) * (dB - 1) := by positivity
    linarith
  · have hid8 := jordan_composite_dim_defect_identity dA dB 8
    have hpos8 : 0 < dA * dB * 8 * ((8 : ℝ) - 2) * (dA - 1) * (dB - 1) := by positivity
    linarith

/-! ## 5. Unified End-to-End UEOT Core → `UEOTQM` Three-Model Operational Classification -/

/-- Master Core-to-QM Reconstruction Bridge (`C-GPT-RECON-02`):
1. Core's actual `survivalMicroKernel` satisfies `FiniteCoreSlice` while its terminal-quotient
   first marginal admits no purification in `classicalModel` over any finite ancilla `B`;
2. `classicalModel` satisfies `Laws` but fails `PurificationExistence`;
3. `realModel` satisfies `Laws` but fails `LocalTomography`;
4. `complexModel` simultaneously satisfies `Laws`, `PurificationExistence`, and `LocalTomography`. -/
theorem ueot_core_to_complex_qm_three_model_bridge :
    UEOTQM.CorePurificationBoundary.FiniteCoreSlice ∧
      (∀ B : UEOTQM.OperationalSystems.FiniteSystem,
        ¬ ∃ Psi : UEOTQM.OperationalSystems.classicalModel.State
            (UEOTQM.OperationalSystems.coreSystem.product B),
          UEOTQM.OperationalSystems.Purifies UEOTQM.OperationalSystems.classicalModel
            Psi UEOTQM.CorePurificationBoundary.firstQuotientState) ∧
      (UEOTQM.OperationalSystems.Laws UEOTQM.OperationalSystems.classicalModel ∧
        ¬ UEOTQM.OperationalSystems.PurificationExistence UEOTQM.OperationalSystems.classicalModel) ∧
      (UEOTQM.OperationalSystems.Laws UEOTQM.OperationalSystems.realModel ∧
        ¬ UEOTQM.OperationalSystems.LocalTomography UEOTQM.OperationalSystems.realModel) ∧
      (UEOTQM.OperationalSystems.Laws UEOTQM.OperationalSystems.complexModel ∧
        UEOTQM.OperationalSystems.PurificationExistence UEOTQM.OperationalSystems.complexModel ∧
        UEOTQM.OperationalSystems.LocalTomography UEOTQM.OperationalSystems.complexModel) := by
  exact ⟨UEOTQM.CorePurificationBoundary.finiteCoreSlice_holds,
    UEOTQM.OperationalSystems.core_first_marginal_no_purifies,
    ⟨UEOTQM.OperationalSystems.classical_laws, UEOTQM.OperationalSystems.classical_not_purification⟩,
    ⟨UEOTQM.OperationalSystems.real_laws, UEOTQM.OperationalSystems.real_not_localTomography⟩,
    ⟨UEOTQM.OperationalSystems.complex_laws,
      UEOTQM.OperationalSystems.complex_purification,
      UEOTQM.ComplexLocalTomography.complex_localTomography⟩⟩

end UEOTPhysicsUnification.GPTSelfDualConeReconstruction
