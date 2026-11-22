import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Open-System Lindblad Decoherence Budget, LOCC Non-Classicality Witness & Pre-Registered
# Blind-Holdout Pipeline for the Flat-Space Mesoscopic Gravimetric Protocol (`P-MESO-BMV-06`)

Pure-kernel Lean 4 formalization closing the theoretical open-system and empirical-contract layer
of `NEXT_GATE` Frontier 4 (`AH08` flat-space mesoscopic gravimetry + `HARDWARE_CERTIFICATION_CONTRACT.md`):

1. **Two-Packet $4 \times 4$ Stabilizer Algebra & Bose–Marletto–Vedral (BMV) Witness**:
   - `bmvWitnessOp_hermitian_and_stabilizer_spectrum`: On the two-qubit spatial-superposition space
     `Qubit2 := Fin 2 × Fin 2`, `W_BMV = I ⊗ I - X ⊗ X + Y ⊗ Z + Z ⊗ Y` is Hermitian, its three
     Pauli-tensor summands `A_1 = X ⊗ X`, `A_2 = -Y ⊗ Z`, `A_3 = -Z ⊗ Y` are commuting involutions
     with `A_1 * A_2 = A_3`, and `(W_BMV - 2) * (W_BMV + 2) = 0` (exact spectrum `{-2, +2}`).
2. **3D Cauchy–Schwarz Separable Bound & LOCC Mediator No-Go Theorem**:
   - `bmv_trace_product_bloch_exact`, `bloch_correlator_abs_le_one_of_cauchy_schwarz`,
     `locc_separable_mixture_bmv_witness_nonneg`, and `ktm_classical_dephased_gravity_witness_eq_one`:
     Every finite convex LOCC combination `∑_a p_a (ρ(r_a) ⊗ ρ(s_a))` of physical Bloch states
     (`‖r_a‖^2 ≤ 1, ‖s_a‖^2 ≤ 1`) satisfies `Im Tr(W_BMV ρ_LOCC) = 0` and `0 ≤ Re Tr(W_BMV ρ_LOCC)`
     by exact 3D Lagrange/Cauchy–Schwarz sum-of-squares, while a classical path-measuring
     Kafri–Taylor–Milburn channel yields `Tr(W_BMV ρ_KTM) = 1 ≥ 0`.
3. **Exact $4 \times 4$ Lindblad Dephased & Depolarized Gravitational Witness & Rate Threshold**:
   - `dephase2_commutes_with_gravUnitary`: Spatial-path Lindblad dephasing commutes identically
     with the diagonal gravitational phase unitary `U_grav(ϕ)`.
   - `bmv_depolarized_witness_trace_exact` & `bmv_dephased_witness_trace_exact`: Exact $4 \times 4$
     matrix traces `1 - ν^2 (cos^2(ϕ/2) + sin ϕ)` (local depolarizing) and
     `1 - ν^2 cos^2(ϕ/2) - ν sin ϕ` (spatial Lindblad pure dephasing).
   - `bmv_signal_gt_one_of_half_angle_window`, `bmv_lindblad_decoherence_rate_threshold_iff`, and
     `bmv_dephased_witness_le_depolarized_and_both_violate_locc`: Exact sub-horizon phase window
     `tan(ϕ/2) < 2 ⟹ cos^2(ϕ/2) + sin ϕ > 1` and exact Lindblad decoherence rate ceiling
     `Γ < log(cos^2(ϕ/2) + sin ϕ) / (2 T)` certifying strict non-LOCC entanglement (`W < 0`)
     simultaneously for both open-system channels.
4. **SPAM-Calibrated Differential Contrast & Pre-Registered Blind-Holdout Non-Vacuity**:
   - `noisy_differential_spam_offset_cancels`, `empirical_bmv_witness_confidence_certifies_non_locc`,
     and `no_vacuous_pass_on_empty_calibration_or_missing_raw_shots`.
-/

namespace UEOTPhysicsUnification.MesoscopicDecoherenceGravimetry

open Matrix
open scoped BigOperators

/-- Two-packet spatial-path Hilbert index `(i_1, i_2) ∈ Fin 2 × Fin 2`. -/
abbrev Qubit2 := Fin 2 × Fin 2

/-! ## 1. Single-Qubit Pauli Algebra, Kronecker Product & $4 \times 4$ BMV Stabilizer Witness -/

/-- Single-qubit identity matrix `I_2`. -/
def pauliI : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then 1 else 0

/-- Single-qubit Pauli `X` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then 0 else 1

/-- Single-qubit Pauli `Y` matrix. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i = 0 ∧ j = 1 then -Complex.I
    else if i = 1 ∧ j = 0 then Complex.I
    else 0

/-- Single-qubit Pauli `Z` matrix. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i = 0 ∧ j = 0 then 1
    else if i = 1 ∧ j = 1 then -1
    else 0

/-- Two-qubit Kronecker tensor product on `Qubit2 = Fin 2 × Fin 2`. -/
def kron (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Qubit2 Qubit2 ℂ :=
  fun p q => A p.1 q.1 * B p.2 q.2

theorem kron_mul (A B C D : Matrix (Fin 2) (Fin 2) ℂ) :
    kron A B * kron C D = kron (A * C) (B * D) := by
  ext p q
  simp only [kron, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem trace_kron (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (kron A B) = Matrix.trace A * Matrix.trace B := by
  simp only [Matrix.trace, Matrix.diag, kron, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem kron_conjTranspose (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (kron A B).conjTranspose = kron A.conjTranspose B.conjTranspose := by
  ext p q
  simp only [Matrix.conjTranspose_apply, kron, star_mul]
  ring

theorem kron_pauliI_eq_one :
    kron pauliI pauliI = (1 : Matrix Qubit2 Qubit2 ℂ) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [kron, pauliI]

/-- Commuting BMV stabilizer generators `A_1 = X ⊗ X`, `A_2 = -Y ⊗ Z`, `A_3 = -Z ⊗ Y`. -/
def stabA1 : Matrix Qubit2 Qubit2 ℂ := kron pauliX pauliX
def stabA2 : Matrix Qubit2 Qubit2 ℂ := -kron pauliY pauliZ
def stabA3 : Matrix Qubit2 Qubit2 ℂ := -kron pauliZ pauliY

/-- Bose–Marletto–Vedral / Tóth–Gühne $4 \times 4$ entanglement witness
`W_BMV = I ⊗ I - X ⊗ X + Y ⊗ Z + Z ⊗ Y`. -/
def bmvWitnessOp : Matrix Qubit2 Qubit2 ℂ :=
  kron pauliI pauliI - kron pauliX pauliX + kron pauliY pauliZ + kron pauliZ pauliY

private lemma pauli_mul_table :
    pauliX * pauliX = pauliI ∧
      pauliY * pauliY = pauliI ∧
      pauliZ * pauliZ = pauliI ∧
      pauliX * pauliY = Complex.I • pauliZ ∧
      pauliY * pauliX = (-Complex.I) • pauliZ ∧
      pauliX * pauliZ = (-Complex.I) • pauliY ∧
      pauliZ * pauliX = Complex.I • pauliY ∧
      pauliY * pauliZ = Complex.I • pauliX ∧
      pauliZ * pauliY = (-Complex.I) • pauliX := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, pauliI, pauliX, pauliY, pauliZ])

private lemma pauli_hermitian :
    pauliI.conjTranspose = pauliI ∧
      pauliX.conjTranspose = pauliX ∧
      pauliY.conjTranspose = pauliY ∧
      pauliZ.conjTranspose = pauliZ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, pauliI, pauliX, pauliY, pauliZ])

/-- `W_BMV` is Hermitian, its stabilizer components `A_1, A_2, A_3` are pairwise-commuting
involutions with `A_1 * A_2 = A_3`, and `W_BMV` satisfies the exact spectral polynomial
`(W_BMV - 2 I)(W_BMV + 2 I) = 0` (eigenvalues `{-2, +2}`). -/
theorem bmvWitnessOp_hermitian_and_stabilizer_spectrum :
    bmvWitnessOp.conjTranspose = bmvWitnessOp ∧
      stabA1 * stabA1 = 1 ∧
      stabA2 * stabA2 = 1 ∧
      stabA3 * stabA3 = 1 ∧
      stabA1 * stabA2 = stabA3 ∧
      stabA2 * stabA1 = stabA3 ∧
      stabA2 * stabA3 = stabA3 * stabA2 ∧
      (bmvWitnessOp - (2 : ℂ) • (1 : Matrix Qubit2 Qubit2 ℂ)) *
        (bmvWitnessOp + (2 : ℂ) • (1 : Matrix Qubit2 Qubit2 ℂ)) = 0 := by
  rcases pauli_mul_table with ⟨hxx, hyy, hzz, hxy, hyx, hxz, hzx, _hyz, _hzy⟩
  rcases pauli_hermitian with ⟨hiH, hxH, hyH, hzH⟩
  have hA1_sq : stabA1 * stabA1 = 1 := by
    unfold stabA1
    rw [kron_mul, hxx, kron_pauliI_eq_one]
  have hA2_sq : stabA2 * stabA2 = 1 := by
    unfold stabA2
    rw [neg_mul_neg, kron_mul, hyy, hzz, kron_pauliI_eq_one]
  have hA3_sq : stabA3 * stabA3 = 1 := by
    unfold stabA3
    rw [neg_mul_neg, kron_mul, hzz, hyy, kron_pauliI_eq_one]
  have h12 : stabA1 * stabA2 = stabA3 := by
    unfold stabA1 stabA2 stabA3
    rw [mul_neg, kron_mul, hxy, hxz]
    ext p q
    simp only [Matrix.neg_apply, kron, Matrix.smul_apply, smul_eq_mul]
    calc
      -(Complex.I * pauliZ p.1 q.1 * (-Complex.I * pauliY p.2 q.2))
        = (Complex.I * Complex.I) * (pauliZ p.1 q.1 * pauliY p.2 q.2) := by ring
      _ = -(pauliZ p.1 q.1 * pauliY p.2 q.2) := by rw [Complex.I_mul_I]; ring
  have h21 : stabA2 * stabA1 = stabA3 := by
    unfold stabA1 stabA2 stabA3
    rw [neg_mul, kron_mul, hyx, hzx]
    ext p q
    simp only [Matrix.neg_apply, kron, Matrix.smul_apply, smul_eq_mul]
    calc
      -(-Complex.I * pauliZ p.1 q.1 * (Complex.I * pauliY p.2 q.2))
        = (Complex.I * Complex.I) * (pauliZ p.1 q.1 * pauliY p.2 q.2) := by ring
      _ = -(pauliZ p.1 q.1 * pauliY p.2 q.2) := by rw [Complex.I_mul_I]; ring
  have h13 : stabA1 * stabA3 = stabA2 := by
    calc
      stabA1 * stabA3 = stabA1 * (stabA1 * stabA2) := by rw [← h12]
      _ = (stabA1 * stabA1) * stabA2 := (mul_assoc _ _ _).symm
      _ = stabA2 := by rw [hA1_sq, one_mul]
  have h31 : stabA3 * stabA1 = stabA2 := by
    calc
      stabA3 * stabA1 = (stabA2 * stabA1) * stabA1 := by rw [← h21]
      _ = stabA2 * (stabA1 * stabA1) := mul_assoc _ _ _
      _ = stabA2 := by rw [hA1_sq, mul_one]
  have h23 : stabA2 * stabA3 = stabA1 := by
    calc
      stabA2 * stabA3 = stabA2 * (stabA2 * stabA1) := by rw [← h21]
      _ = (stabA2 * stabA2) * stabA1 := (mul_assoc _ _ _).symm
      _ = stabA1 := by rw [hA2_sq, one_mul]
  have h32 : stabA3 * stabA2 = stabA1 := by
    calc
      stabA3 * stabA2 = (stabA1 * stabA2) * stabA2 := by rw [← h12]
      _ = stabA1 * (stabA2 * stabA2) := mul_assoc _ _ _
      _ = stabA1 := by rw [hA2_sq, mul_one]
  refine ⟨?_, hA1_sq, hA2_sq, hA3_sq, h12, h21, by rw [h23, h32], ?_⟩
  · unfold bmvWitnessOp
    simp only [conjTranspose_add, conjTranspose_sub, kron_conjTranspose, hiH, hxH, hyH, hzH]
  · have hw : bmvWitnessOp = (1 : Matrix Qubit2 Qubit2 ℂ) - stabA1 - stabA2 - stabA3 := by
      unfold bmvWitnessOp stabA1 stabA2 stabA3
      rw [kron_pauliI_eq_one]
      abel
    have htwo : (2 : ℂ) • (1 : Matrix Qubit2 Qubit2 ℂ) = 1 + 1 :=
      two_smul ℂ (1 : Matrix Qubit2 Qubit2 ℂ)
    rw [hw, htwo]
    calc
      ((1 : Matrix Qubit2 Qubit2 ℂ) - stabA1 - stabA2 - stabA3 - (1 + 1)) *
          ((1 : Matrix Qubit2 Qubit2 ℂ) - stabA1 - stabA2 - stabA3 + (1 + 1))
        = (stabA1 * stabA1 - 1) + (stabA2 * stabA2 - 1) + (stabA3 * stabA3 - 1) +
            (stabA1 * stabA2 - stabA3) + (stabA2 * stabA1 - stabA3) +
            (stabA1 * stabA3 - stabA2) + (stabA3 * stabA1 - stabA2) +
            (stabA2 * stabA3 - stabA1) + (stabA3 * stabA2 - stabA1) := by
            noncomm_ring
      _ = 0 := by
          rw [hA1_sq, hA2_sq, hA3_sq, h12, h21, h13, h31, h23, h32]
          abel

/-! ## 2. 3D Cauchy–Schwarz Separable Bound & LOCC Mediator No-Go Theorem -/

/-- Euclidean squared norm of a 3D Bloch vector `r : Fin 3 → ℝ`. -/
def blochNormSq (r : Fin 3 → ℝ) : ℝ :=
  (r 0) ^ 2 + (r 1) ^ 2 + (r 2) ^ 2

/-- Single-qubit Bloch density matrix `(1/2)(I + r_x X + r_y Y + r_z Z)`. -/
noncomputable def blochDensity (r : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / 2 : ℝ) : ℂ) •
    (pauliI + ((r 0 : ℝ) : ℂ) • pauliX + ((r 1 : ℝ) : ℂ) • pauliY + ((r 2 : ℝ) : ℂ) • pauliZ)

theorem blochDensity_hermitian_and_trace_one (r : Fin 3 → ℝ) :
    (blochDensity r).conjTranspose = blochDensity r ∧
      Matrix.trace (blochDensity r) = 1 := by
  rcases pauli_hermitian with ⟨hiH, hxH, hyH, hzH⟩
  constructor
  · unfold blochDensity
    simp [conjTranspose_smul, conjTranspose_add, hiH, hxH, hyH, hzH]
  · unfold blochDensity
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.smul_apply, Matrix.add_apply,
      pauliI, pauliX, pauliY, pauliZ, smul_eq_mul]
    norm_num
    ring

private lemma trace_pauli_mul_blochDensity (r : Fin 3 → ℝ) :
    Matrix.trace (pauliI * blochDensity r) = 1 ∧
      Matrix.trace (pauliX * blochDensity r) = ((r 0 : ℝ) : ℂ) ∧
      Matrix.trace (pauliY * blochDensity r) = ((r 1 : ℝ) : ℂ) ∧
      Matrix.trace (pauliZ * blochDensity r) = ((r 2 : ℝ) : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold blochDensity;
     simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
       Matrix.smul_apply, Matrix.add_apply, pauliI, pauliX, pauliY, pauliZ, smul_eq_mul];
     norm_num;
     ring_nf;
     try simp only [Complex.I_sq];
     try ring)

/-- Exact $4 \times 4$ matrix trace of `W_BMV` against any two-qubit product Bloch state
`ρ(r) ⊗ ρ(s)`: `Tr(W_BMV (ρ(r) ⊗ ρ(s))) = 1 - (r_0 s_0 - r_1 s_2 - r_2 s_1)`. -/
theorem bmv_trace_product_bloch_exact (r s : Fin 3 → ℝ) :
    Matrix.trace (bmvWitnessOp * kron (blochDensity r) (blochDensity s)) =
      ((1 - (r 0 * s 0 - r 1 * s 2 - r 2 * s 1) : ℝ) : ℂ) := by
  rcases trace_pauli_mul_blochDensity r with ⟨hIr, hXr, hYr, hZr⟩
  rcases trace_pauli_mul_blochDensity s with ⟨hIs, hXs, hYs, hZs⟩
  unfold bmvWitnessOp
  simp only [add_mul, sub_mul, Matrix.trace_add, Matrix.trace_sub, kron_mul, trace_kron,
    hIr, hXr, hYr, hZr, hIs, hXs, hYs, hZs]
  push_cast
  ring

/-- 3D Cauchy–Schwarz / Lagrange sum-of-squares bound on physical Bloch balls:
whenever `‖r‖^2 ≤ 1` and `‖s‖^2 ≤ 1`, `|r_0 s_0 - r_1 s_2 - r_2 s_1| ≤ 1` and
`0 ≤ 1 - (r_0 s_0 - r_1 s_2 - r_2 s_1)`. -/
theorem bloch_correlator_abs_le_one_of_cauchy_schwarz
    {r s : Fin 3 → ℝ} (hr : blochNormSq r ≤ 1) (hs : blochNormSq s ≤ 1) :
    |r 0 * s 0 - r 1 * s 2 - r 2 * s 1| ≤ 1 ∧
      0 ≤ 1 - (r 0 * s 0 - r 1 * s 2 - r 2 * s 1) := by
  have hlagrange :
      (r 0 * s 0 - r 1 * s 2 - r 2 * s 1) ^ 2 +
        (r 0 * s 2 + r 1 * s 0) ^ 2 +
        (r 0 * s 1 + r 2 * s 0) ^ 2 +
        (r 1 * s 1 - r 2 * s 2) ^ 2 =
      blochNormSq r * blochNormSq s := by
    unfold blochNormSq
    ring
  have hprod_le : blochNormSq r * blochNormSq s ≤ 1 := by
    calc
      blochNormSq r * blochNormSq s ≤ 1 * 1 :=
        mul_le_mul hr hs (by unfold blochNormSq; positivity) (by norm_num)
      _ = 1 := by norm_num
  have hsq_le : (r 0 * s 0 - r 1 * s 2 - r 2 * s 1) ^ 2 ≤ 1 ^ 2 := by
    have hrem : 0 ≤ (r 0 * s 2 + r 1 * s 0) ^ 2 + (r 0 * s 1 + r 2 * s 0) ^ 2 +
        (r 1 * s 1 - r 2 * s 2) ^ 2 := by positivity
    nlinarith [hlagrange, hprod_le, hrem]
  have habs : |r 0 * s 0 - r 1 * s 2 - r 2 * s 1| ≤ 1 := by
    simpa using sq_le_sq.mp hsq_le
  exact ⟨habs, by linarith [(abs_le.mp habs).2]⟩

/-- Finite convex LOCC separable ensemble `ρ_LOCC = ∑_a p_a (ρ(r_a) ⊗ ρ(s_a))`. -/
noncomputable def loccState {m : ℕ} (p : Fin m → ℝ) (r s : Fin m → Fin 3 → ℝ) :
    Matrix Qubit2 Qubit2 ℂ :=
  ∑ a : Fin m, ((p a : ℝ) : ℂ) • kron (blochDensity (r a)) (blochDensity (s a))

/-- **LOCC / Classical Gravitational Mediator No-Go Theorem**:
For every finite convex combination of two-packet separable Bloch states (`p_a ≥ 0`, `∑_a p_a = 1`,
`‖r_a‖^2 ≤ 1`, `‖s_a‖^2 ≤ 1`), `ρ_LOCC` has unit trace and its $4 \times 4$ BMV witness expectation
is real and non-negative (`Re Tr(W_BMV ρ_LOCC) ≥ 0`). -/
theorem locc_separable_mixture_bmv_witness_nonneg
    {m : ℕ} (p : Fin m → ℝ) (r s : Fin m → Fin 3 → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a) (hp_sum : (∑ a, p a) = 1)
    (hr : ∀ a, blochNormSq (r a) ≤ 1) (hs : ∀ a, blochNormSq (s a) ≤ 1) :
    Matrix.trace (loccState p r s) = 1 ∧
      (Matrix.trace (bmvWitnessOp * loccState p r s)).im = 0 ∧
      0 ≤ (Matrix.trace (bmvWitnessOp * loccState p r s)).re := by
  refine ⟨?_, ?_⟩
  · unfold loccState
    rw [Matrix.trace_sum]
    have hterm : ∀ a : Fin m,
        Matrix.trace (((p a : ℝ) : ℂ) • kron (blochDensity (r a)) (blochDensity (s a))) =
          ((p a : ℝ) : ℂ) := by
      intro a
      rw [Matrix.trace_smul, trace_kron, (blochDensity_hermitian_and_trace_one (r a)).2,
        (blochDensity_hermitian_and_trace_one (s a)).2]
      simp
    simp_rw [hterm]
    rw [← Complex.ofReal_sum, hp_sum, Complex.ofReal_one]
  · unfold loccState
    rw [Matrix.mul_sum, Matrix.trace_sum]
    have hterm : ∀ a : Fin m,
        Matrix.trace (bmvWitnessOp * (((p a : ℝ) : ℂ) • kron (blochDensity (r a)) (blochDensity (s a)))) =
          ((p a * (1 - (r a 0 * s a 0 - r a 1 * s a 2 - r a 2 * s a 1)) : ℝ) : ℂ) := by
      intro a
      rw [Matrix.mul_smul, Matrix.trace_smul, bmv_trace_product_bloch_exact]
      simp [Complex.ofReal_mul]
    simp_rw [hterm, ← Complex.ofReal_sum, Complex.ofReal_im, Complex.ofReal_re, true_and]
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (hp_nonneg a) (bloch_correlator_abs_le_one_of_cauchy_schwarz (hr a) (hs a)).2

/-! ## 3. Open-System Lindblad Gravitational Channels & Exact $4 \times 4$ Witness Violation -/

/-- Diagonal gravitational interaction unitary `U_grav(ϕ) = diag(1, 1, 1, e^{i ϕ})`. -/
noncomputable def gravUnitary (phi : ℝ) : Matrix Qubit2 Qubit2 ℂ :=
  Matrix.diagonal (fun p =>
    if p = (1, 1) then Complex.exp ((phi : ℂ) * Complex.I) else 1)

/-- Coherent two-packet BMV state vector `|ψ(ϕ)⟩ = (1/2)(|00⟩ + |01⟩ + |10⟩ + e^{i ϕ}|11⟩)`. -/
noncomputable def bmvVec (phi : ℝ) : Qubit2 → ℂ :=
  fun p =>
    if p = (1, 1) then (1 / 2 : ℂ) * Complex.exp ((phi : ℂ) * Complex.I)
    else (1 / 2 : ℂ)

/-- Pure $4 \times 4$ BMV gravitational density matrix `|ψ(ϕ)⟩⟨ψ(ϕ)|`. -/
noncomputable def bmvPureRho (phi : ℝ) : Matrix Qubit2 Qubit2 ℂ :=
  fun p q => bmvVec phi p * star (bmvVec phi q)

/-- Two-packet spatial-path Lindblad pure-dephasing CPTP channel `E_ν^Z ⊗ E_ν^Z`
(`ν = e^{-Γ T} ∈ [0, 1]`). -/
noncomputable def dephase2 (nu : ℝ) (ρ : Matrix Qubit2 Qubit2 ℂ) : Matrix Qubit2 Qubit2 ℂ :=
  let w0 : ℂ := (((1 + nu) / 2 : ℝ) : ℂ)
  let w1 : ℂ := (((1 - nu) / 2 : ℝ) : ℂ)
  (w0 * w0) • ρ +
    (w0 * w1) • (kron pauliI pauliZ * ρ * kron pauliI pauliZ) +
    (w1 * w0) • (kron pauliZ pauliI * ρ * kron pauliZ pauliI) +
    (w1 * w1) • (kron pauliZ pauliZ * ρ * kron pauliZ pauliZ)

private lemma kron_Z_diagonal :
    kron pauliI pauliZ = Matrix.diagonal (fun p : Qubit2 => if p.2 = 0 then (1 : ℂ) else -1) ∧
      kron pauliZ pauliI = Matrix.diagonal (fun p : Qubit2 => if p.1 = 0 then (1 : ℂ) else -1) ∧
      kron pauliZ pauliZ =
        Matrix.diagonal (fun p : Qubit2 =>
          (if p.1 = 0 then (1 : ℂ) else -1) * (if p.2 = 0 then (1 : ℂ) else -1)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (ext ⟨i1, i2⟩ ⟨j1, j2⟩;
     fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
       simp [kron, pauliI, pauliZ])

private lemma diag_sandwich_apply (d1 d2 : Qubit2 → ℂ) (M : Matrix Qubit2 Qubit2 ℂ)
    (p q : Qubit2) :
    (Matrix.diagonal d1 * M * Matrix.diagonal d2) p q = d1 p * M p q * d2 q := by
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- Simultaneous continuous-time gravitational phase evolution and spatial-path Lindblad dephasing
commute identically because `U_grav(ϕ)` and `Z_1, Z_2` are jointly diagonal in the spatial path basis. -/
theorem dephase2_commutes_with_gravUnitary (nu phi : ℝ) (ρ : Matrix Qubit2 Qubit2 ℂ) :
    dephase2 nu (gravUnitary phi * ρ * (gravUnitary phi).conjTranspose) =
      gravUnitary phi * dephase2 nu ρ * (gravUnitary phi).conjTranspose := by
  rcases kron_Z_diagonal with ⟨hIZ, hZI, hZZ⟩
  have hUdag : (gravUnitary phi).conjTranspose =
      Matrix.diagonal (fun p : Qubit2 =>
        star (if p = (1, 1) then Complex.exp ((phi : ℂ) * Complex.I) else 1)) := by
    unfold gravUnitary
    ext p q
    by_cases hpq : p = q
    · subst hpq; simp
    · simp [Matrix.conjTranspose_apply, hpq, Ne.symm hpq]
  ext p q
  unfold dephase2
  rw [hIZ, hZI, hZZ, hUdag]
  unfold gravUnitary
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, diag_sandwich_apply]
  ring

/-- Indexed single-qubit Pauli basis `(I, X, Y, Z)` and single-qubit depolarizing Pauli-twirl weights. -/
def pauliBasis : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => pauliI
  | 1 => pauliX
  | 2 => pauliY
  | 3 => pauliZ

noncomputable def depolWeight (nu : ℝ) : Fin 4 → ℂ
  | 0 => (((1 + 3 * nu) / 4 : ℝ) : ℂ)
  | _ => (((1 - nu) / 4 : ℝ) : ℂ)

/-- Two-packet local isotropic depolarizing CPTP channel `D_ν ⊗ D_ν`. -/
noncomputable def depol2 (nu : ℝ) (ρ : Matrix Qubit2 Qubit2 ℂ) : Matrix Qubit2 Qubit2 ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4,
    (depolWeight nu a * depolWeight nu b) •
      (kron (pauliBasis a) (pauliBasis b) * ρ * kron (pauliBasis a) (pauliBasis b))

private noncomputable def depolDual1 (nu : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ a : Fin 4, depolWeight nu a • (pauliBasis a * P * pauliBasis a)

private lemma depolDual1_pauli (nu : ℝ) :
    depolDual1 nu pauliI = pauliI ∧
      depolDual1 nu pauliX = ((nu : ℝ) : ℂ) • pauliX ∧
      depolDual1 nu pauliY = ((nu : ℝ) : ℂ) • pauliY ∧
      depolDual1 nu pauliZ = ((nu : ℝ) : ℂ) • pauliZ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [depolDual1, Fin.sum_univ_four, depolWeight, pauliBasis,
        Matrix.mul_apply, Fin.sum_univ_two, pauliI, pauliX, pauliY, pauliZ] <;> ring)

private lemma trace_kron_mul_depol2 (nu : ℝ) (P Q : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix Qubit2 Qubit2 ℂ) :
    Matrix.trace (kron P Q * depol2 nu ρ) =
      Matrix.trace (kron (depolDual1 nu P) (depolDual1 nu Q) * ρ) := by
  unfold depol2
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul]
  have hcyc : ∀ a b : Fin 4,
      Matrix.trace (kron P Q * (kron (pauliBasis a) (pauliBasis b) * ρ * kron (pauliBasis a) (pauliBasis b))) =
        Matrix.trace ((kron (pauliBasis a) (pauliBasis b) * kron P Q * kron (pauliBasis a) (pauliBasis b)) * ρ) := by
    intro a b
    rw [← Matrix.mul_assoc (kron P Q), Matrix.trace_mul_cycle (kron P Q)
      (kron (pauliBasis a) (pauliBasis b) * ρ) (kron (pauliBasis a) (pauliBasis b))]
    simp only [Matrix.mul_assoc]
  have hexpand : kron (depolDual1 nu P) (depolDual1 nu Q) =
      ∑ a : Fin 4, ∑ b : Fin 4,
        (depolWeight nu a * depolWeight nu b) •
          kron (pauliBasis a * P * pauliBasis a) (pauliBasis b * Q * pauliBasis b) := by
    ext p q
    simp only [kron, depolDual1, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => by ring)
  rw [hexpand, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Matrix.smul_mul, Matrix.trace_smul, hcyc a b, kron_mul, kron_mul]

private noncomputable def dephaseDual1 (nu : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (((1 + nu) / 2 : ℝ) : ℂ) • P + (((1 - nu) / 2 : ℝ) : ℂ) • (pauliZ * P * pauliZ)

private lemma dephaseDual1_pauli (nu : ℝ) :
    dephaseDual1 nu pauliI = pauliI ∧
      dephaseDual1 nu pauliX = ((nu : ℝ) : ℂ) • pauliX ∧
      dephaseDual1 nu pauliY = ((nu : ℝ) : ℂ) • pauliY ∧
      dephaseDual1 nu pauliZ = pauliZ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [dephaseDual1, Matrix.mul_apply, Fin.sum_univ_two, pauliI, pauliX, pauliY, pauliZ] <;> ring)

private lemma trace_kron_mul_dephase2 (nu : ℝ) (P Q : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix Qubit2 Qubit2 ℂ) :
    Matrix.trace (kron P Q * dephase2 nu ρ) =
      Matrix.trace (kron (dephaseDual1 nu P) (dephaseDual1 nu Q) * ρ) := by
  unfold dephase2
  have hcyc : ∀ K : Matrix Qubit2 Qubit2 ℂ,
      Matrix.trace (kron P Q * (K * ρ * K)) = Matrix.trace ((K * kron P Q * K) * ρ) := by
    intro K
    rw [← Matrix.mul_assoc (kron P Q), Matrix.trace_mul_cycle (kron P Q) (K * ρ) K]
    simp only [Matrix.mul_assoc]
  have hI : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, pauliI * M * pauliI = M := by
    intro M; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, pauliI]
  have hexpand : kron (dephaseDual1 nu P) (dephaseDual1 nu Q) =
      ((((1 + nu) / 2 : ℝ) : ℂ) * (((1 + nu) / 2 : ℝ) : ℂ)) • kron P Q +
      ((((1 + nu) / 2 : ℝ) : ℂ) * (((1 - nu) / 2 : ℝ) : ℂ)) • kron P (pauliZ * Q * pauliZ) +
      ((((1 - nu) / 2 : ℝ) : ℂ) * (((1 + nu) / 2 : ℝ) : ℂ)) • kron (pauliZ * P * pauliZ) Q +
      ((((1 - nu) / 2 : ℝ) : ℂ) * (((1 - nu) / 2 : ℝ) : ℂ)) •
        kron (pauliZ * P * pauliZ) (pauliZ * Q * pauliZ) := by
    ext p q
    simp only [kron, dephaseDual1, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hexpand]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, hcyc, kron_mul, hI]

private lemma trace_bmvPureRho_correlators (phi : ℝ) :
    Matrix.trace (kron pauliI pauliI * bmvPureRho phi) = 1 ∧
      Matrix.trace (kron pauliX pauliX * bmvPureRho phi) = ((Real.cos (phi / 2) ^ 2 : ℝ) : ℂ) ∧
      Matrix.trace (kron pauliY pauliZ * bmvPureRho phi) = ((- (Real.sin phi / 2) : ℝ) : ℂ) ∧
      Matrix.trace (kron pauliZ pauliY * bmvPureRho phi) = ((- (Real.sin phi / 2) : ℝ) : ℂ) := by
  have hexp : Complex.exp ((phi : ℂ) * Complex.I) =
      ((Real.cos phi : ℝ) : ℂ) + ((Real.sin phi : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hcs_c : ((Real.cos phi : ℝ) : ℂ) ^ 2 + ((Real.sin phi : ℝ) : ℂ) ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) (Real.cos_sq_add_sin_sq phi)
    simpa only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one] using h
  have hcos_half_c : (1 + ((Real.cos phi : ℝ) : ℂ)) / 2 = ((Real.cos (phi / 2) : ℝ) : ℂ) ^ 2 := by
    have h := Real.cos_sq (phi / 2)
    have h2 : 2 * (phi / 2) = phi := by ring
    rw [h2] at h
    have hc := congrArg (fun x : ℝ => (x : ℂ)) h
    simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_one, Complex.ofReal_ofNat] at hc
    linear_combination -hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      kron, pauliI, bmvPureRho, bmvVec]
    norm_num [Prod.mk.injEq]
    rw [hexp]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    simp only [Complex.I_sq]
    linear_combination (1 / 4 : ℂ) * hcs_c
  · have hgoal_rhs : (((Real.cos (phi / 2) ^ 2 : ℝ) : ℂ)) = ((Real.cos (phi / 2) : ℝ) : ℂ) ^ 2 :=
      Complex.ofReal_pow _ 2
    have hphi2 : (phi : ℂ) / 2 = ((phi / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hgoal_rhs]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      kron, pauliX, bmvPureRho, bmvVec]
    norm_num [Prod.mk.injEq]
    rw [hexp, hphi2, ← Complex.ofReal_cos]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    linear_combination hcos_half_c
  · have hgoal_rhs : (((-(Real.sin phi / 2) : ℝ) : ℂ)) = -(((Real.sin phi : ℝ) : ℂ) / 2) := by
      simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [hgoal_rhs]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      kron, pauliY, pauliZ, bmvPureRho, bmvVec]
    norm_num [Prod.mk.injEq]
    rw [hexp]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.ofReal_sin]
    ring_nf
    simp only [Complex.I_sq]
    ring
  · have hgoal_rhs : (((-(Real.sin phi / 2) : ℝ) : ℂ)) = -(((Real.sin phi : ℝ) : ℂ) / 2) := by
      simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [hgoal_rhs]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      kron, pauliZ, pauliY, bmvPureRho, bmvVec]
    norm_num [Prod.mk.injEq]
    rw [hexp]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.ofReal_sin]
    ring_nf
    simp only [Complex.I_sq]
    ring

private lemma kron_smul_left_right (a b : ℂ) (P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    kron (a • P) (b • Q) = (a * b) • kron P Q := by
  ext p q
  simp [kron]
  ring

/-- **Exact $4 \times 4$ Depolarized BMV Gravitational Witness Expectation**:
Under local depolarizing visibility `ν ∈ ℝ` on both packets,
`Tr(W_BMV (D_ν ⊗ D_ν)(|ψ(ϕ)⟩⟨ψ(ϕ)|)) = 1 - ν^2 (cos^2(ϕ/2) + sin ϕ)`. -/
theorem bmv_depolarized_witness_trace_exact (nu phi : ℝ) :
    Matrix.trace (bmvWitnessOp * depol2 nu (bmvPureRho phi)) =
      ((1 - nu ^ 2 * (Real.cos (phi / 2) ^ 2 + Real.sin phi) : ℝ) : ℂ) := by
  rcases depolDual1_pauli nu with ⟨hI, hX, hY, hZ⟩
  rcases trace_bmvPureRho_correlators phi with ⟨tII, tXX, tYZ, tZY⟩
  unfold bmvWitnessOp
  simp only [add_mul, sub_mul, Matrix.trace_add, Matrix.trace_sub, trace_kron_mul_depol2,
    hI, hX, hY, hZ, kron_smul_left_right, Matrix.smul_mul, Matrix.trace_smul,
    tII, tXX, tYZ, tZY, smul_eq_mul]
  push_cast
  ring

/-- **Exact $4 \times 4$ Spatial-Lindblad Pure-Dephased BMV Gravitational Witness Expectation**:
Under spatial-path Lindblad pure dephasing `ν = e^{-Γ T}` on both packets,
`Tr(W_BMV (E_ν^Z ⊗ E_ν^Z)(|ψ(ϕ)⟩⟨ψ(ϕ)|)) = 1 - ν^2 cos^2(ϕ/2) - ν sin ϕ`. -/
theorem bmv_dephased_witness_trace_exact (nu phi : ℝ) :
    Matrix.trace (bmvWitnessOp * dephase2 nu (bmvPureRho phi)) =
      ((1 - nu ^ 2 * Real.cos (phi / 2) ^ 2 - nu * Real.sin phi : ℝ) : ℂ) := by
  rcases dephaseDual1_pauli nu with ⟨hI, hX, hY, hZ⟩
  rcases trace_bmvPureRho_correlators phi with ⟨tII, tXX, tYZ, tZY⟩
  have h1Y : kron (((nu : ℝ) : ℂ) • pauliY) pauliZ = ((nu : ℝ) : ℂ) • kron pauliY pauliZ := by
    simpa using kron_smul_left_right ((nu : ℝ) : ℂ) 1 pauliY pauliZ
  have hZ1 : kron pauliZ (((nu : ℝ) : ℂ) • pauliY) = ((nu : ℝ) : ℂ) • kron pauliZ pauliY := by
    simpa using kron_smul_left_right 1 ((nu : ℝ) : ℂ) pauliZ pauliY
  unfold bmvWitnessOp
  simp only [add_mul, sub_mul, Matrix.trace_add, Matrix.trace_sub, trace_kron_mul_dephase2,
    hI, hX, hY, hZ]
  rw [kron_smul_left_right, h1Y, hZ1]
  simp only [Matrix.smul_mul, Matrix.trace_smul, tII, tXX, tYZ, tZY, smul_eq_mul]
  push_cast
  ring

/-- Kafri–Taylor–Milburn / full classical path-measurement limit (`ν = 0`):
complete which-path decoherence yields `Tr(W_BMV ρ_deph(0, ϕ)) = 1 ≥ 0` for all `ϕ`. -/
theorem ktm_classical_dephased_gravity_witness_eq_one (phi : ℝ) :
    Matrix.trace (bmvWitnessOp * dephase2 0 (bmvPureRho phi)) = 1 := by
  rw [bmv_dephased_witness_trace_exact]
  norm_num

/-- **Coherent Gravitational Phase Window (`tan(ϕ/2) < 2`)**:
Whenever `0 < sin(ϕ/2)` and `sin(ϕ/2) < 2 cos(ϕ/2)` (holding across `ϕ ∈ (0, 2 arctan 2)`,
including `AH08`'s `Δϕ_grav ≈ 0.3164 rad`), `1 < cos^2(ϕ/2) + sin ϕ`. -/
theorem bmv_signal_gt_one_of_half_angle_window
    {phi : ℝ} (hsin_pos : 0 < Real.sin (phi / 2))
    (htan_lt_two : Real.sin (phi / 2) < 2 * Real.cos (phi / 2)) :
    1 < Real.cos (phi / 2) ^ 2 + Real.sin phi := by
  have hcs : Real.cos (phi / 2) ^ 2 + Real.sin (phi / 2) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq (phi / 2)
  have hsin2 : Real.sin phi = 2 * Real.sin (phi / 2) * Real.cos (phi / 2) := by
    have h2 : phi = 2 * (phi / 2) := by ring
    conv_lhs => rw [h2]
    exact Real.sin_two_mul (phi / 2)
  have hid : Real.cos (phi / 2) ^ 2 + Real.sin phi =
      1 + Real.sin (phi / 2) * (2 * Real.cos (phi / 2) - Real.sin (phi / 2)) := by
    nlinarith [hcs, hsin2]
  have hdiff_pos : 0 < 2 * Real.cos (phi / 2) - Real.sin (phi / 2) := by linarith
  have hprod_pos : 0 < Real.sin (phi / 2) * (2 * Real.cos (phi / 2) - Real.sin (phi / 2)) :=
    mul_pos hsin_pos hdiff_pos
  linarith

/-- Necessary and sufficient threshold for strict negativity (`< 0`) of the depolarized
BMV witness expectation: `Re Tr(W_BMV ρ_depol(ν, ϕ)) < 0 ↔ 1 < ν^2 (cos^2(ϕ/2) + sin ϕ)`. -/
theorem bmv_depolarized_witness_neg_iff_threshold (nu phi : ℝ) :
    (Matrix.trace (bmvWitnessOp * depol2 nu (bmvPureRho phi))).re < 0 ↔
      1 < nu ^ 2 * (Real.cos (phi / 2) ^ 2 + Real.sin phi) := by
  rw [bmv_depolarized_witness_trace_exact, Complex.ofReal_re]
  constructor <;> intro h <;> linarith

/-- **Exact Lindblad Decoherence Rate Ceiling (`Γ < log(cos^2(ϕ/2) + sin ϕ) / (2 T)`)**:
For coherent interaction time `T > 0` and phase satisfying `1 < cos^2(ϕ/2) + sin ϕ`,
`Re Tr(W_BMV ρ_depol(e^{-Γ T}, ϕ)) < 0 ↔ Γ < log(cos^2(ϕ/2) + sin ϕ) / (2 T)`. -/
theorem bmv_lindblad_decoherence_rate_threshold_iff
    {Gamma T phi : ℝ} (hT : 0 < T)
    (hsig : 1 < Real.cos (phi / 2) ^ 2 + Real.sin phi) :
    (Matrix.trace (bmvWitnessOp * depol2 (Real.exp (-Gamma * T)) (bmvPureRho phi))).re < 0 ↔
      Gamma < Real.log (Real.cos (phi / 2) ^ 2 + Real.sin phi) / (2 * T) := by
  rw [bmv_depolarized_witness_neg_iff_threshold]
  set S := Real.cos (phi / 2) ^ 2 + Real.sin phi
  have hS_pos : 0 < S := by linarith
  have hexp_sq : Real.exp (-Gamma * T) ^ 2 = Real.exp (-(2 * Gamma * T)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp_sq]
  have h2T_pos : 0 < 2 * T := by positivity
  constructor
  · intro hgt
    have hexp_lt : Real.exp (2 * Gamma * T) < S := by
      have hpos_e : 0 < Real.exp (2 * Gamma * T) := Real.exp_pos _
      have hmul := mul_lt_mul_of_pos_left hgt hpos_e
      have hcancel : Real.exp (2 * Gamma * T) * (Real.exp (-(2 * Gamma * T)) * S) = S := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      simpa [hcancel] using hmul
    have hlog : 2 * Gamma * T < Real.log S := by
      have hl := Real.log_lt_log (Real.exp_pos _) hexp_lt
      rwa [Real.log_exp] at hl
    exact (lt_div_iff₀ h2T_pos).mpr (by linarith)
  · intro hlt
    have h2GT : 2 * Gamma * T < Real.log S := by
      have h := (lt_div_iff₀ h2T_pos).mp hlt
      linarith
    have hexp_lt : Real.exp (2 * Gamma * T) < S := by
      have he := Real.exp_lt_exp.mpr h2GT
      rwa [Real.exp_log hS_pos] at he
    have hpos_neg : 0 < Real.exp (-(2 * Gamma * T)) := Real.exp_pos _
    have hmul := mul_lt_mul_of_pos_left hexp_lt hpos_neg
    have hcancel : Real.exp (-(2 * Gamma * T)) * Real.exp (2 * Gamma * T) = 1 := by
      rw [← Real.exp_add]
      simp
    simpa [hcancel] using hmul

/-- **Dominance & Non-LOCC Entanglement Certification Across Both Open-System Channels**:
For `ν ∈ [0, 1]` and `0 ≤ sin ϕ`, pure spatial dephasing achieves an even more negative witness
expectation than isotropic depolarizing (`W_deph ≤ W_depol`), so `Γ < log(cos^2(ϕ/2) + sin ϕ)/(2T)`
certifies strict LOCC violation (`< 0`, disjoint from every `loccState`) for **both** channels. -/
theorem bmv_dephased_witness_le_depolarized_and_both_violate_locc
    {Gamma T phi : ℝ} (hGamma : 0 ≤ Gamma) (hT : 0 < T)
    (hsin_nonneg : 0 ≤ Real.sin phi)
    (hsig : 1 < Real.cos (phi / 2) ^ 2 + Real.sin phi)
    (hrate : Gamma < Real.log (Real.cos (phi / 2) ^ 2 + Real.sin phi) / (2 * T)) :
    let nu := Real.exp (-Gamma * T)
    (Matrix.trace (bmvWitnessOp * dephase2 nu (bmvPureRho phi))).re ≤
        (Matrix.trace (bmvWitnessOp * depol2 nu (bmvPureRho phi))).re ∧
      (Matrix.trace (bmvWitnessOp * depol2 nu (bmvPureRho phi))).re < 0 ∧
      (Matrix.trace (bmvWitnessOp * dephase2 nu (bmvPureRho phi))).re < 0 := by
  intro nu
  have hnu_nonneg : 0 ≤ nu := le_of_lt (Real.exp_pos _)
  have hnu_le_one : nu ≤ 1 := by
    dsimp [nu]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hnu_sq_le : nu ^ 2 ≤ nu := by nlinarith
  have hle : (Matrix.trace (bmvWitnessOp * dephase2 nu (bmvPureRho phi))).re ≤
      (Matrix.trace (bmvWitnessOp * depol2 nu (bmvPureRho phi))).re := by
    rw [bmv_dephased_witness_trace_exact, bmv_depolarized_witness_trace_exact,
      Complex.ofReal_re, Complex.ofReal_re]
    have hmul : nu ^ 2 * Real.sin phi ≤ nu * Real.sin phi :=
      mul_le_mul_of_nonneg_right hnu_sq_le hsin_nonneg
    linarith
  have hneg_depol : (Matrix.trace (bmvWitnessOp * depol2 nu (bmvPureRho phi))).re < 0 :=
    (bmv_lindblad_decoherence_rate_threshold_iff hT hsig).mpr hrate
  exact ⟨hle, hneg_depol, lt_of_le_of_lt hle hneg_depol⟩

/-! ## 4. SPAM-Calibrated Contrast & Pre-Registered Blind-Holdout Contract (`HARDWARE_CERTIFICATION_CONTRACT.md`) -/

/-- Observed bright-outcome probability under non-computational leakage `leak` and asymmetric SPAM `(e0, e1)`. -/
def observedBrightProb (leak e0 e1 p1 : ℝ) : ℝ :=
  (1 - leak) * (e0 + (1 - e0 - e1) * p1)

/-- In the differential `±Δϕ_grav` protocol with dephasing visibility `ν`, the asymmetric SPAM
offset `(1 - leak) * e0` cancels identically, leaving exact contrast `(1 - leak)(1 - e0 - e1) ν sin ϕ`. -/
theorem noisy_differential_spam_offset_cancels (leak e0 e1 nu phi : ℝ) :
    observedBrightProb leak e0 e1 ((1 + nu * Real.sin phi) / 2) -
        observedBrightProb leak e0 e1 ((1 - nu * Real.sin phi) / 2) =
      (1 - leak) * (1 - e0 - e1) * nu * Real.sin phi := by
  unfold observedBrightProb
  ring

/-- Soundness of finite-shot SPAM-calibrated BMV witness certification: if each empirical Pauli
correlator estimator lies within `ε_α` of its true expectation and the empirical upper bound is `< 0`,
then the true quantum state strictly violates `0 ≤ W`. -/
theorem empirical_bmv_witness_confidence_certifies_non_locc
    {cXX cYZ cZY cXX_hat cYZ_hat cZY_hat epsXX epsYZ epsZY : ℝ}
    (hXX : |cXX_hat - cXX| ≤ epsXX)
    (hYZ : |cYZ_hat - cYZ| ≤ epsYZ)
    (hZY : |cZY_hat - cZY| ≤ epsZY)
    (hcert : (1 - cXX_hat + cYZ_hat + cZY_hat) + (epsXX + epsYZ + epsZY) < 0) :
    1 - cXX + cYZ + cZY < 0 := by
  have h1 := (abs_le.mp hXX).2
  have h2 := (abs_le.mp hYZ).1
  have h3 := (abs_le.mp hZY).1
  linarith

/-- Pre-registered hardware submission record matching `HARDWARE_CERTIFICATION_CONTRACT.md` §§2–3. -/
structure PreRegisteredHardwareSubmission where
  rawShotsComplete : Bool
  calibrationPolytopeNonEmpty : Bool
  singleEventPowerPassed : Bool
  holdoutBlindedAndPassed : Bool
  holdoutWitnessUpper95 : ℝ

/-- Decidable hardware certification gate: requires complete nonselective raw shot logs,
non-empty calibration confidence polytope (preventing vacuous pass), discrimination power,
blinded holdout pass, and strict upper-confidence violation `< 0` of the LOCC baseline. -/
noncomputable def deviceCertified (sub : PreRegisteredHardwareSubmission) : Bool :=
  sub.rawShotsComplete &&
    sub.calibrationPolytopeNonEmpty &&
    sub.singleEventPowerPassed &&
    sub.holdoutBlindedAndPassed &&
    decide (sub.holdoutWitnessUpper95 < 0)

/-- Non-vacuity and scope-honesty theorem: absent raw device shots (`rawShotsComplete = false`),
or on an empty calibration region (`calibrationPolytopeNonEmpty = false`), or whenever the
LOCC witness upper bound is `≥ 0`, `deviceCertified` evaluates strictly to `false`. -/
theorem no_vacuous_pass_on_empty_calibration_or_missing_raw_shots
    (sub : PreRegisteredHardwareSubmission) :
    (sub.rawShotsComplete = false → deviceCertified sub = false) ∧
      (sub.calibrationPolytopeNonEmpty = false → deviceCertified sub = false) ∧
      (0 ≤ sub.holdoutWitnessUpper95 → deviceCertified sub = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; simp [deviceCertified, h]
  · intro h; simp [deviceCertified, h]
  · intro h
    have hnot : ¬ (sub.holdoutWitnessUpper95 < 0) := not_lt.mpr h
    simp [deviceCertified, hnot]

end UEOTPhysicsUnification.MesoscopicDecoherenceGravimetry
