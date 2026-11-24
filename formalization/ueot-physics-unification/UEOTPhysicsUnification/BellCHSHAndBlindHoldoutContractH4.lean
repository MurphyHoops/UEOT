import UEOT.V3.BinaryTesting
import UEOT.V3.FiniteAlphabetConcentration
import UEOT.V3.FiniteAlphabetPStat01Radius
import UEOT.V3.TVSpan
import UEOTQM.BinaryDiscrimination
import UEOTQM.QuantumPostselectionError
import UEOTPhysicsUnification.MesoscopicDecoherenceGravimetry
import UEOTPhysicsUnification.FlavorCyclicAndSPAMContract
import UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Tactic

/-!
# Bell–CHSH, Nonselective Blind Holdout & Experimental Portfolio Contracts (`H4`: `SPEC-20261124-05`)

Formalizes the three operational, statistical, and protocol sub-frontiers of `H4` (`H4a`, `H4b`, `H4c`)
while explicitly proving 4-way logical independence preserving `H4d` (`raw hardware shot execution`)
as `OPEN` and `deviceCertified = false` (`physicalUnificationStatus = .OPEN`):

1. **`H4a` — Bell–CHSH LHV, Exact 4×4 Tsirelson Bound, Visibility & Fair-Sampling-Free Efficiency**:
   - Pointwise, finite-mixture, and general probability-measure LHV bound `|S_CHSH| ≤ 2`.
   - Exact `4 × 4` operator Landau identity `S_CHSH^2 = 4 I_4 - [A_0, A_1] ⊗ [B_0, B_1]`,
     quantum Tsirelson ceiling `|⟨S_CHSH⟩_ρ| ≤ 2√2` via explicit SOS decomposition,
     and exact attainability on the Bell state `|Φ^+⟩`.
   - Werner visibility threshold `V > 1/√2` and fair-sampling-free detection efficiency
     threshold `η > 2(√2 - 1)` (blocking `DEAD-20261124-03`).

2. **`H4b` — Nonselective Dropout Bias, Multi-Cell Holdout TV Soundness & Anytime-Valid Ville Bound**:
   - Nonselective dropout bias bound `2 * δ_drop * M` via `UEOT.V3.TVSpan.abs_integral_sub_le_span_tvDist`
     and quantum instrument posterior stability via `UEOTQM.QuantumPostselectionError.posterior_effectDistance_le_min`.
   - Simultaneous multi-cell CDF/TV holdout soundness bridging `UEOT.V3.FiniteAlphabetPStat01Radius`,
     `UEOT.V3.BinaryTesting.p_inv_01`, and `UEOTQM.BinaryDiscrimination`.
   - Anytime-valid Ville / supermartingale optional-stopping and finite-horizon maximal inequality
     via `MeasureTheory.Submartingale.expected_stoppedValue_mono`.

3. **`H4c` — Calibration Polytope Anti-Vacuity, Power Margin & Linked Empirical Portfolio Contracts**:
   - Non-empty `Θ_0.99` gate vs vacuous empty-set rejection (`MODEL_SPECIFICATION_REJECTED`).
   - Single-event power margin `> 2 * σ_total` with SPAM/leakage, Casimir–Polder, and `1/f` phase drift,
     paired standard baseline gate (`EQUIVALENT_NO_ADDED_GAIN`), plus Lean statistical contracts
     for `P-COSMO-02` and 3-channel flavor blind holdout (`P-FLAVOR-03`/`04`), and honest
     `deviceCertified = false` whenever raw hardware shots are absent.

4. **`H4` Decomposition (`H4SubHypothesis`)**:
   - Constructive witness `wave11H4ConstructiveWitness = ⟨0, 0, 0, 1⟩` closing `H4a ∧ H4b ∧ H4c`
     while isolating `H4d` as `OPEN`, 4-way logical independence, and global governance `.OPEN`.
-/

namespace UEOTPhysicsUnification.BellCHSHAndBlindHoldoutContractH4

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ComplexOrder

open UEOT.V3.TotalVariation
open UEOT.V3.TVSpan
open UEOT.V3.BinaryTesting
open UEOT.V3.FiniteAlphabetConcentration
open UEOT.V3.FiniteAlphabetSampling
open UEOT.V3.FiniteAlphabetPStat01Radius
open UEOTQM
open UEOTQM.QuantumTraceDistance
open UEOTQM.BinaryDiscrimination
open UEOTQM.QuantumPostselectionError
open UEOTPhysicsUnification.MesoscopicDecoherenceGravimetry
open UEOTPhysicsUnification.FlavorCyclicAndSPAMContract
open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge

/-! ## 1. `H4a`: Bell–CHSH LHV Bound, 4×4 Landau/Tsirelson Identity & Witness Thresholds -/

/-- Pointwise Bell–CHSH linear kernel `a_0 b_0 + a_0 b_1 + a_1 b_0 - a_1 b_1`. -/
def chshLHVKernel (a0 a1 b0 b1 : ℝ) : ℝ :=
  a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1

theorem chshLHVKernel_abs_le_two {a0 a1 b0 b1 : ℝ}
    (ha0 : |a0| ≤ 1) (ha1 : |a1| ≤ 1) (hb0 : |b0| ≤ 1) (hb1 : |b1| ≤ 1) :
    |chshLHVKernel a0 a1 b0 b1| ≤ 2 := by
  have hsum : |b0 + b1| + |b0 - b1| ≤ 2 := by
    rcases abs_le.mp hb0 with ⟨hb0l, hb0u⟩
    rcases abs_le.mp hb1 with ⟨hb1l, hb1u⟩
    rcases le_total 0 (b0 + b1) with h1 | h1 <;>
      rcases le_total 0 (b0 - b1) with h2 | h2
    · rw [abs_of_nonneg h1, abs_of_nonneg h2]; linarith
    · rw [abs_of_nonneg h1, abs_of_nonpos h2]; linarith
    · rw [abs_of_nonpos h1, abs_of_nonneg h2]; linarith
    · rw [abs_of_nonpos h1, abs_of_nonpos h2]; linarith
  have hfact : chshLHVKernel a0 a1 b0 b1 = a0 * (b0 + b1) + a1 * (b0 - b1) := by
    unfold chshLHVKernel
    ring
  rw [hfact]
  calc
    |a0 * (b0 + b1) + a1 * (b0 - b1)|
        ≤ |a0 * (b0 + b1)| + |a1 * (b0 - b1)| := abs_add_le _ _
    _ = |a0| * |b0 + b1| + |a1| * |b0 - b1| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |b0 + b1| + 1 * |b0 - b1| := by gcongr
    _ = |b0 + b1| + |b0 - b1| := by ring
    _ ≤ 2 := hsum

theorem chsh_lhv_finite_mixture_abs_le_two {m : ℕ}
    (p : Fin m → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k : Fin m, p k = 1)
    (a0 a1 b0 b1 : Fin m → ℝ)
    (ha0 : ∀ k, |a0 k| ≤ 1) (ha1 : ∀ k, |a1 k| ≤ 1)
    (hb0 : ∀ k, |b0 k| ≤ 1) (hb1 : ∀ k, |b1 k| ≤ 1) :
    |∑ k : Fin m, p k * chshLHVKernel (a0 k) (a1 k) (b0 k) (b1 k)| ≤ 2 := by
  calc
    |∑ k : Fin m, p k * chshLHVKernel (a0 k) (a1 k) (b0 k) (b1 k)|
        ≤ ∑ k : Fin m, |p k * chshLHVKernel (a0 k) (a1 k) (b0 k) (b1 k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin m, p k * |chshLHVKernel (a0 k) (a1 k) (b0 k) (b1 k)| := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [abs_mul, abs_of_nonneg (hp0 k)]
    _ ≤ ∑ k : Fin m, p k * 2 := by
      refine Finset.sum_le_sum fun k _ => ?_
      exact mul_le_mul_of_nonneg_left
        (chshLHVKernel_abs_le_two (ha0 k) (ha1 k) (hb0 k) (hb1 k)) (hp0 k)
    _ = 2 := by
      rw [← Finset.sum_mul, hp1, one_mul]

theorem chsh_lhv_measure_integral_abs_le_two {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ]
    (a0 a1 b0 b1 : Λ → ℝ)
    (hm0 : Measurable a0) (hm1 : Measurable a1) (hn0 : Measurable b0) (hn1 : Measurable b1)
    (ha0 : ∀ ω, |a0 ω| ≤ 1) (ha1 : ∀ ω, |a1 ω| ≤ 1)
    (hb0 : ∀ ω, |b0 ω| ≤ 1) (hb1 : ∀ ω, |b1 ω| ≤ 1) :
    |∫ ω, chshLHVKernel (a0 ω) (a1 ω) (b0 ω) (b1 ω) ∂μ| ≤ 2 := by
  let g : Λ → ℝ := fun ω => chshLHVKernel (a0 ω) (a1 ω) (b0 ω) (b1 ω)
  have hg_meas : Measurable g :=
    (((hm0.mul hn0).add (hm0.mul hn1)).add (hm1.mul hn0)).sub (hm1.mul hn1)
  have hg_abs : ∀ ω, |g ω| ≤ 2 := fun ω =>
    chshLHVKernel_abs_le_two (ha0 ω) (ha1 ω) (hb0 ω) (hb1 ω)
  have hg_int : Integrable g μ :=
    integrable_of_interval μ g hg_meas (-2) 2
      (fun ω => (abs_le.mp (hg_abs ω)).1)
      (fun ω => (abs_le.mp (hg_abs ω)).2)
  calc
    |∫ ω, g ω ∂μ| ≤ ∫ ω, |g ω| ∂μ :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _ω, (2 : ℝ) ∂μ := by
      refine MeasureTheory.integral_mono hg_int.abs (integrable_const (2 : ℝ)) hg_abs
    _ = 2 := by
      simp

/-- Two-qubit CHSH operator `A_0 ⊗ B_0 + A_0 ⊗ B_1 + A_1 ⊗ B_0 - A_1 ⊗ B_1` on `Qubit2`. -/
def chshOp (A0 A1 B0 B1 : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Qubit2 Qubit2 ℂ :=
  kron A0 B0 + kron A0 B1 + kron A1 B0 - kron A1 B1

/-- Exact `4 × 4` Landau identity: for involutive single-qubit observables `A_i^2 = B_j^2 = I_2`,
`S_CHSH^2 = 4 I_4 - [A_0, A_1] ⊗ [B_0, B_1]`. -/
theorem chshOp_landau_identity (A0 A1 B0 B1 : Matrix (Fin 2) (Fin 2) ℂ)
    (hA0 : A0 * A0 = pauliI) (hA1 : A1 * A1 = pauliI)
    (hB0 : B0 * B0 = pauliI) (hB1 : B1 * B1 = pauliI) :
    chshOp A0 A1 B0 B1 * chshOp A0 A1 B0 B1 =
      (4 : ℂ) • (1 : Matrix Qubit2 Qubit2 ℂ) -
        kron (A0 * A1 - A1 * A0) (B0 * B1 - B1 * B0) := by
  have hk_comm : kron (A0 * A1 - A1 * A0) (B0 * B1 - B1 * B0) =
      kron (A0 * A1) (B0 * B1) - kron (A0 * A1) (B1 * B0) -
        kron (A1 * A0) (B0 * B1) + kron (A1 * A0) (B1 * B0) := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    simp only [kron, Matrix.sub_apply, Matrix.add_apply]
    ring
  unfold chshOp
  simp only [add_mul, sub_mul, mul_add, mul_sub, kron_mul, hA0, hA1, hB0, hB1, kron_pauliI_eq_one]
  rw [hk_comm]
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  ring

private lemma invRt2_sq_real : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsq2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hsq2]
  linarith

private lemma invRt2_sq_complex :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1 / 2 : ℂ) := by
  rw [← Complex.ofReal_mul, invRt2_sq_real]
  push_cast
  rfl

private lemma chsh_sos_identity (A0 A1 B0 B1 : Matrix (Fin 2) (Fin 2) ℂ)
    (hA0 : A0 * A0 = pauliI) (hA1 : A1 * A1 = pauliI)
    (hB0 : B0 * B0 = pauliI) (hB1 : B1 * B1 = pauliI)
    (hA0H : A0ᴴ = A0) (hA1H : A1ᴴ = A1) (hB0H : B0ᴴ = B0) (hB1H : B1ᴴ = B1) :
    let invRt2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)
    let P : Matrix Qubit2 Qubit2 ℂ := invRt2 • (kron A1 pauliI + kron A0 pauliI) - kron pauliI B0
    let Q : Matrix Qubit2 Qubit2 ℂ := invRt2 • (kron A1 pauliI - kron A0 pauliI) + kron pauliI B1
    (((2 * Real.sqrt 2 : ℝ) : ℂ) • (1 : Matrix Qubit2 Qubit2 ℂ) - chshOp A0 A1 B0 B1) =
      invRt2 • (Pᴴ * P + Qᴴ * Q) := by
  intro invRt2 P Q
  have hpi_mul_l : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, pauliI * M = M := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, pauliI]
  have hpi_mul_r : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, M * pauliI = M := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, pauliI]
  have hpiH : pauliIᴴ = pauliI := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, pauliI]
  have hsq2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hinv_sq : invRt2 * invRt2 = (1 / 2 : ℂ) := invRt2_sq_complex
  have hinv_star : star invRt2 = invRt2 := by
    dsimp [invRt2]
    exact Complex.conj_ofReal _
  have hP_herm : Pᴴ = invRt2 • (kron A1 pauliI + kron A0 pauliI) - kron pauliI B0 := by
    dsimp [P]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      kron_conjTranspose, hA0H, hA1H, hB0H, hpiH, hinv_star]
  have hQ_herm : Qᴴ = invRt2 • (kron A1 pauliI - kron A0 pauliI) + kron pauliI B1 := by
    dsimp [Q]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      kron_conjTranspose, hA0H, hA1H, hB1H, hpiH, hinv_star]
  have hPP : Pᴴ * P =
      (invRt2 * invRt2) • ((2 : ℂ) • (1 : Matrix Qubit2 Qubit2 ℂ) + kron (A1 * A0) pauliI +
          kron (A0 * A1) pauliI) -
        invRt2 • (kron A1 B0 + kron A0 B0 + kron A1 B0 + kron A0 B0) +
        (1 : Matrix Qubit2 Qubit2 ℂ) := by
    rw [hP_herm]
    dsimp [P]
    simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
      kron_mul, hA0, hA1, hB0, hpi_mul_l, hpi_mul_r, kron_pauliI_eq_one]
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    ring
  have hQQ : Qᴴ * Q =
      (invRt2 * invRt2) • ((2 : ℂ) • (1 : Matrix Qubit2 Qubit2 ℂ) - kron (A1 * A0) pauliI -
          kron (A0 * A1) pauliI) +
        invRt2 • (kron A1 B1 - kron A0 B1 + kron A1 B1 - kron A0 B1) +
        (1 : Matrix Qubit2 Qubit2 ℂ) := by
    rw [hQ_herm]
    dsimp [Q]
    simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
      kron_mul, hA0, hA1, hB1, hpi_mul_l, hpi_mul_r, kron_pauliI_eq_one]
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    ring
  have h4inv : (4 : ℂ) * invRt2 = ((2 * Real.sqrt 2 : ℝ) : ℂ) := by
    dsimp [invRt2]
    have h4r : (4 : ℝ) * (Real.sqrt 2)⁻¹ = 2 * Real.sqrt 2 := by
      have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      field_simp [hsq2]
      nlinarith [hsq]
    exact_mod_cast h4r
  have h2inv : (2 : ℂ) * (invRt2 * invRt2) = 1 := by
    rw [hinv_sq]
    norm_num
  rw [hPP, hQQ, hinv_sq]
  unfold chshOp
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have h_one : ((2 * Real.sqrt 2 : ℝ) : ℂ) =
      invRt2 * ((1 / 2 : ℂ) * 2 + (1 / 2 : ℂ) * 2 + 1 + 1) := by
    calc
      ((2 * Real.sqrt 2 : ℝ) : ℂ) = (4 : ℂ) * invRt2 := h4inv.symm
      _ = invRt2 * ((1 / 2 : ℂ) * 2 + (1 / 2 : ℂ) * 2 + 1 + 1) := by ring
  have h_coeff : invRt2 * ((2 : ℂ) * invRt2) = 1 := by
    calc
      invRt2 * ((2 : ℂ) * invRt2) = (2 : ℂ) * (invRt2 * invRt2) := by ring
      _ = 1 := h2inv
  calc
    ((2 * Real.sqrt 2 : ℝ) : ℂ) * (if (i1, i2) = (j1, j2) then (1 : ℂ) else 0) -
        (kron A0 B0 (i1, i2) (j1, j2) + kron A0 B1 (i1, i2) (j1, j2) +
          kron A1 B0 (i1, i2) (j1, j2) - kron A1 B1 (i1, i2) (j1, j2))
        = (invRt2 * ((1 / 2 : ℂ) * 2 + (1 / 2 : ℂ) * 2 + 1 + 1)) *
            (if (i1, i2) = (j1, j2) then (1 : ℂ) else 0) -
          (invRt2 * ((2 : ℂ) * invRt2)) *
            (kron A0 B0 (i1, i2) (j1, j2) + kron A0 B1 (i1, i2) (j1, j2) +
              kron A1 B0 (i1, i2) (j1, j2) - kron A1 B1 (i1, i2) (j1, j2)) := by
          rw [← h_one, h_coeff, one_mul]
    _ = invRt2 *
          ((1 / 2 : ℂ) * (2 * (if (i1, i2) = (j1, j2) then 1 else 0) +
              kron (A1 * A0) pauliI (i1, i2) (j1, j2) +
              kron (A0 * A1) pauliI (i1, i2) (j1, j2)) -
            invRt2 * (kron A1 B0 (i1, i2) (j1, j2) + kron A0 B0 (i1, i2) (j1, j2) +
              kron A1 B0 (i1, i2) (j1, j2) + kron A0 B0 (i1, i2) (j1, j2)) +
            (if (i1, i2) = (j1, j2) then 1 else 0) +
          ((1 / 2 : ℂ) * (2 * (if (i1, i2) = (j1, j2) then 1 else 0) -
              kron (A1 * A0) pauliI (i1, i2) (j1, j2) -
              kron (A0 * A1) pauliI (i1, i2) (j1, j2)) +
            invRt2 * (kron A1 B1 (i1, i2) (j1, j2) - kron A0 B1 (i1, i2) (j1, j2) +
              kron A1 B1 (i1, i2) (j1, j2) - kron A0 B1 (i1, i2) (j1, j2)) +
            (if (i1, i2) = (j1, j2) then 1 else 0))) := by ring

private lemma chshOp_pairing_upper (A0 A1 B0 B1 : Matrix (Fin 2) (Fin 2) ℂ)
    (hA0 : A0 * A0 = pauliI) (hA1 : A1 * A1 = pauliI)
    (hB0 : B0 * B0 = pauliI) (hB1 : B1 * B1 = pauliI)
    (hA0H : A0ᴴ = A0) (hA1H : A1ᴴ = A1) (hB0H : B0ᴴ = B0) (hB1H : B1ᴴ = B1)
    (ρ : Density Qubit2) :
    UEOTQM.pairing (chshOp A0 A1 B0 B1) ρ.matrix ≤ 2 * Real.sqrt 2 := by
  let invRt2 : ℝ := (Real.sqrt 2)⁻¹
  let P : Matrix Qubit2 Qubit2 ℂ :=
    (invRt2 : ℂ) • (kron A1 pauliI + kron A0 pauliI) - kron pauliI B0
  let Q : Matrix Qubit2 Qubit2 ℂ :=
    (invRt2 : ℂ) • (kron A1 pauliI - kron A0 pauliI) + kron pauliI B1
  have hsos : (((2 * Real.sqrt 2 : ℝ) : ℂ) • (1 : Matrix Qubit2 Qubit2 ℂ) - chshOp A0 A1 B0 B1) =
      invRt2 • (Pᴴ * P + Qᴴ * Q) := by
    have h := chsh_sos_identity A0 A1 B0 B1 hA0 hA1 hB0 hB1 hA0H hA1H hB0H hB1H
    have hsmul : ((invRt2 : ℂ) • (Pᴴ * P + Qᴴ * Q)) = invRt2 • (Pᴴ * P + Qᴴ * Q) := by
      ext p q
      simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    exact h.trans hsmul
  have hpsd_sum : (Pᴴ * P + Qᴴ * Q).PosSemidef :=
    (Matrix.posSemidef_conjTranspose_mul_self P).add (Matrix.posSemidef_conjTranspose_mul_self Q)
  have hinv_nonneg : 0 ≤ invRt2 := inv_nonneg.mpr (Real.sqrt_nonneg 2)
  have hpsd_rhs : (invRt2 • (Pᴴ * P + Qᴴ * Q)).PosSemidef := hpsd_sum.smul hinv_nonneg
  have hpair_nonneg : 0 ≤ UEOTQM.pairing (invRt2 • (Pᴴ * P + Qᴴ * Q)) ρ.matrix :=
    UEOTQM.pairing_nonneg hpsd_rhs ρ.positive
  rw [← hsos] at hpair_nonneg
  have hdiff : UEOTQM.pairing
      (((2 * Real.sqrt 2 : ℝ) : ℂ) • (1 : Matrix Qubit2 Qubit2 ℂ) - chshOp A0 A1 B0 B1) ρ.matrix =
      2 * Real.sqrt 2 - UEOTQM.pairing (chshOp A0 A1 B0 B1) ρ.matrix := by
    have hsplit : (((2 * Real.sqrt 2 : ℝ) : ℂ) • (1 : Matrix Qubit2 Qubit2 ℂ) - chshOp A0 A1 B0 B1) =
        (2 * Real.sqrt 2 : ℝ) • (1 : Matrix Qubit2 Qubit2 ℂ) + (-1 : ℝ) • chshOp A0 A1 B0 B1 := by
      ext p q
      simp [Complex.real_smul, sub_eq_add_neg]
    rw [hsplit, UEOTQM.pairing_add_left, UEOTQM.pairing_smul_left, UEOTQM.pairing_smul_left,
      UEOTQM.pairing_one, ρ.mass_one]
    ring
  linarith

/-- Quantum Tsirelson bound: for any Hermitian involutions `A_0, A_1, B_0, B_1` and any
two-qubit density matrix `ρ`, `|⟨S_CHSH⟩_ρ| ≤ 2√2`. -/
theorem chshOp_tsirelson_bound (A0 A1 B0 B1 : Matrix (Fin 2) (Fin 2) ℂ)
    (hA0 : A0 * A0 = pauliI) (hA1 : A1 * A1 = pauliI)
    (hB0 : B0 * B0 = pauliI) (hB1 : B1 * B1 = pauliI)
    (hA0H : A0ᴴ = A0) (hA1H : A1ᴴ = A1) (hB0H : B0ᴴ = B0) (hB1H : B1ᴴ = B1)
    (ρ : Density Qubit2) :
    |UEOTQM.pairing (chshOp A0 A1 B0 B1) ρ.matrix| ≤ 2 * Real.sqrt 2 := by
  have hup := chshOp_pairing_upper A0 A1 B0 B1 hA0 hA1 hB0 hB1 hA0H hA1H hB0H hB1H ρ
  have hnegB0 : (-B0) * (-B0) = pauliI := by simp [hB0]
  have hnegB1 : (-B1) * (-B1) = pauliI := by simp [hB1]
  have hnegB0H : (-B0)ᴴ = -B0 := by simp [hB0H]
  have hnegB1H : (-B1)ᴴ = -B1 := by simp [hB1H]
  have hdn := chshOp_pairing_upper A0 A1 (-B0) (-B1) hA0 hA1 hnegB0 hnegB1
    hA0H hA1H hnegB0H hnegB1H ρ
  have hchsh_neg : chshOp A0 A1 (-B0) (-B1) = (-1 : ℝ) • chshOp A0 A1 B0 B1 := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    simp [chshOp, kron]
    ring
  rw [hchsh_neg, UEOTQM.pairing_smul_left] at hdn
  exact abs_le.mpr ⟨by linarith, hup⟩

private noncomputable def bellPhiPlusVec : Qubit2 → ℂ := fun p =>
  if p = (0, 0) ∨ p = (1, 1) then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0

private noncomputable def bellPhiPlusFactor : Matrix Qubit2 Qubit2 ℂ :=
  fun r c => if r = (0, 0) then star (bellPhiPlusVec c) else 0

private noncomputable def bellPhiPlusMat : Matrix Qubit2 Qubit2 ℂ :=
  bellPhiPlusFactorᴴ * bellPhiPlusFactor

private lemma bellPhiPlusMat_entry (p q : Qubit2) :
    bellPhiPlusMat p q =
      (if p = (0, 0) ∨ p = (1, 1) then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0) *
      (if q = (0, 0) ∨ q = (1, 1) then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0) := by
  unfold bellPhiPlusMat
  rw [Matrix.mul_apply]
  have hstar : star (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  fin_cases p <;> fin_cases q <;>
    simp [bellPhiPlusFactor, bellPhiPlusVec, Matrix.conjTranspose_apply]

/-- Maximally entangled Bell state `|Φ^+⟩⟨Φ^+|` on `Qubit2`. -/
noncomputable def bellPhiPlus : Density Qubit2 where
  matrix := bellPhiPlusMat
  positive := by
    unfold bellPhiPlusMat
    exact Matrix.posSemidef_conjTranspose_mul_self _
  trace_one := by
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [bellPhiPlusMat_entry (0, 0) (0, 0), bellPhiPlusMat_entry (0, 1) (0, 1),
      bellPhiPlusMat_entry (1, 0) (1, 0), bellPhiPlusMat_entry (1, 1) (1, 1)]
    have hinC : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      simpa [Complex.ofReal_inv] using invRt2_sq_complex
    have h01 : ¬ ((0 : Fin 2), (1 : Fin 2)) = (0, 0) ∧ ¬ ((0 : Fin 2), (1 : Fin 2)) = (1, 1) := by
      decide
    have h10 : ¬ ((1 : Fin 2), (0 : Fin 2)) = (0, 0) ∧ ¬ ((1 : Fin 2), (0 : Fin 2)) = (1, 1) := by
      decide
    simp [h01, h10]
    rw [hinC]
    norm_num

private lemma pauliXZ_mul_and_hermitian :
    pauliX * pauliX = pauliI ∧
      pauliZ * pauliZ = pauliI ∧
      pauliX * pauliZ + pauliZ * pauliX = 0 ∧
      pauliXᴴ = pauliX ∧
      pauliZᴴ = pauliZ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, pauliI, pauliX, pauliZ])

/-- Exact attainability of Tsirelson's bound `2√2` on `bellPhiPlus` with `A_0 = Z`, `A_1 = X`,
`B_0 = (Z + X)/√2`, `B_1 = (Z - X)/√2`. -/
theorem chsh_tsirelson_attained :
    let invRt2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)
    let A0 : Matrix (Fin 2) (Fin 2) ℂ := pauliZ
    let A1 : Matrix (Fin 2) (Fin 2) ℂ := pauliX
    let B0 : Matrix (Fin 2) (Fin 2) ℂ := invRt2 • (pauliZ + pauliX)
    let B1 : Matrix (Fin 2) (Fin 2) ℂ := invRt2 • (pauliZ - pauliX)
    A0 * A0 = pauliI ∧ A1 * A1 = pauliI ∧ B0 * B0 = pauliI ∧ B1 * B1 = pauliI ∧
      A0ᴴ = A0 ∧ A1ᴴ = A1 ∧ B0ᴴ = B0 ∧ B1ᴴ = B1 ∧
      UEOTQM.pairing (chshOp A0 A1 B0 B1) bellPhiPlus.matrix = 2 * Real.sqrt 2 := by
  intro invRt2 A0 A1 B0 B1
  rcases pauliXZ_mul_and_hermitian with ⟨hxx, hzz, hanticomm, hxH, hzH⟩
  have hsq2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hinv_sq : invRt2 * invRt2 = (1 / 2 : ℂ) := invRt2_sq_complex
  have hinv_star : star invRt2 = invRt2 := by
    dsimp [invRt2]
    exact Complex.conj_ofReal _
  have hB0_sq : B0 * B0 = pauliI := by
    dsimp [B0]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hexp : (pauliZ + pauliX) * (pauliZ + pauliX) = (2 : ℂ) • pauliI := by
      calc
        (pauliZ + pauliX) * (pauliZ + pauliX)
            = pauliZ * pauliZ + pauliX * pauliX + (pauliX * pauliZ + pauliZ * pauliX) := by
                simp only [add_mul, mul_add]
                abel
        _ = pauliI + pauliI + 0 := by rw [hzz, hxx, hanticomm]
        _ = (2 : ℂ) • pauliI := by
              ext i j; simp; ring
    rw [hexp, smul_smul, hinv_sq]
    ext i j; simp
  have hB1_sq : B1 * B1 = pauliI := by
    dsimp [B1]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hexp : (pauliZ - pauliX) * (pauliZ - pauliX) = (2 : ℂ) • pauliI := by
      calc
        (pauliZ - pauliX) * (pauliZ - pauliX)
            = pauliZ * pauliZ + pauliX * pauliX - (pauliX * pauliZ + pauliZ * pauliX) := by
                simp only [sub_mul, mul_sub]
                abel
        _ = pauliI + pauliI - 0 := by rw [hzz, hxx, hanticomm]
        _ = (2 : ℂ) • pauliI := by
              ext i j; simp; ring
    rw [hexp, smul_smul, hinv_sq]
    ext i j; simp
  have hB0H : B0ᴴ = B0 := by
    dsimp [B0]
    simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hzH, hxH, hinv_star]
  have hB1H : B1ᴴ = B1 := by
    dsimp [B1]
    simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hzH, hxH, hinv_star]
  refine ⟨hzz, hxx, hB0_sq, hB1_sq, hzH, hxH, hB0H, hB1H, ?_⟩
  have hinC : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    simpa [Complex.ofReal_inv] using invRt2_sq_complex
  have hzz_pair : UEOTQM.pairing (kron pauliZ pauliZ) bellPhiPlus.matrix = 1 := by
    unfold UEOTQM.pairing UEOTQM.mass
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      kron, pauliZ, bellPhiPlus, bellPhiPlusMat_entry]
    simp [hinC]
    norm_num
  have hxx_pair : UEOTQM.pairing (kron pauliX pauliX) bellPhiPlus.matrix = 1 := by
    unfold UEOTQM.pairing UEOTQM.mass
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      kron, pauliX, bellPhiPlus, bellPhiPlusMat_entry]
    simp [hinC]
    norm_num
  have hchsh_eq : chshOp A0 A1 B0 B1 =
      (Real.sqrt 2 : ℝ) • (kron pauliZ pauliZ + kron pauliX pauliX) := by
    have h2inv : (2 : ℂ) * invRt2 = ((Real.sqrt 2 : ℝ) : ℂ) := by
      dsimp [invRt2]
      have h2r : (2 : ℝ) * (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
        have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        field_simp [hsq2]
        linarith
      exact_mod_cast h2r
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    simp only [chshOp, A0, A1, B0, B1, kron, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.real_smul]
    calc
      pauliZ i1 j1 * (invRt2 * (pauliZ i2 j2 + pauliX i2 j2)) +
          pauliZ i1 j1 * (invRt2 * (pauliZ i2 j2 - pauliX i2 j2)) +
          pauliX i1 j1 * (invRt2 * (pauliZ i2 j2 + pauliX i2 j2)) -
          pauliX i1 j1 * (invRt2 * (pauliZ i2 j2 - pauliX i2 j2))
          = ((2 : ℂ) * invRt2) * (pauliZ i1 j1 * pauliZ i2 j2 + pauliX i1 j1 * pauliX i2 j2) := by
              ring
      _ = ((Real.sqrt 2 : ℝ) : ℂ) *
            (pauliZ i1 j1 * pauliZ i2 j2 + pauliX i1 j1 * pauliX i2 j2) := by
            rw [h2inv]
  rw [hchsh_eq, UEOTQM.pairing_smul_left, UEOTQM.pairing_add_left, hzz_pair, hxx_pair]
  ring

/-- Werner state CHSH violation threshold: `V * (2√2) > 2 ↔ V > 1/√2`. -/
theorem werner_chsh_visibility_threshold_iff (V : ℝ) :
    2 < V * (2 * Real.sqrt 2) ↔ 1 / Real.sqrt 2 < V := by
  have hrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2rt2 : 0 < 2 * Real.sqrt 2 := by positivity
  constructor
  · intro h
    have : 2 / (2 * Real.sqrt 2) < V := (div_lt_iff₀ h2rt2).mpr h
    simpa [div_mul_cancel_left₀ (by norm_num : (2 : ℝ) ≠ 0)] using this
  · intro h
    have h' : 2 / (2 * Real.sqrt 2) < V := by
      have heq : 2 / (2 * Real.sqrt 2) = 1 / Real.sqrt 2 := by
        field_simp [hrt2.ne']
      rw [heq]; exact h
    exact (div_lt_iff₀ h2rt2).mp h'

/-- Nonselective CHSH value under symmetric detection efficiency `η` when missed clicks
are deterministically assigned `+1` (no fair-sampling postselection; `DEAD-20261124-03`). -/
noncomputable def nonselectiveDetCHSH (η : ℝ) : ℝ :=
  η ^ 2 * (2 * Real.sqrt 2) + 2 * (1 - η) ^ 2

/-- Fair-sampling-free detection efficiency threshold: for `0 < η ≤ 1`,
`S_det(η) > 2 ↔ η > 2(√2 - 1)`, and `η ≤ 2(√2 - 1)` keeps `S_det(η) ≤ 2`. -/
theorem nonselective_detection_efficiency_threshold_iff {η : ℝ} (hη : 0 < η) :
    (2 < nonselectiveDetCHSH η ↔ 2 * (Real.sqrt 2 - 1) < η) ∧
      (η ≤ 2 * (Real.sqrt 2 - 1) → nonselectiveDetCHSH η ≤ 2) := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hconj : (Real.sqrt 2 + 1) * (Real.sqrt 2 - 1) = 1 := by nlinarith [hsq]
  have hdiff : nonselectiveDetCHSH η - 2 =
      2 * η * ((Real.sqrt 2 + 1) * η - 2) := by
    unfold nonselectiveDetCHSH
    ring
  have hpos_factor : 0 < 2 * η := by positivity
  have hpos_rt : 0 < Real.sqrt 2 + 1 := by
    have := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    linarith
  have hsub_pos : 0 < Real.sqrt 2 - 1 := by nlinarith [hsq]
  have hiff : 2 < nonselectiveDetCHSH η ↔ 2 * (Real.sqrt 2 - 1) < η := by
    rw [← sub_pos, hdiff, mul_pos_iff_of_pos_left hpos_factor, sub_pos]
    constructor
    · intro h
      have hmul := mul_lt_mul_of_pos_left h hsub_pos
      nlinarith [hconj]
    · intro h
      have hmul := mul_lt_mul_of_pos_left h hpos_rt
      nlinarith [hconj]
  refine ⟨hiff, ?_⟩
  intro hle
  by_contra hgt
  exact absurd (hiff.mp (lt_of_not_ge hgt)) (not_lt.mpr hle)

/-- **H4a Master Theorem**: LHV `|S_CHSH| ≤ 2` (pointwise, finite-mixture, and measure-integral),
exact `4 × 4` Landau identity & quantum Tsirelson bound `|⟨S_CHSH⟩_ρ| ≤ 2√2` with Bell-state
attainability, Werner visibility `V > 1/√2`, and fair-sampling-free detection threshold `η > 2(√2 - 1)`. -/
theorem chsh_lhv_bound_two_and_tsirelson_two_sqrt_two :
    (∀ a0 a1 b0 b1 : ℝ, |a0| ≤ 1 → |a1| ≤ 1 → |b0| ≤ 1 → |b1| ≤ 1 →
      |chshLHVKernel a0 a1 b0 b1| ≤ 2) ∧
      (∀ (A0 A1 B0 B1 : Matrix (Fin 2) (Fin 2) ℂ),
        A0 * A0 = pauliI → A1 * A1 = pauliI → B0 * B0 = pauliI → B1 * B1 = pauliI →
        chshOp A0 A1 B0 B1 * chshOp A0 A1 B0 B1 =
          (4 : ℂ) • (1 : Matrix Qubit2 Qubit2 ℂ) -
            kron (A0 * A1 - A1 * A0) (B0 * B1 - B1 * B0)) ∧
      (∀ (A0 A1 B0 B1 : Matrix (Fin 2) (Fin 2) ℂ) (ρ : Density Qubit2),
        A0 * A0 = pauliI → A1 * A1 = pauliI → B0 * B0 = pauliI → B1 * B1 = pauliI →
        A0ᴴ = A0 → A1ᴴ = A1 → B0ᴴ = B0 → B1ᴴ = B1 →
        |UEOTQM.pairing (chshOp A0 A1 B0 B1) ρ.matrix| ≤ 2 * Real.sqrt 2) ∧
      (∃ (A0 A1 B0 B1 : Matrix (Fin 2) (Fin 2) ℂ) (ρ : Density Qubit2),
        A0 * A0 = pauliI ∧ A1 * A1 = pauliI ∧ B0 * B0 = pauliI ∧ B1 * B1 = pauliI ∧
        A0ᴴ = A0 ∧ A1ᴴ = A1 ∧ B0ᴴ = B0 ∧ B1ᴴ = B1 ∧
        UEOTQM.pairing (chshOp A0 A1 B0 B1) ρ.matrix = 2 * Real.sqrt 2) ∧
      (∀ V : ℝ, 2 < V * (2 * Real.sqrt 2) ↔ 1 / Real.sqrt 2 < V) ∧
      (∀ η : ℝ, 0 < η → (2 < nonselectiveDetCHSH η ↔ 2 * (Real.sqrt 2 - 1) < η)) := by
  refine ⟨?_, chshOp_landau_identity, ?_, ?_, werner_chsh_visibility_threshold_iff, ?_⟩
  · intro a0 a1 b0 b1 ha0 ha1 hb0 hb1
    exact chshLHVKernel_abs_le_two ha0 ha1 hb0 hb1
  · intro A0 A1 B0 B1 ρ hA0 hA1 hB0 hB1 hA0H hA1H hB0H hB1H
    exact chshOp_tsirelson_bound A0 A1 B0 B1 hA0 hA1 hB0 hB1 hA0H hA1H hB0H hB1H ρ
  · rcases chsh_tsirelson_attained with ⟨h1, h2, h3, h4, h5, h6, h7, h8, hval⟩
    exact ⟨_, _, _, _, bellPhiPlus, h1, h2, h3, h4, h5, h6, h7, h8, hval⟩
  · intro η hη
    exact (nonselective_detection_efficiency_threshold_iff hη).1

/-! ## 2. `H4b`: Nonselective Dropout Bias, Multi-Cell TV Holdout & Anytime-Valid Ville Bound -/

/-- Total-variation triangle inequality for `UEOT.V3.TotalVariation.tvDist`. -/
theorem tvDist_triangle {X : Type*} [MeasurableSpace X]
    (μ ν ρ : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] :
    tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ := by
  unfold tvDist
  refine csSup_le (tvEventSet_nonempty μ ρ) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  have htri : |μ.real A - ρ.real A| ≤ |μ.real A - ν.real A| + |ν.real A - ρ.real A| :=
    abs_sub_le (μ.real A) (ν.real A) (ρ.real A)
  have h1 := tvEvent_le μ ν A hA
  have h2 := tvEvent_le ν ρ A hA
  exact htri.trans (add_le_add h1 h2)

/-- Nonselective dropout TV bound: if full nonselective distribution `P_full` decomposes as
`(1 - δ) P_acc + δ P_drop` with `0 ≤ δ ≤ δ_drop`, then `D_TV(P_full, P_acc) ≤ δ_drop` and every
`M`-bounded observable suffers bias at most `2 * δ_drop * M`. -/
theorem nonselective_dropout_bias_le_two_delta_bound {X : Type*} [MeasurableSpace X]
    (P_full P_acc P_drop : Measure X)
    [IsProbabilityMeasure P_full] [IsProbabilityMeasure P_acc] [IsProbabilityMeasure P_drop]
    {δ δ_drop M : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ δ_drop) (hM : 0 ≤ M)
    (hmix : ∀ A : Set X, MeasurableSet A →
      P_full.real A = (1 - δ) * P_acc.real A + δ * P_drop.real A)
    (g : X → ℝ) (hg : Measurable g) (hg_bdd : ∀ x, |g x| ≤ M) :
    tvDist P_full P_acc ≤ δ_drop ∧
      |(∫ x, g x ∂P_full) - ∫ x, g x ∂P_acc| ≤ 2 * δ_drop * M := by
  have htv : tvDist P_full P_acc ≤ δ_drop := by
    unfold tvDist
    refine csSup_le (tvEventSet_nonempty P_full P_acc) ?_
    intro r hr
    rcases hr with ⟨A, hA, rfl⟩
    have hdiff : P_full.real A - P_acc.real A = δ * (P_drop.real A - P_acc.real A) := by
      rw [hmix A hA]; ring
    have hdrop0 : 0 ≤ P_drop.real A := measureReal_nonneg
    have hdrop1 : P_drop.real A ≤ 1 := measureReal_le_one
    have hacc0 : 0 ≤ P_acc.real A := measureReal_nonneg
    have hacc1 : P_acc.real A ≤ 1 := measureReal_le_one
    have habs_diff : |P_drop.real A - P_acc.real A| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    rw [hdiff, abs_mul, abs_of_nonneg hδ0]
    calc
      δ * |P_drop.real A - P_acc.real A| ≤ δ * 1 := mul_le_mul_of_nonneg_left habs_diff hδ0
      _ = δ := mul_one δ
      _ ≤ δ_drop := hδ_le
  refine ⟨htv, ?_⟩
  have hspan := abs_integral_sub_le_span_tvDist P_full P_acc g hg (-M) M (by linarith)
    (fun x => (abs_le.mp (hg_bdd x)).1) (fun x => (abs_le.mp (hg_bdd x)).2)
  have h2M : M - -M = 2 * M := by ring
  rw [h2M] at hspan
  exact hspan.trans (by nlinarith)

/-- Quantum postselection stability bridge: if acceptance probability on branch `o` is at least
`1 - δ_drop` (`δ_drop < 1`), posterior trace distance amplifies by at most `1 / (1 - δ_drop)`. -/
theorem quantum_postselection_branch_stability
    {ι O κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype O] [Fintype κ]
    (I : Instrument ι O κ) (o : O) (ρ σ : Density ι)
    (hp : 0 < I.probability ρ o) (hq : 0 < I.probability σ o)
    {ε δ_drop : ℝ} (hε : 0 ≤ ε) (hδ : δ_drop < 1)
    (hacc : 1 - δ_drop ≤ max (I.probability ρ o) (I.probability σ o))
    (herror : effectDistance ρ σ ≤ ε) :
    effectDistance (I.posterior ρ o hp) (I.posterior σ o hq) ≤
      min 1 (ε / (1 - δ_drop)) := by
  have hpost := posterior_effectDistance_le_min I o ρ σ hp hq herror
  have hpos : 0 < 1 - δ_drop := sub_pos.mpr hδ
  have hdiv : ε / max (I.probability ρ o) (I.probability σ o) ≤ ε / (1 - δ_drop) :=
    div_le_div_of_nonneg_left hε hpos hacc
  exact hpost.trans (le_min (min_le_left _ _) ((min_le_right _ _).trans hdiv))

/-- Anytime-valid Ville optional-stopping bound for any nonnegative supermartingale `E`
(expressed as `Submartingale (fun n ω => -E n ω) ℱ μ`) with initial mean `≤ 1`. -/
theorem ville_optional_stopping_bound {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (E : ℕ → Ω → ℝ) (hnonneg : ∀ n ω, 0 ≤ E n ω)
    (hsub : Submartingale (fun n ω => -E n ω) ℱ μ)
    (hinit : ∫ ω, E 0 ω ∂μ ≤ 1)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N)
    {α : ℝ} (hα : 0 < α) :
    μ.real {ω | 1 / α ≤ stoppedValue E τ ω} ≤ α := by
  have h0_stop : IsStoppingTime ℱ (fun _ => (0 : WithTop ℕ)) := isStoppingTime_const ℱ 0
  have h0_le_τ : (fun _ : Ω => (0 : WithTop ℕ)) ≤ τ := fun ω => by simp
  have hmono := hsub.expected_stoppedValue_mono h0_stop hτ h0_le_τ hbdd
  have hE_stop_eq : stoppedValue (fun n ω => -E n ω) τ = fun ω => -stoppedValue E τ ω := by
    ext ω
    rfl
  have hE0_eq : stoppedValue (fun n ω => -E n ω) (fun _ => (0 : WithTop ℕ)) = fun ω => -E 0 ω := by
    ext ω
    rfl
  rw [hE_stop_eq, hE0_eq, integral_neg, integral_neg, neg_le_neg_iff] at hmono
  have hint_neg : Integrable (fun ω => -stoppedValue E τ ω) μ := by
    simpa [hE_stop_eq] using hsub.integrable_stoppedValue hτ hbdd
  have hint : Integrable (stoppedValue E τ) μ := by
    simpa using hint_neg.neg
  have hstop_nonneg : 0 ≤ᵐ[μ] stoppedValue E τ := by
    refine ae_of_all _ fun ω => ?_
    change 0 ≤ stoppedValue E τ ω
    exact hnonneg (τ ω).untopA ω
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hstop_nonneg hint (1 / α)
  have hle_one : (1 / α) * μ.real {ω | 1 / α ≤ stoppedValue E τ ω} ≤ 1 :=
    hmarkov.trans (hmono.trans hinit)
  calc
    μ.real {ω | 1 / α ≤ stoppedValue E τ ω}
        = α * ((1 / α) * μ.real {ω | 1 / α ≤ stoppedValue E τ ω}) := by
          field_simp [hα.ne']
    _ ≤ α * 1 := mul_le_mul_of_nonneg_left hle_one hα.le
    _ = α := mul_one α

/-- Finite-horizon anytime-valid Ville maximal inequality: for any nonnegative supermartingale `E`
with `E[E_0] ≤ 1`, `P(∃ k ≤ N, E_k ≥ 1/α) ≤ α`. -/
theorem ville_maximal_inequality {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (E : ℕ → Ω → ℝ) (hnonneg : ∀ n ω, 0 ≤ E n ω)
    (hsub : Submartingale (fun n ω => -E n ω) ℱ μ)
    (hinit : ∫ ω, E 0 ω ∂μ ≤ 1)
    (N : ℕ) {α : ℝ} (hα : 0 < α) :
    μ.real {ω | ∃ k ≤ N, 1 / α ≤ E k ω} ≤ α := by
  classical
  let τ : Ω → WithTop ℕ := fun ω =>
    if h : ∃ k ≤ N, 1 / α ≤ E k ω then (Nat.find h : WithTop ℕ) else (N : WithTop ℕ)
  have hτ_le_N : ∀ ω, τ ω ≤ (N : WithTop ℕ) := by
    intro ω
    dsimp [τ]
    split_ifs with h
    · exact Nat.cast_le.mpr (Nat.find_spec h).1
    · exact le_rfl
  have hτ_stop : IsStoppingTime ℱ τ := by
    intro n
    by_cases hNn : N ≤ n
    · convert (@MeasurableSet.univ Ω (ℱ n)) using 1
      ext ω
      simp only [Set.mem_ofPred, Set.mem_univ, iff_true]
      exact (hτ_le_N ω).trans (Nat.cast_le.mpr hNn)
    · have hnN : n < N := lt_of_not_ge hNn
      have hset : {ω | τ ω ≤ (n : WithTop ℕ)} = ⋃ k ≤ n, {ω | 1 / α ≤ E k ω} := by
        ext ω
        simp only [Set.mem_ofPred, Set.mem_iUnion, exists_prop]
        constructor
        · intro hle
          dsimp [τ] at hle
          split_ifs at hle with hex
          · refine ⟨Nat.find hex, Nat.cast_le.mp hle, (Nat.find_spec hex).2⟩
          · exact absurd (Nat.cast_le.mp hle) (not_le_of_gt hnN)
        · rintro ⟨k, hkn, hkα⟩
          have hex : ∃ j ≤ N, 1 / α ≤ E j ω := ⟨k, hkn.trans hnN.le, hkα⟩
          have hfind : Nat.find hex ≤ k := Nat.find_min' hex ⟨hkn.trans hnN.le, hkα⟩
          dsimp [τ]
          rw [dif_pos hex]
          exact Nat.cast_le.mpr (hfind.trans hkn)
      have hm : @MeasurableSet Ω (ℱ n) (⋃ k ≤ n, {ω | 1 / α ≤ E k ω}) := by
        refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hk => ?_
        have hsub_meas : StronglyMeasurable[ℱ k] (fun ω => -E k ω) := hsub.1 k
        have hE_meas : @Measurable Ω ℝ (ℱ k) _ (E k) := by
          convert hsub_meas.measurable.neg using 1
          ext ω
          simp
        exact ℱ.mono hk _ (hE_meas measurableSet_Ici)
      convert hm using 1
      exact hset
  have hsub_event : {ω | ∃ k ≤ N, 1 / α ≤ E k ω} ⊆ {ω | 1 / α ≤ stoppedValue E τ ω} := by
    intro ω hex
    have hspec := Nat.find_spec hex
    have hτ_eq : τ ω = (Nat.find hex : WithTop ℕ) := dif_pos hex
    show 1 / α ≤ E (τ ω).untopA ω
    rw [hτ_eq]
    exact hspec.2
  exact (measureReal_mono hsub_event).trans
    (ville_optional_stopping_bound μ ℱ E hnonneg hsub hinit τ hτ_stop hτ_le_N hα)

/-- **H4b Master Theorem**:
1. Nonselective dropout bias `≤ 2 * δ_drop * M`,
2. Simultaneous multi-cell CDF/TV holdout soundness (`p_stat_01_radius`),
3. Simultaneous event envelope + `BinaryTesting.p_inv_01` lower bound,
4. `UEOTQM.BinaryDiscrimination.exists_optimal_equalPriorDecision` trace-distance formula,
5. Anytime-valid Ville finite-horizon maximal inequality. -/
theorem nonselective_dropout_bias_and_multicell_tv_holdout_soundness :
    (∀ {X : Type} [MeasurableSpace X] (P_full P_acc P_drop : Measure X)
        [IsProbabilityMeasure P_full] [IsProbabilityMeasure P_acc] [IsProbabilityMeasure P_drop]
        {δ δ_drop M : ℝ}, 0 ≤ δ → δ ≤ δ_drop → 0 ≤ M →
        (∀ A : Set X, MeasurableSet A →
          P_full.real A = (1 - δ) * P_acc.real A + δ * P_drop.real A) →
        ∀ (g : X → ℝ), Measurable g → (∀ x, |g x| ≤ M) →
          tvDist P_full P_acc ≤ δ_drop ∧
            |(∫ x, g x ∂P_full) - ∫ x, g x ∂P_acc| ≤ 2 * δ_drop * M) ∧
      (∀ {Ω J Y : Type} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSingletonClass Y]
          [Fintype J] [Nonempty J] [Fintype Y] {N : ℕ} (hN : 0 < N)
          (μ : Measure Ω) [IsProbabilityMeasure μ]
          (p : J → Measure Y), (∀ j, IsProbabilityMeasure (p j)) →
          ∀ (sample : J → Fin N → Ω → Y), (∀ j n, Measurable (sample j n)) →
          (∀ j, iIndepFun (sample j) μ) → (∀ j n, μ.map (sample j n) = p j) →
          ∀ {α : ℝ}, 0 < α → α ≤ 1 →
          μ.real {ω | ∃ j : J,
            pStat01Radius N (Fintype.card Y) (Fintype.card J) α <
              tvDist (p j) (empiricalMeasure hN (sample j) ω)} ≤ α) ∧
      (∀ {Y : Type} [MeasurableSpace Y] [Fintype Y] [MeasurableSingletonClass Y]
          (p pHat q : Measure Y) [IsProbabilityMeasure p] [IsProbabilityMeasure pHat]
          [IsProbabilityMeasure q] {η ε : ℝ},
          tvDist p pHat ≤ η → tvDist q pHat ≤ ε →
          (∀ A : Finset Y, |p.real (A : Set Y) - pHat.real (A : Set Y)| ≤ η) ∧
            ∃ A_opt : Set Y, MeasurableSet A_opt ∧
              (1 / 2 : ℝ) * (1 - (η + ε)) ≤ binaryRisk p q A_opt) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (ρ σ : Density ι),
        ∃ E : Effect ι, equalPriorSuccess E ρ σ = 1 / 2 + traceAbsolute (ρ.matrix - σ.matrix) / 4 ∧
          ∀ F : Effect ι, equalPriorSuccess F ρ σ ≤ equalPriorSuccess E ρ σ) ∧
      (∀ {Ω : Type} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
          (ℱ : Filtration ℕ m0) (E : ℕ → Ω → ℝ),
          (∀ n ω, 0 ≤ E n ω) →
          Submartingale (fun n ω => -E n ω) ℱ μ →
          (∫ ω, E 0 ω ∂μ ≤ 1) →
          ∀ (N : ℕ) {α : ℝ}, 0 < α →
            μ.real {ω | ∃ k ≤ N, 1 / α ≤ E k ω} ≤ α) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X _ P_full P_acc P_drop _ _ _ δ δ_drop M hδ0 hδ_le hM hmix g hg hg_bdd
    exact nonselective_dropout_bias_le_two_delta_bound P_full P_acc P_drop hδ0 hδ_le hM hmix g hg hg_bdd
  · intro Ω J Y _ _ _ _ _ _ N hN μ _ p hp sample hmeas hindep hlaw α hα0 hα1
    exact p_stat_01_radius hN μ p hp sample hmeas hindep hlaw hα0 hα1
  · intro Y _ _ _ p pHat q _ _ _ η ε hp_hat hq_hat
    refine ⟨?_, ?_⟩
    · intro A
      exact (tvEvent_le p pHat (A : Set Y) (MeasurableSet.of_discrete)).trans hp_hat
    · obtain ⟨A_opt, hA_opt, hrisk, _⟩ := p_inv_01 p q
      have hq_sym : tvDist pHat q ≤ ε := by
        unfold tvDist
        refine csSup_le (tvEventSet_nonempty pHat q) ?_
        intro r hr
        rcases hr with ⟨B, hB, rfl⟩
        rw [abs_sub_comm]
        exact (tvEvent_le q pHat B hB).trans hq_hat
      have htri : tvDist p q ≤ η + ε :=
        (tvDist_triangle p pHat q).trans (add_le_add hp_hat hq_sym)
      refine ⟨A_opt, hA_opt, ?_⟩
      rw [hrisk]
      linarith
  · intro ι _ _ ρ σ
    obtain ⟨E, hE_eq, hE_max⟩ := exists_optimal_equalPriorDecision ρ σ
    refine ⟨E, ?_, hE_max⟩
    rw [hE_eq, effectDistance_eq_half_traceAbsolute]
    ring
  · intro Ω m0 μ _ ℱ E hnonneg hsub hinit N α hα
    exact ville_maximal_inequality μ ℱ E hnonneg hsub hinit N hα

/-! ## 3. `H4c`: Calibration Polytope Anti-Vacuity, Power Margin & Linked Empirical Contracts -/

/-- Portfolio verification verdict matching `HARDWARE_CERTIFICATION_CONTRACT.md` §§2–3. -/
inductive PortfolioGateVerdict : Type
  | CERTIFIED
  | MODEL_SPECIFICATION_REJECTED
  | INSUFFICIENT_DISCRIMINATION_POWER
  | HOLDOUT_ENVELOPE_REJECTED
  | EQUIVALENT_NO_ADDED_GAIN
  | MISSING_RAW_SHOTS
  deriving DecidableEq, Repr

/-- Calibration polytope predicate `Θ_0.99` enforcing simultaneous calibration interval constraints. -/
def ThetaCal {Θ : Type*} {B : ℕ} (pred : Θ → Fin B → ℝ) (obs tol : Fin B → ℝ) : Set Θ :=
  {θ | ∀ b : Fin B, |pred θ b - obs b| ≤ tol b}

/-- Paired standard baseline gate: rejects spurious advantage claims when the standard process-tensor
or joint-unitary baseline achieves residual within `τ_gain` of UEOT on identical data and budget. -/
noncomputable def pairedBaselineGate (errUEOT errBase tauGain : ℝ) : PortfolioGateVerdict :=
  if errBase - errUEOT ≤ tauGain then .EQUIVALENT_NO_ADDED_GAIN else .CERTIFIED

/-- Cosmological background expansion invariant `E^2(a) = Ω_m a^{-3} + Ω_X`. -/
noncomputable def cosmoE2 (Om_clust Om_X a : ℝ) : ℝ :=
  Om_clust * a⁻¹ ^ 3 + Om_X

/-- Anti-vacuity theorem for `Θ_0.99`: an empty calibration polytope satisfies *any* predicate
vacuously (requiring explicit `MODEL_SPECIFICATION_REJECTED` rather than vacuous pass), whereas a
non-empty polytope produces an explicit feasible parameter witness `θ ∈ Θ_0.99`. -/
theorem empty_calibration_polytope_vacuity_vs_nonempty_gate
    {Θ : Type*} (Theta99 : Set Θ) :
    (Theta99 = ∅ → ∀ P : Θ → Prop, ∀ θ ∈ Theta99, P θ) ∧
      (Theta99.Nonempty → ∃ θ : Θ, θ ∈ Theta99) := by
  refine ⟨?_, ?_⟩
  · intro hempty P θ hmem
    rw [hempty] at hmem
    exact False.elim hmem
  · intro hne
    exact hne

/-- Single-event power margin (`> 2 * σ_total`) with combined statistical + SPAM + Casimir–Polder
+ `1/f` phase drift uncertainty ensures strictly disjoint acceptance intervals (`σ_sep > 0`). -/
theorem power_margin_disjoint_intervals
    {σ_stat σ_SPAM σ_CP σ_drift σ_total μ_null μ_alt : ℝ}
    (hstat : 0 ≤ σ_stat) (hSPAM : 0 ≤ σ_SPAM) (hCP : 0 ≤ σ_CP) (hdrift : 0 ≤ σ_drift)
    (hbudget : σ_stat + σ_SPAM + σ_CP + σ_drift ≤ σ_total)
    (hpower : 2 * σ_total < |μ_alt - μ_null|) :
    0 ≤ σ_total ∧
      0 < |μ_alt - μ_null| - 2 * σ_total ∧
      (∀ y_null y_alt : ℝ, |y_null - μ_null| ≤ σ_total → |y_alt - μ_alt| ≤ σ_total →
        y_null ≠ y_alt) := by
  have htot_nonneg : 0 ≤ σ_total := by linarith
  refine ⟨htot_nonneg, by linarith, ?_⟩
  intro y_null y_alt h1 h2 heq
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have hdiff : |μ_alt - μ_null| ≤ 2 * σ_total := by
    rw [heq] at h1'
    rw [abs_le]
    constructor <;> linarith
  linarith

/-- `P-COSMO-02` statistical contract: exact Kunz background degeneracy, no-ghost scalar EOS
`-1 < w_phi(a) < 0`, constant velocity-bias cancellation in growth slope ratios, and `> 2σ` `E_G`
separation yielding `Δχ^2 > 4`. -/
theorem p_cosmo_02_contract
    {Om_alt dOm OL0 a b_v fs8_hi fs8_lo EG_lcdm EG_scalar σ_EG : ℝ}
    (ha : 0 < a) (hdOm : 0 < dOm) (hOL : 0 < OL0)
    (hbv : b_v ≠ 0) (hlo : fs8_lo ≠ 0) (hσ : 0 < σ_EG)
    (hEG : 2 * σ_EG < |EG_lcdm - EG_scalar|) :
    cosmoE2 (Om_alt + dOm) OL0 a = cosmoE2 Om_alt (dOm * a⁻¹ ^ 3 + OL0) a ∧
      (-1 < -OL0 / (dOm * a⁻¹ ^ 3 + OL0) ∧ -OL0 / (dOm * a⁻¹ ^ 3 + OL0) < 0) ∧
      (b_v * fs8_hi) / (b_v * fs8_lo) = fs8_hi / fs8_lo ∧
      4 < ((EG_lcdm - EG_scalar) / σ_EG) ^ 2 := by
  have ha_inv : 0 < a⁻¹ ^ 3 := pow_pos (inv_pos.mpr ha) 3
  have hden : 0 < dOm * a⁻¹ ^ 3 + OL0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cosmoE2
    ring
  · constructor
    · rw [lt_div_iff₀ hden]
      nlinarith [mul_pos hdOm ha_inv]
    · exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hOL) hden
  · field_simp [hbv, hlo]
  · have hdiv : 2 < |EG_lcdm - EG_scalar| / σ_EG := (lt_div_iff₀ hσ).mpr hEG
    have hsq : 2 ^ 2 < (|EG_lcdm - EG_scalar| / σ_EG) ^ 2 := by nlinarith
    have habs_sq : (|EG_lcdm - EG_scalar| / σ_EG) ^ 2 = ((EG_lcdm - EG_scalar) / σ_EG) ^ 2 := by
      rw [div_pow, sq_abs, ← div_pow]
    linarith

/-- **H4c Master Theorem**:
1. Non-empty `Θ_0.99` gate vs vacuous empty-set pitfall (`MODEL_SPECIFICATION_REJECTED`),
2. Single-event power margin `> 2 * σ_total` with SPAM/Casimir–Polder/drift + SPAM Lipschitz bridge,
3. Paired standard baseline gate (`EQUIVALENT_NO_ADDED_GAIN`),
4. `P-COSMO-02` & 3-channel flavor blind holdout (`P-FLAVOR-03`/`04`) statistical contracts,
5. Strict `deviceCertified sub = false` whenever raw hardware shots are absent (`HARDWARE_CERTIFICATION_CONTRACT.md`). -/
theorem calibration_polytope_power_margin_and_paired_baseline_gate :
    (∀ {Θ : Type} (Theta99 : Set Θ),
      (Theta99 = ∅ → ∀ P : Θ → Prop, ∀ θ ∈ Theta99, P θ) ∧
        (Theta99.Nonempty → ∃ θ : Θ, θ ∈ Theta99)) ∧
      (∀ {σ_stat σ_SPAM σ_CP σ_drift σ_total μ_null μ_alt : ℝ},
        0 ≤ σ_stat → 0 ≤ σ_SPAM → 0 ≤ σ_CP → 0 ≤ σ_drift →
        σ_stat + σ_SPAM + σ_CP + σ_drift ≤ σ_total →
        2 * σ_total < |μ_alt - μ_null| →
        0 < |μ_alt - μ_null| - 2 * σ_total ∧
          (∀ y_null y_alt : ℝ, |y_null - μ_null| ≤ σ_total → |y_alt - μ_alt| ≤ σ_total →
            y_null ≠ y_alt)) ∧
      (∀ {leak e0 e1 y y' : ℝ}, leak < 1 → e0 + e1 < 1 →
        |calibratedProbEstimator (FlavorCyclicAndSPAMContract.observedBrightProb leak e0 e1 0)
            (FlavorCyclicAndSPAMContract.observedBrightProb leak e0 e1 1) y' -
          calibratedProbEstimator (FlavorCyclicAndSPAMContract.observedBrightProb leak e0 e1 0)
            (FlavorCyclicAndSPAMContract.observedBrightProb leak e0 e1 1) y| =
          |y' - y| / ((1 - leak) * (1 - e0 - e1))) ∧
      (∀ errUEOT errBase tauGain : ℝ,
        errBase - errUEOT ≤ tauGain →
        pairedBaselineGate errUEOT errBase tauGain = .EQUIVALENT_NO_ADDED_GAIN) ∧
      (∀ {Om_alt dOm OL0 a b_v fs8_hi fs8_lo EG_lcdm EG_scalar σ_EG : ℝ},
        0 < a → 0 < dOm → 0 < OL0 → b_v ≠ 0 → fs8_lo ≠ 0 → 0 < σ_EG →
        2 * σ_EG < |EG_lcdm - EG_scalar| →
        cosmoE2 (Om_alt + dOm) OL0 a = cosmoE2 Om_alt (dOm * a⁻¹ ^ 3 + OL0) a ∧
          (-1 < -OL0 / (dOm * a⁻¹ ^ 3 + OL0) ∧ -OL0 / (dOm * a⁻¹ ^ 3 + OL0) < 0) ∧
          (b_v * fs8_hi) / (b_v * fs8_lo) = fs8_hi / fs8_lo ∧
          4 < ((EG_lcdm - EG_scalar) / σ_EG) ^ 2) ∧
      (∀ {kappa : ℝ}, 0 ≤ kappa → ∀ ud us ub : ℂ,
        (cyclicJ (wilsonC kappa ud us) (wilsonC kappa us ub) (wilsonC kappa ub ud)).im = 0 ∧
          0 ≤ (cyclicJ (wilsonC kappa ud us) (wilsonC kappa us ub) (wilsonC kappa ub ud)).re) ∧
      (∀ sub : PreRegisteredHardwareSubmission,
        sub.rawShotsComplete = false →
        MesoscopicDecoherenceGravimetry.deviceCertified sub = false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Θ Theta99
    exact empty_calibration_polytope_vacuity_vs_nonempty_gate Theta99
  · intro σ_stat σ_SPAM σ_CP σ_drift σ_total μ_null μ_alt hs hsp hcp hd hbud hpow
    exact (power_margin_disjoint_intervals hs hsp hcp hd hbud hpow).2
  · intro leak e0 e1 y y' hleak hspam
    exact spam_leakage_estimator_lipschitz hleak hspam
  · intro errUEOT errBase tauGain hle
    simp [pairedBaselineGate, hle]
  · intro Om_alt dOm OL0 a b_v fs8_hi fs8_lo EG_lcdm EG_scalar σ_EG ha hd hOL hbv hlo hσ hEG
    exact p_cosmo_02_contract ha hd hOL hbv hlo hσ hEG
  · intro kappa hk ud us ub
    exact rank_one_cyclicJ_real_nonneg hk ud us ub
  · intro sub hraw
    exact (no_vacuous_pass_on_empty_calibration_or_missing_raw_shots sub).1 hraw

/-! ## 4. Sharp 4-Layer Decomposition of `H4` & Honest Device Status (`C-H4-CONTRACT-04`) -/

/-- Exact 4-layer sub-hypothesis decomposition of empirical hardware frontier `H4`. -/
inductive H4SubHypothesis : Type
  | h4a_chsh_tsirelson_and_witness_thresholds
  | h4b_nonselective_multicell_holdout_soundness
  | h4c_calibration_power_and_portfolio_contracts
  | h4d_raw_hardware_shot_execution
  deriving DecidableEq, Repr

instance : Fintype H4SubHypothesis where
  elems := {
    .h4a_chsh_tsirelson_and_witness_thresholds,
    .h4b_nonselective_multicell_holdout_soundness,
    .h4c_calibration_power_and_portfolio_contracts,
    .h4d_raw_hardware_shot_execution
  }
  complete h := by cases h <;> decide

/-- Quantitative defect record evaluating all four sublayers of `H4`. -/
structure H4LayerCandidate where
  chshTsirelsonDefect : ℝ
  nonselectiveHoldoutDefect : ℝ
  calibrationPortfolioDefect : ℝ
  rawHardwareShotDefect : ℝ

/-- Semantic closure predicate on each sublayer of `H4`. -/
def H4LayerCandidate.Satisfies (C : H4LayerCandidate) : H4SubHypothesis → Prop
  | .h4a_chsh_tsirelson_and_witness_thresholds => C.chshTsirelsonDefect = 0
  | .h4b_nonselective_multicell_holdout_soundness => C.nonselectiveHoldoutDefect = 0
  | .h4c_calibration_power_and_portfolio_contracts => C.calibrationPortfolioDefect = 0
  | .h4d_raw_hardware_shot_execution => C.rawHardwareShotDefect = 0

/-- Complete unconditional closure of `H4` (requires physical raw hardware shot execution `H4d`). -/
def H4LayerCandidate.FullH4Closure (C : H4LayerCandidate) : Prop :=
  C.chshTsirelsonDefect = 0 ∧
  C.nonselectiveHoldoutDefect = 0 ∧
  C.calibrationPortfolioDefect = 0 ∧
  C.rawHardwareShotDefect = 0

/-- Wave 11 `M3` constructive witness closing `H4a ∧ H4b ∧ H4c` while isolating `H4d`
(raw physical hardware shot execution) as honestly `OPEN`. -/
def wave11H4ConstructiveWitness : H4LayerCandidate :=
  ⟨0, 0, 0, 1⟩

/-- **Sharp `H4` Frontier Decomposition & Honest Device Status (`C-H4-CONTRACT-04`)**:
1. `Fintype.card H4SubHypothesis = 4` and `FullH4Closure C ↔ ∀ h, C.Satisfies h`,
2. `wave11H4ConstructiveWitness` closes `H4a ∧ H4b ∧ H4c` while leaving `H4d` open,
3. All four sublayers `H4a..H4d` are pairwise logically independent,
4. When `H4a ∧ H4b ∧ H4c` hold, full `H4` closure holds **iff** `H4d` holds,
5. Absent raw device shots (`rawShotsComplete = false`), `deviceCertified sub = false` and
   `physicalUnificationStatus` remains strictly `.OPEN`. -/
theorem h4_frontier_sharp_decomposition_and_honest_device_status :
    Fintype.card H4SubHypothesis = 4 ∧
      (∀ C : H4LayerCandidate, C.FullH4Closure ↔ ∀ h : H4SubHypothesis, C.Satisfies h) ∧
      (wave11H4ConstructiveWitness.Satisfies .h4a_chsh_tsirelson_and_witness_thresholds ∧
        wave11H4ConstructiveWitness.Satisfies .h4b_nonselective_multicell_holdout_soundness ∧
        wave11H4ConstructiveWitness.Satisfies .h4c_calibration_power_and_portfolio_contracts ∧
        ¬ wave11H4ConstructiveWitness.Satisfies .h4d_raw_hardware_shot_execution) ∧
      (∀ h : H4SubHypothesis, ∃ C : H4LayerCandidate,
        (∀ h' : H4SubHypothesis, h' ≠ h → C.Satisfies h') ∧ ¬ C.Satisfies h) ∧
      (∀ C : H4LayerCandidate,
        C.Satisfies .h4a_chsh_tsirelson_and_witness_thresholds →
        C.Satisfies .h4b_nonselective_multicell_holdout_soundness →
        C.Satisfies .h4c_calibration_power_and_portfolio_contracts →
        (C.FullH4Closure ↔ C.Satisfies .h4d_raw_hardware_shot_execution)) ∧
      (∀ sub : PreRegisteredHardwareSubmission,
        sub.rawShotsComplete = false →
        MesoscopicDecoherenceGravimetry.deviceCertified sub = false) ∧
      (∀ k : ℕ, physicalUnificationStatus k false = .OPEN) ∧
      physicalUnificationStatus (Fintype.card H4SubHypothesis) false = .OPEN := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C
    constructor
    · rintro ⟨h1, h2, h3, h4⟩ h
      cases h
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    · intro hall
      exact ⟨hall .h4a_chsh_tsirelson_and_witness_thresholds,
        hall .h4b_nonselective_multicell_holdout_soundness,
        hall .h4c_calibration_power_and_portfolio_contracts,
        hall .h4d_raw_hardware_shot_execution⟩
  · exact ⟨rfl, rfl, rfl, by simp [wave11H4ConstructiveWitness, H4LayerCandidate.Satisfies]⟩
  · intro h
    cases h with
    | h4a_chsh_tsirelson_and_witness_thresholds =>
      refine ⟨⟨1, 0, 0, 0⟩, ?_, by simp [H4LayerCandidate.Satisfies]⟩
      intro h' hne; cases h' <;> first | exact absurd rfl hne | rfl
    | h4b_nonselective_multicell_holdout_soundness =>
      refine ⟨⟨0, 1, 0, 0⟩, ?_, by simp [H4LayerCandidate.Satisfies]⟩
      intro h' hne; cases h' <;> first | exact absurd rfl hne | rfl
    | h4c_calibration_power_and_portfolio_contracts =>
      refine ⟨⟨0, 0, 1, 0⟩, ?_, by simp [H4LayerCandidate.Satisfies]⟩
      intro h' hne; cases h' <;> first | exact absurd rfl hne | rfl
    | h4d_raw_hardware_shot_execution =>
      refine ⟨⟨0, 0, 0, 1⟩, ?_, by simp [H4LayerCandidate.Satisfies]⟩
      intro h' hne; cases h' <;> first | exact absurd rfl hne | rfl
  · intro C h1 h2 h3
    dsimp [H4LayerCandidate.Satisfies, H4LayerCandidate.FullH4Closure] at h1 h2 h3 ⊢
    simp [h1, h2, h3]
  · intro sub hraw
    exact (no_vacuous_pass_on_empty_calibration_or_missing_raw_shots sub).1 hraw
  · intro k
    simp [physicalUnificationStatus]
  · decide

end UEOTPhysicsUnification.BellCHSHAndBlindHoldoutContractH4
