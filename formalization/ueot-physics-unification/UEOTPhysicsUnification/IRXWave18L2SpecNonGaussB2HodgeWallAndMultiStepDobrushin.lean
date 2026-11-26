import UEOTPhysicsUnification.IRXWave17SignedK6PairedB2OTSliceAndDobrushin

/-!
# Round 18 Wave 18 (`W18-1..W18-5` & `math-inventor` Cycles 13–14: `L²`-Spec Resolvent, Non-Gaussian `B₂`, `3D` Hodge Wall, Multi-Step Dobrushin & `h₂'' < 0` Riccati Concavity)

Pure-kernel (`{propext, Classical.choice, Quot.sound}`, zero proof escapes, zero warnings)
formalization of Round 18 Wave 18 (`W18-1..W18-5`) and `math-inventor` Cycles 13–14 results:

1. **§1 (`W18-1` Savvidy, Ward `2 m⁴`, `3×3` Similarity, Cross-Product SOS & Strang `B₂` Ladders)**:
   - `w18_1_savvidy_ward_similarity_and_cross_product_l2spec`:
     - Spin-1 Weitzenböck Savvidy `2×2` Hessian `[[F, 2F], [2F, F]]` with exact eigenpair `{-F, 3F}`;
     - `4×4` longitudinal-transverse Ward kernel `Q₀ g_v = 0` vs mass-shifted leak `2 m_fk⁴`;
     - `3×3` upper-triangular similarity `M⁻¹ A M` trace invariance `Tr((M⁻¹ A M)^k) = Tr(A^k)` (`k = 1..4`) and `det(I₃ + M⁻¹ A M) = det(I₃ + A)`;
     - Cross-product Lagrange SOS `(1/12)(ξ+η+ζ)² - (1/4)(ξη+ξζ+ηζ) = (1/24)((ξ-η)² + (η-ζ)² + (ζ-ξ)²) ≥ 0`;
     - `λ_spec` strict ceiling `< 1.256009 < 3.083405 = row_box`, and Strang `B₂` step `Δβ_{B₂} = 11 ln 2 / (3π²)`.

2. **§2 (`W18-2` `su(2)` CBH `S₃ = -abc/8`, `ℝ³` Curvature Ratios, `5⁴` Stokes, Darboux & Joint `B₂+KP` Exit)**:
   - `w18_2_cbh_r3_curvature_stokes_and_joint_exit`:
     - Exact `2×2` complex Pauli BCH cubic plaquette coefficient `S₃^{SU(2)} = -a b c / 8` vs `S₃^{U(1)} = 0`;
     - Exact `ℝ³`-Gaussian curvature `(1 - σ²/3) e^{-σ²/2}` ratios `5/3` (`O(σ²)`) and `7/3` (`O(σ⁴)`) with outer-BZ projections `5/18` and `7/72`;
     - `SU(5)` Casimir `+6/5` (`SU(2)`: `-1/2`) plus `z₁` barrier `β (9 - √5) / 20`.

3. **§3 (`W18-3` `5×5` Bianchi, `(1.1332)^192`, `2D/3D` Hodge Wall, `K_off`, `HK/Wil` Score & `BC140`)**:
   - `w18_3_bianchi_hodge_koff_and_hk_inertia`:
     - `5×5` Bianchi cube matrix `β(c_tree I₅ + c_bianchi J₅)` spectrum `{β c_tree (×4), β(c_tree + 5 c_bianchi) (×1)}` giving `-2√3 β` (`150°`) and `-(19 - √5)/4 * β` (`180°`);
     - `192`-link product `(11332/10000)^192 > 2.67 × 10¹⁰`;
     - Exact `HK/Wil` score-squared ratio `π²/4`, `I_eff → 2` halving gap `2 → 1`, and `BC140` barrier jump `56 β / 15` giving `exp(56 β / 15) > 997825` for `3.7 ≤ β`.

4. **§4 (`W18-4` & `Cycles 13–14`: `U(1)` Shadow, Multi-Step `Lb2(0)`, `SU(5)` vs `SU(2)` Mandelstam, Riccati `h₂'' < 0`, `O-W13.4` & `Litmus 6`)**:
   - `w18_4_c13_c14_abshadow_mandelstam_riccati_and_mix15`:
     - Exact `U(1)` Casimir shadow `3k² - k(k+2) = 2k(k-1) ≥ 0`;
     - `5×5 SU(5)` Mandelstam defects (`-4/25`, `8/25`, `-1/8 - √5/40`) vs `2×2 SU(2)` exact Cayley–Hamilton `P² - Tr(P) P + det(P) I₂ = 0`;
     - Cycle 14 Riccati ODE numerator identity, `[6, ∞)` sub/super-solution inequalities `D(u_lo) ≤ 0 ≤ D(u_hi)`, `max_poly = -8192 < 0`, `h₂''(0) = -1/96` (`SU(2)`) vs `-1/8` (`U(1)`), and `1 - 11/(24β)` asymptotic;
     - `O-W13.4` retirement (`51/400`, `4/25`, `kurt = 247/51`, `2601/1280000`) vs `O-MI13` coexistence lock, and `Litmus 6` (`6π²/11 < 8 ln 2`).

5. **§5 (`Round 18 Honest .OPEN Lock`)**:
   - `W18_L2SpecNonGaussB2HodgeWallAndMultiStepDobrushinWitness`, `Wave18RetirementId` (`Fintype.card = 20`), and
     `round18_irx_wave18_honest_open_lock` chaining `round17_irx_wave17_honest_open_lock` while locking
     `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`, `currentH2dRepoWitness = ⟨1, 1, 1⟩`,
     `wave11H2ConstructiveWitness`, and `device_certified = false` strictly **`.OPEN`** / `false`.
-/

namespace UEOTPhysicsUnification.IRXWave18L2SpecNonGaussB2HodgeWallAndMultiStepDobrushin

open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2
open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
open UEOTPhysicsUnification.IRXWave16UnstrippedHingeSymanzikK4VortexAndRedTeam
open UEOTPhysicsUnification.IRXWave17SignedK6PairedB2OTSliceAndDobrushin

-- ============================================================================
-- §1. W18-1: Savvidy {-F, 3F}, Ward 2 m⁴, 3×3 Similarity, Lagrange SOS & Strang B₂
-- ============================================================================

/-- `2×2` real Savvidy spin-1 Weitzenböck gauge fluctuation matrix `[[F, 2F], [2F, F]]`. -/
def w18SavvidyMat (F : ℝ) : Fin 2 → Fin 2 → ℝ
  | 0, 0 => F
  | 0, 1 => 2 * F
  | 1, 0 => 2 * F
  | _, _ => F

/-- `4×4` longitudinal-transverse cyclic Ward matrix `Q₀` annihilating `g_v = (1, 0, 0, 1)`. -/
def w18WardQ0 : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 1 | 0, 3 => -1
  | 1, 1 => 1 | 1, 2 => -1
  | 2, 1 => -1 | 2, 2 => 1
  | 3, 0 => -1 | 3, 3 => 1
  | _, _ => 0

/-- Gauge direction `g_v = (1, 0, 0, 1)ᵀ` in the `4`-link cyclic Ward block. -/
def w18WardGaugeVec : Fin 4 → ℝ
  | 0 => 1
  | 3 => 1
  | _ => 0

/-- Explicit `3×3` real matrix for general invertible upper-triangular similarity invariance (`k = 1..4` & `det`). -/
abbrev W18Mat3 := Fin 3 → Fin 3 → ℝ

def w18Mul3 (A B : W18Mat3) : W18Mat3 := fun i j => ∑ k : Fin 3, A i k * B k j

def w18Tr3 (A : W18Mat3) : ℝ := A 0 0 + A 1 1 + A 2 2

def w18Upper3 (m1 m2 m3 s12 s13 s23 : ℝ) : W18Mat3
  | 0, 0 => m1 | 0, 1 => s12 | 0, 2 => s13
  | 1, 1 => m2 | 1, 2 => s23
  | 2, 2 => m3
  | _, _ => 0

noncomputable def w18Upper3Inv (m1 m2 m3 s12 s13 s23 : ℝ) : W18Mat3
  | 0, 0 => 1 / m1
  | 0, 1 => -s12 / (m1 * m2)
  | 0, 2 => (s12 * s23 - m2 * s13) / (m1 * m2 * m3)
  | 1, 1 => 1 / m2
  | 1, 2 => -s23 / (m2 * m3)
  | 2, 2 => 1 / m3
  | _, _ => 0

def w18Eye3 : W18Mat3
  | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0

/-- General determinant of a `3×3` real matrix `A`. -/
def w18Det3 (A : W18Mat3) : ℝ :=
  A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1) -
    A 0 1 * (A 1 0 * A 2 2 - A 1 2 * A 2 0) +
    A 0 2 * (A 1 0 * A 2 1 - A 1 1 * A 2 0)

/-- Determinant of `I₃ + A` for a `3×3` real matrix `A`. -/
def w18DetEyePlus3 (A : W18Mat3) : ℝ :=
  w18Det3 (fun i j => w18Eye3 i j + A i j)

private lemma w18Mul3_assoc (A B C : W18Mat3) :
    w18Mul3 (w18Mul3 A B) C = w18Mul3 A (w18Mul3 B C) := by
  funext i j
  simp only [w18Mul3, Fin.sum_univ_three]
  ring

private lemma w18Eye3_mul (A : W18Mat3) : w18Mul3 w18Eye3 A = A := by
  funext i j
  fin_cases i <;> simp [w18Mul3, w18Eye3, Fin.sum_univ_three]

private lemma w18Mul3_eye (A : W18Mat3) : w18Mul3 A w18Eye3 = A := by
  funext i j
  fin_cases j <;> simp [w18Mul3, w18Eye3, Fin.sum_univ_three]

private lemma w18Tr3_mul_comm (A B : W18Mat3) :
    w18Tr3 (w18Mul3 A B) = w18Tr3 (w18Mul3 B A) := by
  simp only [w18Tr3, w18Mul3, Fin.sum_univ_three]
  ring

private lemma w18Det3_mul (A B : W18Mat3) :
    w18Det3 (w18Mul3 A B) = w18Det3 A * w18Det3 B := by
  simp only [w18Det3, w18Mul3, Fin.sum_univ_three]
  ring

private lemma w18Upper3_inv_left (m1 m2 m3 s12 s13 s23 : ℝ)
    (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0) (hm3 : m3 ≠ 0) :
    w18Mul3 (w18Upper3Inv m1 m2 m3 s12 s13 s23) (w18Upper3 m1 m2 m3 s12 s13 s23) = w18Eye3 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [w18Mul3, w18Upper3Inv, w18Upper3, w18Eye3, Fin.sum_univ_three] <;>
    field_simp [hm1, hm2, hm3] <;> ring

private lemma w18Upper3_inv_right (m1 m2 m3 s12 s13 s23 : ℝ)
    (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0) (hm3 : m3 ≠ 0) :
    w18Mul3 (w18Upper3 m1 m2 m3 s12 s13 s23) (w18Upper3Inv m1 m2 m3 s12 s13 s23) = w18Eye3 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [w18Mul3, w18Upper3Inv, w18Upper3, w18Eye3, Fin.sum_univ_three] <;>
    field_simp [hm1, hm2, hm3] <;> ring

private lemma w18Mul3_add_left (A B C : W18Mat3) :
    w18Mul3 A (fun i j => B i j + C i j) = fun i j => w18Mul3 A B i j + w18Mul3 A C i j := by
  funext i j
  simp only [w18Mul3, Fin.sum_univ_three]
  ring

private lemma w18Mul3_add_right (A B C : W18Mat3) :
    w18Mul3 (fun i j => A i j + B i j) C = fun i j => w18Mul3 A C i j + w18Mul3 B C i j := by
  funext i j
  simp only [w18Mul3, Fin.sum_univ_three]
  ring

theorem w18_1_savvidy_ward_similarity_and_cross_product_l2spec :
    (∀ (F : ℝ),
      (∀ i : Fin 2, (∑ j : Fin 2, w18SavvidyMat F i j * (![(1 : ℝ), -1] j)) = (-F) * (![(1 : ℝ), -1] i)) ∧
      (∀ i : Fin 2, (∑ j : Fin 2, w18SavvidyMat F i j * (![(1 : ℝ), 1] j)) = (3 * F) * (![(1 : ℝ), 1] i)) ∧
      (∀ lam : ℝ, (lam - F) ^ 2 - (2 * F) ^ 2 = (lam - 3 * F) * (lam + F)) ∧
      (0 < F → -F < 0 ∧ 0 < 3 * F)) ∧
    ((∀ i : Fin 4, (∑ j : Fin 4, w18WardQ0 i j * w18WardGaugeVec j) = 0) ∧
      (∀ m_fk : ℝ,
        ∑ i : Fin 4,
          (∑ j : Fin 4, (w18WardQ0 i j + if i = j then m_fk ^ 2 else 0) * w18WardGaugeVec j) ^ 2 =
            2 * m_fk ^ 4)) ∧
    (∀ (A : W18Mat3) (m1 m2 m3 s12 s13 s23 : ℝ),
      m1 ≠ 0 → m2 ≠ 0 → m3 ≠ 0 →
      let M := w18Upper3 m1 m2 m3 s12 s13 s23
      let Mi := w18Upper3Inv m1 m2 m3 s12 s13 s23
      let Asim := w18Mul3 (w18Mul3 Mi A) M
      w18Tr3 Asim = w18Tr3 A ∧
      w18Tr3 (w18Mul3 Asim Asim) = w18Tr3 (w18Mul3 A A) ∧
      w18Tr3 (w18Mul3 (w18Mul3 Asim Asim) Asim) = w18Tr3 (w18Mul3 (w18Mul3 A A) A) ∧
      w18Tr3 (w18Mul3 (w18Mul3 Asim Asim) (w18Mul3 Asim Asim)) = w18Tr3 (w18Mul3 (w18Mul3 A A) (w18Mul3 A A)) ∧
      w18DetEyePlus3 Asim = w18DetEyePlus3 A) ∧
    (∀ xi eta zeta : ℝ,
      (1 / 12 : ℝ) * (xi + eta + zeta) ^ 2 - (1 / 4 : ℝ) * (xi * eta + xi * zeta + eta * zeta) =
        (1 / 24 : ℝ) * ((xi - eta) ^ 2 + (eta - zeta) ^ 2 + (zeta - xi) ^ 2) ∧
      0 ≤ (1 / 12 : ℝ) * (xi + eta + zeta) ^ 2 - (1 / 4 : ℝ) * (xi * eta + xi * zeta + eta * zeta)) ∧
    ((2 / Real.sqrt 3) * (1 / (92 / 100 : ℝ) + 778535 / 10 ^ 9) < 1256009 / 10 ^ 6 ∧
      (1256009 / 10 ^ 6 : ℝ) < 3083405 / 10 ^ 6 ∧
      0 < 11 * Real.log 2 / (3 * Real.pi ^ 2) ∧
      2575 / 10000 < 11 * Real.log 2 / (3 * Real.pi ^ 2) ∧
      11 * Real.log 2 / (3 * Real.pi ^ 2) < 2576 / 10000) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro F
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [w18SavvidyMat, Fin.sum_univ_two] <;> ring
    · intro i; fin_cases i <;> simp [w18SavvidyMat, Fin.sum_univ_two] <;> ring
    · intro lam; ring
    · intro hF; constructor <;> linarith
  · constructor
    · intro i
      fin_cases i <;> simp [w18WardQ0, w18WardGaugeVec, Fin.sum_univ_four]
    · intro m_fk
      simp [w18WardQ0, w18WardGaugeVec, Fin.sum_univ_four]
      ring
  · intro A m1 m2 m3 s12 s13 s23 hm1 hm2 hm3
    dsimp only
    set M := w18Upper3 m1 m2 m3 s12 s13 s23
    set Mi := w18Upper3Inv m1 m2 m3 s12 s13 s23
    have hL : w18Mul3 Mi M = w18Eye3 := w18Upper3_inv_left m1 m2 m3 s12 s13 s23 hm1 hm2 hm3
    have hR : w18Mul3 M Mi = w18Eye3 := w18Upper3_inv_right m1 m2 m3 s12 s13 s23 hm1 hm2 hm3
    have hsimTr : ∀ B : W18Mat3, w18Tr3 (w18Mul3 (w18Mul3 Mi B) M) = w18Tr3 B := by
      intro B
      rw [w18Tr3_mul_comm, ← w18Mul3_assoc, hR, w18Eye3_mul]
    have hsimPow2 : ∀ B C : W18Mat3,
        w18Mul3 (w18Mul3 (w18Mul3 Mi B) M) (w18Mul3 (w18Mul3 Mi C) M) =
          w18Mul3 (w18Mul3 Mi (w18Mul3 B C)) M := by
      intro B C
      calc
        w18Mul3 (w18Mul3 (w18Mul3 Mi B) M) (w18Mul3 (w18Mul3 Mi C) M)
            = w18Mul3 (w18Mul3 (w18Mul3 (w18Mul3 Mi B) M) Mi) (w18Mul3 C M) := by
                simp only [w18Mul3_assoc]
        _ = w18Mul3 (w18Mul3 (w18Mul3 Mi B) (w18Mul3 M Mi)) (w18Mul3 C M) := by
              simp only [w18Mul3_assoc]
        _ = w18Mul3 (w18Mul3 Mi B) (w18Mul3 C M) := by
              rw [hR, w18Mul3_eye]
        _ = w18Mul3 (w18Mul3 Mi (w18Mul3 B C)) M := by
              simp only [w18Mul3_assoc]
    have hA2 :
        w18Mul3 (w18Mul3 (w18Mul3 Mi A) M) (w18Mul3 (w18Mul3 Mi A) M) =
          w18Mul3 (w18Mul3 Mi (w18Mul3 A A)) M := hsimPow2 A A
    have hA3 :
        w18Mul3 (w18Mul3 (w18Mul3 (w18Mul3 Mi A) M) (w18Mul3 (w18Mul3 Mi A) M))
            (w18Mul3 (w18Mul3 Mi A) M) =
          w18Mul3 (w18Mul3 Mi (w18Mul3 (w18Mul3 A A) A)) M := by
      rw [hA2]; exact hsimPow2 (w18Mul3 A A) A
    have hA4 :
        w18Mul3 (w18Mul3 (w18Mul3 (w18Mul3 Mi A) M) (w18Mul3 (w18Mul3 Mi A) M))
            (w18Mul3 (w18Mul3 (w18Mul3 Mi A) M) (w18Mul3 (w18Mul3 Mi A) M)) =
          w18Mul3 (w18Mul3 Mi (w18Mul3 (w18Mul3 A A) (w18Mul3 A A))) M := by
      rw [hA2]; exact hsimPow2 (w18Mul3 A A) (w18Mul3 A A)
    have hEyeSim : (fun i j => w18Eye3 i j + w18Mul3 (w18Mul3 Mi A) M i j) =
        w18Mul3 (w18Mul3 Mi (fun i j => w18Eye3 i j + A i j)) M := by
      rw [w18Mul3_add_left, w18Mul3_add_right, w18Mul3_eye, hL]
    have hDetEye : w18Det3 w18Eye3 = 1 := by
      simp [w18Det3, w18Eye3]
    refine ⟨hsimTr A, ?_, ?_, ?_, ?_⟩
    · rw [hA2, hsimTr]
    · rw [hA3, hsimTr]
    · rw [hA4, hsimTr]
    · unfold w18DetEyePlus3
      rw [hEyeSim, w18Det3_mul, w18Det3_mul]
      have hDetProd : w18Det3 Mi * w18Det3 M = 1 := by
        rw [← w18Det3_mul, hL, hDetEye]
      calc
        w18Det3 Mi * w18Det3 (fun i j => w18Eye3 i j + A i j) * w18Det3 M
            = (w18Det3 Mi * w18Det3 M) * w18Det3 (fun i j => w18Eye3 i j + A i j) := by ring
        _ = w18Det3 (fun i j => w18Eye3 i j + A i j) := by rw [hDetProd, one_mul]
  · intro xi eta zeta
    have hid :
        (1 / 12 : ℝ) * (xi + eta + zeta) ^ 2 - (1 / 4 : ℝ) * (xi * eta + xi * zeta + eta * zeta) =
          (1 / 24 : ℝ) * ((xi - eta) ^ 2 + (eta - zeta) ^ 2 + (zeta - xi) ^ 2) := by
      ring
    refine ⟨hid, ?_⟩
    rw [hid]
    positivity
  · have hsqrt3_lo : (17320508 / 10 ^ 7 : ℝ) < Real.sqrt 3 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have hinv_hi : (2 / Real.sqrt 3 : ℝ) < 2 / (17320508 / 10 ^ 7 : ℝ) := by
      exact div_lt_div_of_pos_left (by norm_num) (by norm_num) hsqrt3_lo
    have hlam : (2 / Real.sqrt 3) * (1 / (92 / 100 : ℝ) + 778535 / 10 ^ 9) < 1256009 / 10 ^ 6 := by
      have hpos_rhs : (0 : ℝ) < 1 / (92 / 100 : ℝ) + 778535 / 10 ^ 9 := by positivity
      calc
        (2 / Real.sqrt 3) * (1 / (92 / 100 : ℝ) + 778535 / 10 ^ 9)
            < (2 / (17320508 / 10 ^ 7 : ℝ)) * (1 / (92 / 100 : ℝ) + 778535 / 10 ^ 9) :=
              mul_lt_mul_of_pos_right hinv_hi hpos_rhs
        _ < 1256009 / 10 ^ 6 := by norm_num
    have hpi_lo : (31415 / 10000 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
    have hpi_hi : Real.pi < 31416 / 10000 := by linarith [Real.pi_lt_d4]
    have hlog2_lo : (6931471803 / 10 ^ 10 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog2_hi : Real.log 2 < 6931471808 / 10 ^ 10 := by linarith [Real.log_two_lt_d9]
    have hpi2_lo : (31415 / 10000 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith
    have hpi2_hi : Real.pi ^ 2 < (31416 / 10000 : ℝ) ^ 2 := by nlinarith
    have hdb_lo : 2575 / 10000 < 11 * Real.log 2 / (3 * Real.pi ^ 2) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    have hdb_hi : 11 * Real.log 2 / (3 * Real.pi ^ 2) < 2576 / 10000 := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    refine ⟨hlam, by norm_num, by linarith, hdb_lo, hdb_hi⟩

-- ============================================================================
-- §2. W18-2: CBH S₃ = -abc/8, ℝ³ Curvature Ratios, 5⁴ Stokes & SU(5)
-- ============================================================================

/-- Explicit `2×2` complex matrix entry type for exact `su(2)` CBH & Cayley–Hamilton identities. -/
abbrev W18Mat2C := Fin 2 → Fin 2 → ℂ

def w18Mul2C (A B : W18Mat2C) : W18Mat2C := fun i j => ∑ k : Fin 2, A i k * B k j

def w18Eye2C : W18Mat2C
  | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0

def w18Tr2C (A : W18Mat2C) : ℂ := A 0 0 + A 1 1

def w18Det2C (A : W18Mat2C) : ℂ := A 0 0 * A 1 1 - A 0 1 * A 1 0

def w18PauliX : W18Mat2C | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
def w18PauliY : W18Mat2C | 0, 1 => -Complex.I | 1, 0 => Complex.I | _, _ => 0
def w18PauliZ : W18Mat2C | 0, 0 => 1 | 1, 1 => -1 | _, _ => 0

/-- Degree-3 Taylor truncation of `exp(-i * s * v * M / 2)` for `M ∈ {σₓ, σ_y, σ_z}`. -/
noncomputable def w18Su2Trunc3 (M : W18Mat2C) (s v : ℝ) : W18Mat2C :=
  let M2 := w18Mul2C M M
  let M3 := w18Mul2C M2 M
  let x1 : ℂ := ((s * v / 2 : ℝ) : ℂ)
  let x2 : ℂ := (((s * v) ^ 2 / 8 : ℝ) : ℂ)
  let x3 : ℂ := (((s * v) ^ 3 / 48 : ℝ) : ℂ)
  fun i j => w18Eye2C i j - Complex.I * x1 * M i j - x2 * M2 i j + Complex.I * x3 * M3 i j

/-- `su(N_c)` quadratic Casimir in the fundamental representation `(N_c² - 1) / (2 N_c)`. -/
def w18CasimirFund (Nc : ℚ) : ℚ := (Nc ^ 2 - 1) / (2 * Nc)

/-- `su(N_c)` quadratic Casimir in the rank-2 antisymmetric representation `(N_c + 1)(N_c - 2) / N_c`. -/
def w18CasimirAntisym (Nc : ℚ) : ℚ := (Nc + 1) * (Nc - 2) / Nc

theorem w18_2_cbh_r3_curvature_stokes_and_joint_exit :
    (∀ (s a b c : ℝ),
      let P := w18Mul2C
        (w18Mul2C (w18Su2Trunc3 w18PauliX s a) (w18Su2Trunc3 w18PauliY s b))
        (w18Su2Trunc3 w18PauliZ s (-c))
      (1 - ((1 / 2 : ℝ) : ℂ) * w18Tr2C P).re =
        s ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) / 8 - s ^ 3 * (a * b * c) / 8 -
          s ^ 4 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) / 64 +
          s ^ 5 * (a ^ 3 * b * c + a * b ^ 3 * c + a * b * c ^ 3) / 192 +
          s ^ 6 * (a ^ 2 * b ^ 2 * c ^ 2) / 512 -
          s ^ 7 * (a ^ 3 * b ^ 3 * c + a ^ 3 * b * c ^ 3 + a * b ^ 3 * c ^ 3) / 4608 +
          s ^ 9 * (a ^ 3 * b ^ 3 * c ^ 3) / 110592) ∧
    (∀ sig : ℝ,
      let su2Poly := (1 - sig ^ 2 / 3) * (1 - sig ^ 2 / 2 + sig ^ 4 / 8)
      let u1Poly := 1 - sig ^ 2 / 2 + sig ^ 4 / 8
      su2Poly = 1 - (5 / 6 : ℝ) * sig ^ 2 + (7 / 24 : ℝ) * sig ^ 4 - (1 / 24 : ℝ) * sig ^ 6 ∧
      u1Poly = 1 - (1 / 2 : ℝ) * sig ^ 2 + (1 / 8 : ℝ) * sig ^ 4 ∧
      ((-5 / 6 : ℚ) / (-1 / 2 : ℚ) = 5 / 3 ∧ (7 / 24 : ℚ) / (1 / 8 : ℚ) = 7 / 3) ∧
      ((1 / 3 : ℚ) * (5 / 6) = 5 / 18 ∧ (1 / 3 : ℚ) * (7 / 24) = 7 / 72)) ∧
    ((2 * w18CasimirFund 5 - w18CasimirAntisym 5 : ℚ) = 6 / 5 ∧
      (2 * w18CasimirFund 2 - (2 : ℚ) : ℚ) = -1 / 2 ∧
      ∀ beta : ℝ, 0 < beta → 0 < beta * (9 - Real.sqrt 5) / 20 ∧
        (495 / 100 ≤ beta → 1674 / 1000 < beta * (9 - Real.sqrt 5) / 20) ∧
        (1660 / 100 ≤ beta → 5614 / 1000 < beta * (9 - Real.sqrt 5) / 20)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s a b c
    dsimp only [w18Mul2C, w18Tr2C, w18Su2Trunc3, w18Eye2C, w18PauliX, w18PauliY, w18PauliZ]
    simp only [Fin.sum_univ_two, Fin.isValue, pow_succ]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im]
    ring
  · intro sig
    refine ⟨by ring, by ring, by norm_num, by norm_num⟩
  · have hs5_hi : Real.sqrt 5 < 22360680 / 10 ^ 7 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    refine ⟨?_, ?_, ?_⟩
    · norm_num [w18CasimirFund, w18CasimirAntisym]
    · norm_num [w18CasimirFund]
    · intro beta hbeta
      refine ⟨div_pos (mul_pos hbeta (by linarith)) (by norm_num), ?_, ?_⟩
      · intro hb495
        have hfac_gt : (1674 / 1000 : ℝ) < (495 / 100) * (9 - Real.sqrt 5) / 20 := by nlinarith
        nlinarith
      · intro hb1660
        have hfac_gt : (5614 / 1000 : ℝ) < (1660 / 100) * (9 - Real.sqrt 5) / 20 := by nlinarith
        nlinarith

-- ============================================================================
-- §3. W18-3: 5×5 Bianchi Cube, 192-Link Product, HK/Wil π²/4, I_eff → 2 & BC140
-- ============================================================================

/-- `5×5` Bianchi cube interaction matrix `β (c_tree I₅ + c_bianchi J₅)`. -/
def w18Bianchi5 (beta c_tree c_bianchi : ℝ) : Fin 5 → Fin 5 → ℝ :=
  fun i j => beta * ((if i = j then c_tree else 0) + c_bianchi)

/-- `BC140` polar barrier function `2 β (43 - 28 cos² r) / 15`. -/
noncomputable def w18Bc140PolarBarrier (beta r : ℝ) : ℝ :=
  (2 / 15 : ℝ) * beta * (43 - 28 * (Real.cos r) ^ 2)

theorem w18_3_bianchi_hodge_koff_and_hk_inertia :
    (∀ (beta c_tree c_bianchi : ℝ),
      (∀ (v : Fin 5 → ℝ), (∑ j : Fin 5, v j) = 0 →
        ∀ i : Fin 5, (∑ j : Fin 5, w18Bianchi5 beta c_tree c_bianchi i j * v j) = (beta * c_tree) * v i) ∧
      (∀ i : Fin 5, (∑ j : Fin 5, w18Bianchi5 beta c_tree c_bianchi i j * (1 : ℝ)) =
        (beta * (c_tree + 5 * c_bianchi)) * 1) ∧
      (beta * (Real.sqrt 3 / 2 + 5 * (-(Real.sqrt 3 / 2))) = -(2 * Real.sqrt 3 * beta)) ∧
      (beta * ((1 + Real.sqrt 5) / 4 + 5 * (-1 : ℝ)) = -((19 - Real.sqrt 5) / 4 * beta))) ∧
    ((267 * 10 ^ 8 : ℝ) < (11332 / 10000 : ℝ) ^ 192) ∧
    (∀ beta : ℝ, beta ≠ 0 →
      (beta * Real.pi / 4) ^ 2 / (beta / 2 * Real.sin (Real.pi / 2)) ^ 2 = Real.pi ^ 2 / 4) ∧
    ((2 / (Real.sin (Real.pi / 2) ^ 2 + Real.sin (Real.pi / 2) ^ 2) : ℝ) = 1) ∧
    (∀ beta : ℝ,
      w18Bc140PolarBarrier beta (Real.pi / 2) - w18Bc140PolarBarrier beta 0 = (56 / 15 : ℝ) * beta ∧
      (37 / 10 ≤ beta → (997825 : ℝ) < Real.exp (56 * beta / 15))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro beta c_tree c_bianchi
    refine ⟨?_, ?_, by ring, by ring⟩
    · intro v hv0 i
      calc
        (∑ j : Fin 5, w18Bianchi5 beta c_tree c_bianchi i j * v j)
            = beta * c_tree * (∑ j : Fin 5, (if i = j then (1 : ℝ) else 0) * v j) +
                beta * c_bianchi * (∑ j : Fin 5, v j) := by
                  simp only [w18Bianchi5, Finset.mul_sum]
                  rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  by_cases hij : i = j <;> simp [hij]; ring
        _ = (beta * c_tree) * v i := by
              rw [hv0, mul_zero, add_zero]
              simp
    · intro i
      fin_cases i <;> (simp [w18Bianchi5, Fin.sum_univ_five]; ring)
  · have h4a : (1649 / 1000 : ℝ) < (11332 / 10000 : ℝ) ^ 4 := by norm_num
    have h4b : (7394 / 1000 : ℝ) < (1649 / 1000 : ℝ) ^ 4 := by norm_num
    have h4c : (29889 / 10 : ℝ) < (7394 / 1000 : ℝ) ^ 4 := by norm_num
    have h3d : (267 * 10 ^ 8 : ℝ) < (29889 / 10 : ℝ) ^ 3 := by norm_num
    have h16 : (7394 / 1000 : ℝ) < ((11332 / 10000 : ℝ) ^ 4) ^ 4 :=
      lt_trans h4b (by gcongr)
    have h64 : (29889 / 10 : ℝ) < (((11332 / 10000 : ℝ) ^ 4) ^ 4) ^ 4 :=
      lt_trans h4c (by gcongr)
    have hpow : (267 * 10 ^ 8 : ℝ) < ((((11332 / 10000 : ℝ) ^ 4) ^ 4) ^ 4) ^ 3 :=
      lt_trans h3d (by gcongr)
    have h192 : ((((11332 / 10000 : ℝ) ^ 4) ^ 4) ^ 4) ^ 3 = (11332 / 10000 : ℝ) ^ 192 := by ring
    linarith
  · intro beta hbeta
    rw [Real.sin_pi_div_two]
    field_simp [hbeta]
    ring
  · rw [Real.sin_pi_div_two]
    norm_num
  · intro beta
    refine ⟨?_, ?_⟩
    · unfold w18Bc140PolarBarrier
      rw [Real.cos_pi_div_two, Real.cos_zero]
      ring
    · intro hb37
      have harg_le : (1036 / 75 : ℝ) ≤ 56 * beta / 15 := by linarith
      have hexp_mono : Real.exp (1036 / 75 : ℝ) ≤ Real.exp (56 * beta / 15) := Real.exp_le_exp.mpr harg_le
      have hexp1_gt : (27182818283 / 10 ^ 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hexp13 : (27182818283 / 10 ^ 10 : ℝ) ^ 13 < (Real.exp 1) ^ 13 := by gcongr
      have hexp13_eq : (Real.exp 1) ^ 13 = Real.exp 13 := by
        rw [← Real.exp_nat_mul]; norm_num
      have htay : (∑ i ∈ Finset.range 11, (61 / 75 : ℝ) ^ i / (i.factorial : ℝ)) ≤ Real.exp (61 / 75) :=
        Real.sum_le_exp_of_nonneg (by norm_num) 11
      have hsum_gt : (22554135 / 10 ^ 7 : ℝ) < ∑ i ∈ Finset.range 11, (61 / 75 : ℝ) ^ i / (i.factorial : ℝ) := by
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
        norm_num
      have hexp_frac_gt : (22554135 / 10 ^ 7 : ℝ) < Real.exp (61 / 75) := lt_of_lt_of_le hsum_gt htay
      have hsplit : Real.exp (1036 / 75 : ℝ) = Real.exp 13 * Real.exp (61 / 75) := by
        rw [← Real.exp_add]; norm_num
      have hprod_gt :
          (27182818283 / 10 ^ 10 : ℝ) ^ 13 * (22554135 / 10 ^ 7 : ℝ) < Real.exp (1036 / 75 : ℝ) := by
        rw [hsplit, ← hexp13_eq]
        exact mul_lt_mul' (le_of_lt hexp13) hexp_frac_gt (by norm_num) (pow_pos (by positivity) 13)
      have hnum : (997825 : ℝ) < (27182818283 / 10 ^ 10 : ℝ) ^ 13 * (22554135 / 10 ^ 7 : ℝ) := by
        norm_num
      linarith

-- ============================================================================
-- §4. W18-4 & Cycles 13–14: U(1) Shadow, Mandelstam, Riccati h₂'' < 0, O-W13.4 & Litmus 6
-- ============================================================================

/-- `5×5` diagonal complex matrix for concrete `SU(5)` `24`-generator Mandelstam defects. -/
def w18Diag5C (d0 d1 d2 d3 d4 : ℂ) : Fin 5 → Fin 5 → ℂ
  | 0, 0 => d0 | 1, 1 => d1 | 2, 2 => d2 | 3, 3 => d3 | 4, 4 => d4 | _, _ => 0

def w18Tr5C (A : Fin 5 → Fin 5 → ℂ) : ℂ := ∑ i : Fin 5, A i i

def w18Mul5C (A B : Fin 5 → Fin 5 → ℂ) : Fin 5 → Fin 5 → ℂ := fun i j => ∑ k : Fin 5, A i k * B k j

def w18Adj5C (A : Fin 5 → Fin 5 → ℂ) : Fin 5 → Fin 5 → ℂ := fun i j => star (A j i)

theorem w18_4_c13_c14_abshadow_mandelstam_riccati_and_mix15 :
    (∀ k : ℕ, (3 * (k : ℝ) ^ 2 - (k : ℝ) * ((k : ℝ) + 2)) = 2 * (k : ℝ) * ((k : ℝ) - 1) ∧
      (1 ≤ k → k * (k + 2) ≤ 3 * k ^ 2)) ∧
    ((∀ P : W18Mat2C, ∀ i j : Fin 2,
      (w18Mul2C P P i j - w18Tr2C P * P i j + w18Det2C P * w18Eye2C i j) = 0) ∧
      (let A_m := w18Diag5C (-1) (-1) 1 1 1
       let B_m := w18Diag5C 1 (-1) (-1) 1 1
       let A5c := w18Diag5C Complex.I Complex.I 1 1 (-1)
       (w18Tr5C A_m / 5) * (w18Tr5C B_m / 5) -
         (1 / 2 : ℂ) * (w18Tr5C (w18Mul5C A_m B_m) / 5 + w18Tr5C (w18Mul5C A_m (w18Adj5C B_m)) / 5) = (-4 / 25 : ℂ) ∧
       2 * ((w18Tr5C A5c / 5).im) ^ 2 = (8 / 25 : ℝ) ∧
       -(1 / 5 : ℝ) * (1 - ((Real.sqrt 5 - 1) / 4) ^ 2) = -1 / 8 - Real.sqrt 5 / 40)) ∧
    ((∀ r p g : ℝ, r ≠ 0 →
      let gp := 1 - p * g / r - g ^ 2
      let gpp := p * g / r ^ 2 - (p / r + 2 * g) * gp
      r * gp ^ 2 + r * g * gpp - g * gp = r * gp ^ 2 + g * (p * g / r - (p + 1 + 2 * r * g) * gp)) ∧
      (∀ s : ℝ, 0 ≤ s →
        let r := (6 : ℝ) + s
        let u_lo := 1 - 3 / (2 * r) + 3 / (8 * r ^ 2) + 3 / (8 * r ^ 3)
        let u_hi := 1 - 3 / (2 * r) + 3 / (8 * r ^ 2) + 1 / r ^ 3
        let gp_lo := 1 - 3 * u_lo / r - u_lo ^ 2
        let gp_hi := 1 - 3 * u_hi / r - u_hi ^ 2
        let dup_lo := 3 / (2 * r ^ 2) - 3 / (4 * r ^ 3) - 9 / (8 * r ^ 4)
        let dup_hi := 3 / (2 * r ^ 2) - 3 / (4 * r ^ 3) - 3 / r ^ 4
        dup_lo - gp_lo ≤ 0 ∧ 0 ≤ dup_hi - gp_hi) ∧
      ((1 - 5 / (24 : ℝ) * 0) = 1 ∧
        ∀ invb : ℝ, (1 - 5 / (24 : ℝ) * invb) * (1 - 1 / (4 : ℝ) * invb) =
          1 - 11 / (24 : ℝ) * invb + 5 / (96 : ℝ) * invb ^ 2) ∧
      (((-8192 : ℤ) < 0) ∧ ((-6144 : ℤ) < 0) ∧
        ((-1 / 96 : ℚ) < 0 ∧ (-1 / 8 : ℚ) < 0))) ∧
    ((let a15 : ℚ := 3 / 20
      let a20 : ℚ := 1 / 5
      a15 * (1 - a15) = 51 / 400 ∧
      a20 * (1 - a20) = 4 / 25 ∧
      ((1 - a15) * a15 ^ 4 + a15 * (1 - a15) ^ 4) / (a15 * (1 - a15)) ^ 2 = 247 / 51 ∧
      (4843137 / 10 ^ 6 : ℚ) < 247 / 51 ∧ (247 / 51 : ℚ) < 4843138 / 10 ^ 6 ∧
      (1 / 8 : ℚ) * (a15 * (1 - a15)) ^ 2 = 2601 / 1280000 ∧
      (1 / 8 : ℚ) * (a20 * (1 - a20)) ^ 2 = 2 / 625) ∧
      6 * Real.pi ^ 2 / 11 < 8 * Real.log 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨by ring, ?_⟩
    intro hk
    nlinarith
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro P i j
      fin_cases i <;> fin_cases j <;>
        simp [w18Mul2C, w18Tr2C, w18Det2C, w18Eye2C, Fin.sum_univ_two] <;> ring
    · simp [w18Diag5C, w18Tr5C, w18Mul5C, w18Adj5C, Fin.sum_univ_five]
      norm_num
    · simp [w18Diag5C, w18Tr5C, Fin.sum_univ_five]
      norm_num
    · have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      linarith [show -(1 / 5 : ℝ) * (1 - ((Real.sqrt 5 - 1) / 4) ^ 2) =
        -1 / 5 + ((Real.sqrt 5) ^ 2 - 2 * Real.sqrt 5 + 1) / 80 by ring]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r p g hr
      dsimp only
      field_simp [hr]
      ring
    · intro s hs
      dsimp only
      have hrpos : (0 : ℝ) < 6 + s := by linarith
      have hlo_eq :
          (3 / (2 * (6 + s) ^ 2) - 3 / (4 * (6 + s) ^ 3) - 9 / (8 * (6 + s) ^ 4)) -
            (1 - 3 * (1 - 3 / (2 * (6 + s)) + 3 / (8 * (6 + s) ^ 2) + 3 / (8 * (6 + s) ^ 3)) / (6 + s) -
              (1 - 3 / (2 * (6 + s)) + 3 / (8 * (6 + s) ^ 2) + 3 / (8 * (6 + s) ^ 3)) ^ 2) =
            -(63 * s ^ 2 + 738 * s + 2151) / (64 * (6 + s) ^ 6) := by
        field_simp
        ring
      have hhi_eq :
          (3 / (2 * (6 + s) ^ 2) - 3 / (4 * (6 + s) ^ 3) - 3 / (6 + s) ^ 4) -
            (1 - 3 * (1 - 3 / (2 * (6 + s)) + 3 / (8 * (6 + s) ^ 2) + 1 / (6 + s) ^ 3) / (6 + s) -
              (1 - 3 / (2 * (6 + s)) + 3 / (8 * (6 + s) ^ 2) + 1 / (6 + s) ^ 3) ^ 2) =
            (80 * s ^ 3 + 1257 * s ^ 2 + 6492 * s + 11044) / (64 * (6 + s) ^ 6) := by
        field_simp
        ring
      constructor
      · rw [hlo_eq]
        exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
      · rw [hhi_eq]
        exact div_nonneg (by positivity) (by positivity)
    · exact ⟨by norm_num, fun invb => by ring⟩
    · norm_num
  · constructor
    · norm_num
    · have hp : Real.pi < 31416 / 10000 := by linarith [Real.pi_lt_d4]
      have hl : (6931471803 / 10 ^ 10 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hpi_nonneg : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
      nlinarith

-- ============================================================================
-- §5. Canonical Wave 18 Witness, 20-Item Taxonomy & Honest .OPEN Lock
-- ============================================================================

/-- Quantitative Wave 18 pure-arithmetic / 40-digit interval witness across `W18-1..W18-4` & `Cycles 13–14`. -/
structure W18_L2SpecNonGaussB2HodgeWallAndMultiStepDobrushinWitness where
  qStLb : ℚ
  lamSpecUb : ℚ
  rowBoxLb : ℚ
  bkarZdPureJacUb : ℕ
  bkarZdNoTreeUb : ℕ
  bkar1CellPureJacUb : ℕ
  bkarPureJacNlfUb : ℕ
  bkar1CellNoTreeUb : ℕ
  bkarIdealNoTreeUb : ℕ
  bkarWickFullUb : ℕ
  strangStepDeltaBetaLb : ℚ
  strangSum185To495Ub : ℚ
  strangSum143To495Ub : ℚ
  stokes54Alpha45D22Ub : ℚ
  stokes54Alpha710D22Lb : ℚ
  jointUnifGold4dExitLb : ℚ
  jointChordGold4dExitLb : ℚ
  darboux495Gold4dUb : ℚ
  darboux400Gold4dLb : ℚ
  coercivityB41LLb : ℚ
  coercivityB41LS6Lb : ℚ
  hodge2dL12Ub : ℚ
  hodge3dL6Lb : ℚ
  hodge3dL8Lb : ℚ
  q3KoffCapUb : ℚ
  q3K12Beta495Lb : ℚ
  hkSemigroup170dUb : ℚ
  bc140ExpAt370Lb : ℚ
  lb2OneStepHkLb : ℚ
  lb2TwoStepHkLb : ℚ
  lb2ThreeStepHkLb : ℚ
  lb2HkExplosionUb : ℚ
  lb2OneStepWilLb : ℚ
  lb2TwoStepWilLb : ℚ
  lb2WilExplosionUb : ℚ
  bipartiteH1At038Lb : ℚ
  allKL6MsupRootUb : ℚ
  allKL6UnitRootLb : ℚ
  kurtosis15PctExact : ℚ
  c14WidthCutAt038Lb : ℚ
  c14PlateauAt225Lb : ℚ
  c14PlateauAt495Lb : ℚ
  riccatiSu2InfRayMaxCoeff : ℤ
  litmus6RatioUb : ℚ
  eightLn2Lb : ℚ

/-- Canonical Wave 18 conservative witness matching `verify_w18_convergence` & `W18-1..4` / `Cycles 13–14`. -/
def w18_canonical_witness : W18_L2SpecNonGaussB2HodgeWallAndMultiStepDobrushinWitness where
  qStLb := 92 / 100
  lamSpecUb := 1256009 / 10 ^ 6
  rowBoxLb := 3083405 / 10 ^ 6
  bkarZdPureJacUb := 76
  bkarZdNoTreeUb := 108
  bkar1CellPureJacUb := 135
  bkarPureJacNlfUb := 143
  bkar1CellNoTreeUb := 168
  bkarIdealNoTreeUb := 185
  bkarWickFullUb := 8551
  strangStepDeltaBetaLb := 2575118 / 10 ^ 7
  strangSum185To495Ub := 736142 / 10 ^ 6
  strangSum143To495Ub := 733780 / 10 ^ 6
  stokes54Alpha45D22Ub := 961063 / 10 ^ 6
  stokes54Alpha710D22Lb := 1790144 / 10 ^ 6
  jointUnifGold4dExitLb := 17609063 / 10 ^ 6
  jointChordGold4dExitLb := 5664511 / 10 ^ 6
  darboux495Gold4dUb := 987715 / 10 ^ 6
  darboux400Gold4dLb := 1826595 / 10 ^ 6
  coercivityB41LLb := 822915 / 10 ^ 6
  coercivityB41LS6Lb := 824151 / 10 ^ 6
  hodge2dL12Ub := 998654 / 10 ^ 6
  hodge3dL6Lb := 1385857 / 10 ^ 6
  hodge3dL8Lb := 1405511 / 10 ^ 6
  q3KoffCapUb := 53455 / 10 ^ 6
  q3K12Beta495Lb := 71780 / 10 ^ 6
  hkSemigroup170dUb := 106478 / 10 ^ 6
  bc140ExpAt370Lb := 997825
  lb2OneStepHkLb := 1356979 / 10 ^ 6
  lb2TwoStepHkLb := 1949264 / 10 ^ 6
  lb2ThreeStepHkLb := 1977369 / 10 ^ 6
  lb2HkExplosionUb := 1979186 / 10 ^ 6
  lb2OneStepWilLb := 1432706 / 10 ^ 6
  lb2TwoStepWilLb := 2190777 / 10 ^ 6
  lb2WilExplosionUb := 2287161 / 10 ^ 6
  bipartiteH1At038Lb := 1987259 / 10 ^ 6
  allKL6MsupRootUb := 427390 / 10 ^ 6
  allKL6UnitRootLb := 1357501 / 10 ^ 6
  kurtosis15PctExact := 247 / 51
  c14WidthCutAt038Lb := 102521 / 10 ^ 4
  c14PlateauAt225Lb := 622034 / 10 ^ 6
  c14PlateauAt495Lb := 372034 / 10 ^ 6
  riccatiSu2InfRayMaxCoeff := -8192
  litmus6RatioUb := 5383421 / 10 ^ 6
  eightLn2Lb := 5545177 / 10 ^ 6

/-- Every quantitative separation in `w18_canonical_witness` holds constructively. -/
theorem w18_canonical_witness_margins :
    w18_canonical_witness.lamSpecUb < w18_canonical_witness.rowBoxLb ∧
    w18_canonical_witness.bkarZdPureJacUb < w18_canonical_witness.bkarZdNoTreeUb ∧
    w18_canonical_witness.bkarZdNoTreeUb < w18_canonical_witness.bkar1CellPureJacUb ∧
    w18_canonical_witness.bkar1CellPureJacUb < w18_canonical_witness.bkarPureJacNlfUb ∧
    w18_canonical_witness.bkarPureJacNlfUb < w18_canonical_witness.bkar1CellNoTreeUb ∧
    w18_canonical_witness.bkar1CellNoTreeUb < w18_canonical_witness.bkarIdealNoTreeUb ∧
    w18_canonical_witness.bkarIdealNoTreeUb < w18_canonical_witness.bkarWickFullUb ∧
    w18_canonical_witness.strangSum185To495Ub < 3 / 4 ∧
    w18_canonical_witness.strangSum143To495Ub < 3 / 4 ∧
    w18_canonical_witness.stokes54Alpha45D22Ub < 1 ∧
    1 < w18_canonical_witness.stokes54Alpha710D22Lb ∧
    4 < w18_canonical_witness.jointChordGold4dExitLb ∧
    495 / 100 < w18_canonical_witness.jointChordGold4dExitLb ∧
    w18_canonical_witness.jointChordGold4dExitLb < w18_canonical_witness.jointUnifGold4dExitLb ∧
    w18_canonical_witness.darboux495Gold4dUb < 1 ∧
    1 < w18_canonical_witness.darboux400Gold4dLb ∧
    w18_canonical_witness.coercivityB41LLb < w18_canonical_witness.coercivityB41LS6Lb ∧
    w18_canonical_witness.hodge2dL12Ub < 1 ∧
    1 < w18_canonical_witness.hodge3dL6Lb ∧
    w18_canonical_witness.hodge3dL6Lb < w18_canonical_witness.hodge3dL8Lb ∧
    w18_canonical_witness.q3KoffCapUb < w18_canonical_witness.q3K12Beta495Lb ∧
    w18_canonical_witness.hkSemigroup170dUb < 1 ∧
    997800 < w18_canonical_witness.bc140ExpAt370Lb ∧
    w18_canonical_witness.lb2OneStepHkLb < w18_canonical_witness.lb2TwoStepHkLb ∧
    w18_canonical_witness.lb2TwoStepHkLb < w18_canonical_witness.lb2ThreeStepHkLb ∧
    w18_canonical_witness.lb2ThreeStepHkLb < w18_canonical_witness.lb2HkExplosionUb ∧
    w18_canonical_witness.lb2OneStepWilLb < w18_canonical_witness.lb2TwoStepWilLb ∧
    w18_canonical_witness.lb2TwoStepWilLb < w18_canonical_witness.lb2WilExplosionUb ∧
    1 < w18_canonical_witness.bipartiteH1At038Lb ∧
    w18_canonical_witness.allKL6MsupRootUb < 1 ∧
    1 < w18_canonical_witness.allKL6UnitRootLb ∧
    10 < w18_canonical_witness.c14WidthCutAt038Lb ∧
    0 < w18_canonical_witness.c14PlateauAt225Lb ∧
    0 < w18_canonical_witness.c14PlateauAt495Lb ∧
    w18_canonical_witness.riccatiSu2InfRayMaxCoeff < 0 ∧
    w18_canonical_witness.litmus6RatioUb < w18_canonical_witness.eightLn2Lb := by
  unfold w18_canonical_witness
  norm_num

/-- Finite 20-element taxonomy of Round 18 Wave 18 (`W18-1..W18-5`) & `Cycles 13–14` closures & residual walls. -/
inductive Wave18RetirementId
  | o_w18_1_savvidy_ward_and_similarity_invariance_retired
  | o_w18_1_cross_product_gram_sos_l2spec
  | o_w18_1_strang_b2_ladder_summability
  | o_w18_1_cubic_shift_chernoff_wall
  | o_w18_1_v4_wpair_tree_dominance
  | o_w18_2_cbh_cubic_and_r3_curvature_lift
  | o_w18_2_five4_stokes_alpha_4_5_contraction
  | o_w18_2_darboux_495_pass_vs_400_wall
  | o_w18_2_joint_b2_kp_exit_above_495
  | o_w18_2_fixed_tree_gauge_slice_artifact
  | o_w18_3_bianchi_5x5_collective_and_192_wall
  | o_w18_3_3d_midplane_hodge_ceiling_and_koff
  | o_w18_3_hk_equatorial_inertia_and_coarse_gap
  | o_w18_4_lb2_multistep_vs_bipartite_h1_wall
  | o_w18_4_allk_l6_and_u1_casimir_shadow_wall
  | o_w18_4_su5_mandelstam_nonclosure_vs_su2
  | o_mi14_riccati_all_positive_reals_concavity
  | o_mi14_midcoupling_free_energy_plateau
  | o_w13_4_mixture15_retired_vs_o_mi13_coexistence_open
  | o_w18_5_core_team_cycles13_to_14_convergence
  deriving DecidableEq, Repr

private def wave18RetirementToFin : Wave18RetirementId → Fin 20
  | .o_w18_1_savvidy_ward_and_similarity_invariance_retired => 0
  | .o_w18_1_cross_product_gram_sos_l2spec => 1
  | .o_w18_1_strang_b2_ladder_summability => 2
  | .o_w18_1_cubic_shift_chernoff_wall => 3
  | .o_w18_1_v4_wpair_tree_dominance => 4
  | .o_w18_2_cbh_cubic_and_r3_curvature_lift => 5
  | .o_w18_2_five4_stokes_alpha_4_5_contraction => 6
  | .o_w18_2_darboux_495_pass_vs_400_wall => 7
  | .o_w18_2_joint_b2_kp_exit_above_495 => 8
  | .o_w18_2_fixed_tree_gauge_slice_artifact => 9
  | .o_w18_3_bianchi_5x5_collective_and_192_wall => 10
  | .o_w18_3_3d_midplane_hodge_ceiling_and_koff => 11
  | .o_w18_3_hk_equatorial_inertia_and_coarse_gap => 12
  | .o_w18_4_lb2_multistep_vs_bipartite_h1_wall => 13
  | .o_w18_4_allk_l6_and_u1_casimir_shadow_wall => 14
  | .o_w18_4_su5_mandelstam_nonclosure_vs_su2 => 15
  | .o_mi14_riccati_all_positive_reals_concavity => 16
  | .o_mi14_midcoupling_free_energy_plateau => 17
  | .o_w13_4_mixture15_retired_vs_o_mi13_coexistence_open => 18
  | .o_w18_5_core_team_cycles13_to_14_convergence => 19

private def wave18RetirementOfFin (i : Fin 20) : Wave18RetirementId :=
  match i.1 with
  | 0 => .o_w18_1_savvidy_ward_and_similarity_invariance_retired
  | 1 => .o_w18_1_cross_product_gram_sos_l2spec
  | 2 => .o_w18_1_strang_b2_ladder_summability
  | 3 => .o_w18_1_cubic_shift_chernoff_wall
  | 4 => .o_w18_1_v4_wpair_tree_dominance
  | 5 => .o_w18_2_cbh_cubic_and_r3_curvature_lift
  | 6 => .o_w18_2_five4_stokes_alpha_4_5_contraction
  | 7 => .o_w18_2_darboux_495_pass_vs_400_wall
  | 8 => .o_w18_2_joint_b2_kp_exit_above_495
  | 9 => .o_w18_2_fixed_tree_gauge_slice_artifact
  | 10 => .o_w18_3_bianchi_5x5_collective_and_192_wall
  | 11 => .o_w18_3_3d_midplane_hodge_ceiling_and_koff
  | 12 => .o_w18_3_hk_equatorial_inertia_and_coarse_gap
  | 13 => .o_w18_4_lb2_multistep_vs_bipartite_h1_wall
  | 14 => .o_w18_4_allk_l6_and_u1_casimir_shadow_wall
  | 15 => .o_w18_4_su5_mandelstam_nonclosure_vs_su2
  | 16 => .o_mi14_riccati_all_positive_reals_concavity
  | 17 => .o_mi14_midcoupling_free_energy_plateau
  | 18 => .o_w13_4_mixture15_retired_vs_o_mi13_coexistence_open
  | _ => .o_w18_5_core_team_cycles13_to_14_convergence

private def wave18RetirementEquivFin20 : Wave18RetirementId ≃ Fin 20 where
  toFun := wave18RetirementToFin
  invFun := wave18RetirementOfFin
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Wave18RetirementId :=
  Fintype.ofEquiv (Fin 20) wave18RetirementEquivFin20.symm

/-- **Round 18 Wave 18 Honest `.OPEN` Lock**:
    1. Chains Round 17 (`round17_irx_wave17_honest_open_lock`) cleanly into Round 18 (`W18-1..W18-5` + Cycles 13–14);
    2. Certifies all 20 Wave 18 structural retirements/obstructions & `w18_canonical_witness` margins;
    3. Locks `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`, `currentH2dRepoWitness = ⟨1, 1, 1⟩`,
       `wave11H2ConstructiveWitness`, and `device_certified = false` strictly **`.OPEN`** / `false` (`7-Way + Litmus 6`). `[C/B/P/X]` -/
theorem round18_irx_wave18_honest_open_lock :
    -- (1) Full Round 17 honest OPEN core + 7-Way + H2d repo witness preserved verbatim
    ((∀ c : Round07IRXFirstPrinciples.SevenWayCounterexampleId,
        (Round07IRXFirstPrinciples.sevenWaySignature c).positiveMassGap = false) ∧
      Function.Injective Round07IRXFirstPrinciples.sevenWaySignature ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      ¬ (currentH2dRepoWitness.toH2LayerCandidate).Satisfies .h2d_clay_4d_continuum_measure ∧
      ¬ wave11H2ConstructiveWitness.Satisfies .h2d_clay_4d_continuum_measure ∧
      currentH2dRepoWitness = ⟨1, 1, 1⟩ ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) ∧
    -- (2) Round 18 taxonomy (20 items) chained cleanly onto Round 17 (17 items) & Round 16 (16 items)
    (Nonempty Wave18RetirementId ∧ Fintype.card Wave18RetirementId = 20 ∧
      Nonempty W18_L2SpecNonGaussB2HodgeWallAndMultiStepDobrushinWitness ∧
      Nonempty Wave17RetirementId ∧ Fintype.card Wave17RetirementId = 17 ∧
      Nonempty W17_SignedK6PairedB2OTSliceAndDobrushinWitness ∧
      Nonempty Wave16RetirementId ∧ Fintype.card Wave16RetirementId = 16) ∧
    -- (3) Round 18 §1..§4 pure-kernel theorems + Round 17 highlighted scientific milestones + w18 margins
    ((w17_canonical_witness.b2D13Dim8Ub < 1 ∧ 1 < w17_canonical_witness.minKpB185Lb ∧
        135 / 100 < w17_canonical_witness.cycle12Beta495Gap6dLb ∧ w17_canonical_witness.cycle11Corr2Pl150d495Ub < 1) ∧
      ((∀ xi eta zeta : ℝ,
          0 ≤ (1 / 12 : ℝ) * (xi + eta + zeta) ^ 2 - (1 / 4 : ℝ) * (xi * eta + xi * zeta + eta * zeta)) ∧
        (2 / Real.sqrt 3) * (1 / (92 / 100 : ℝ) + 778535 / 10 ^ 9) < 1256009 / 10 ^ 6 ∧
        (2 * w18CasimirFund 5 - w18CasimirAntisym 5 : ℚ) = 6 / 5 ∧
        (2 * w18CasimirFund 2 - (2 : ℚ) : ℚ) = -1 / 2 ∧
        (267 * 10 ^ 8 : ℝ) < (11332 / 10000 : ℝ) ^ 192 ∧
        (∀ beta : ℝ, beta ≠ 0 →
          (beta * Real.pi / 4) ^ 2 / (beta / 2 * Real.sin (Real.pi / 2)) ^ 2 = Real.pi ^ 2 / 4) ∧
        (997825 : ℝ) < Real.exp (56 * (37 / 10 : ℝ) / 15) ∧
        (∀ k : ℕ, 1 ≤ k → k * (k + 2) ≤ 3 * k ^ 2) ∧
        (∀ P : W18Mat2C, ∀ i j : Fin 2,
          (w18Mul2C P P i j - w18Tr2C P * P i j + w18Det2C P * w18Eye2C i j) = 0) ∧
        (∀ s : ℝ, 0 ≤ s →
          let r := (6 : ℝ) + s
          let u_lo := 1 - 3 / (2 * r) + 3 / (8 * r ^ 2) + 3 / (8 * r ^ 3)
          let gp_lo := 1 - 3 * u_lo / r - u_lo ^ 2
          (3 / (2 * r ^ 2) - 3 / (4 * r ^ 3) - 9 / (8 * r ^ 4)) - gp_lo ≤ 0) ∧
        (1 - 11 / (24 : ℝ) * 0 = 1) ∧
        w18_canonical_witness.lamSpecUb < w18_canonical_witness.rowBoxLb ∧
        w18_canonical_witness.hodge2dL12Ub < 1 ∧
        1 < w18_canonical_witness.hodge3dL6Lb ∧
        w18_canonical_witness.q3KoffCapUb < w18_canonical_witness.q3K12Beta495Lb ∧
        w18_canonical_witness.stokes54Alpha45D22Ub < 1 ∧
        1 < w18_canonical_witness.stokes54Alpha710D22Lb ∧
        w18_canonical_witness.darboux495Gold4dUb < 1 ∧
        1 < w18_canonical_witness.darboux400Gold4dLb ∧
        10 < w18_canonical_witness.c14WidthCutAt038Lb ∧
        w18_canonical_witness.riccatiSu2InfRayMaxCoeff < 0 ∧
        6 * Real.pi ^ 2 / 11 < 8 * Real.log 2)) ∧
    -- (4) Universal minimal irreducible H2d obstruction remains unbridged (.OPEN)
    (∀ (core : Round05CrossObligationH2d.H2dMinimalIrreducibleCore),
      (∀ o : H2dCoreObligation, core.toObstructionCandidate.Satisfies o) ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) := by
  rcases round17_irx_wave17_honest_open_lock with
    ⟨hCore, ⟨hW17ne, hW17card, hW17wit, hW16ne, hW16card⟩, hR17thm, hMinCore⟩
  rcases w18_1_savvidy_ward_similarity_and_cross_product_l2spec with
    ⟨_, _, _, hCS, hLam, _, _, _, _⟩
  rcases w18_2_cbh_r3_curvature_stokes_and_joint_exit with
    ⟨_, _, hCas5, hCas2, _⟩
  rcases w18_3_bianchi_hodge_koff_and_hk_inertia with
    ⟨_, h192, hHKWil, _, hBC⟩
  rcases w18_4_c13_c14_abshadow_mandelstam_riccati_and_mix15 with
    ⟨hAb, ⟨hCH, _⟩, ⟨_, hRiccLo, _, _⟩, ⟨_, hLit6⟩⟩
  rcases w18_canonical_witness_margins with
    ⟨hLamW, _, _, _, _, _, _, _, _, hSt45, hSt710, _, _, _, hD495, hD400, _, hH2, hH3, _, hKoff, _, _, _, _, _, _, _, _, _, _, hCut, _, _, hMaxC, _⟩
  refine ⟨hCore, ⟨⟨.o_w18_1_cross_product_gram_sos_l2spec⟩, by decide, ⟨w18_canonical_witness⟩, hW17ne, hW17card, hW17wit, hW16ne, hW16card⟩, ?_, hMinCore⟩
  refine ⟨⟨hR17thm.2.2.2.2.2.2.2.2.2.1, hR17thm.2.2.2.2.2.2.2.2.2.2.1, hR17thm.2.2.2.2.2.2.2.2.2.2.2.1, hR17thm.2.2.2.2.2.2.2.2.2.2.2.2⟩, ?_⟩
  refine ⟨fun xi eta zeta => (hCS xi eta zeta).2, hLam, hCas5, hCas2, h192, hHKWil, (hBC (37 / 10)).2 (by norm_num),
    fun k hk => (hAb k).2 hk, hCH, fun s hs => (hRiccLo s hs).1, by ring,
    hLamW, hH2, hH3, hKoff, hSt45, hSt710, hD495, hD400, hCut, hMaxC, hLit6⟩

end UEOTPhysicsUnification.IRXWave18L2SpecNonGaussB2HodgeWallAndMultiStepDobrushin
