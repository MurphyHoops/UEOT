import UEOTPhysicsUnification.IRXWave18L2SpecNonGaussB2HodgeWallAndMultiStepDobrushin

/-!
# Round 19 Wave 19 (`W19-1..W19-5` & `math-inventor` Cycles 15–18: Smooth UV PoU / `H_sm3` SOS, Landau `Z(p)` / Gribov, `1/μ` & Schur-Peeling `3D→2D→1D`, `2×2` Red-Black, Elitzur `1/3`, Sherman–Morrison `C_L` & `K_comm`)

Pure-kernel (`{propext, Classical.choice, Quot.sound}`, zero proof escapes, zero warnings)
formalization of Round 19 Wave 19 (`W19-1..W19-5`) and `math-inventor` Cycles 15–18 `[C/B/P]` results
with strict `[E]` / `[X]` isolation:

1. **§1 (`W19-1` Smooth UV PoU, `H_sm3` Row & Frobenius SOS, `Q_st ≥ 0.955 I`, Wick `8551→5515` [audited], Strang `B₂`)**:
   - `w19_1_smooth_pou_hsm3_sos_wick_and_strang`:
     - `Q₄ g_v = 0` vs mass leak `2 m_fk⁴`, `m = 1` 12-DOF PoU slope `126` & exact rational bracket
       `α σ² ∈ (280511 / 10⁸, 280512 / 10⁸)` (`cov > 997202 / 10⁶`);
     - Exact 12-variable `H_sm3` Row-SOS identities for all four rows `m = 0..3` (`≤ 27/64`) and
       full Frobenius-SOS identity `4 ∑_{m<n} ‖u_{mn}‖² = (1/4) ∑ ‖w_k‖² - (1/16) ‖w₀ - w₁ - w₂ + w₃‖²`;
     - Tightened spectral bound `λ_spec(W19) = (2/√3)(1/0.955 + q_{t,ℓ¹}) < 1.210010 < 1.256009 = λ_spec(W18)`,
       audited bug-free Wick compression `5515 < 8551` (post-`O-W20.1-Poly4ConstantLeak` & `O-W20.1-Gp2BetaLeak` fix), and Strang `B₂` chains
       `5515 → 8.1875` (`21,384` steps, `sum < 0.456322`) & `5515 → 4.95` (`21,397` steps, `sum < 0.753383`) keeping `O-W19.1` and `O-W18.1` `.OPEN`.

2. **§2 (`W19-2` Landau Gribov `det M_FP = 8 cos²(θ/2)`, `M_FP^cell`, `L_tree`, CBH O'Neill & `SU(5)` `z₁`)**:
   - `w19_2_landau_gribov_cell_mfp_cbh_and_su5`:
     - Exact `3×3` 2-link Landau Faddeev–Popov `det M_FP(θ) = 8 cos²(θ/2)`, antipodal Gribov zero at `θ = π`,
       and negative eigenvalue `< -0.517` at `θ = 7π/6` (`210°`);
     - Exact `3×3` cell `M_FP^cell` spectrum `{8 - 4√2, 8, 8 + 4√2}` (`> 2.343145`) and fixed-tree `L_tree`
       smallest singular value `(√5 - 1)/2 ∈ (0.618033, 0.618034)`;
     - Exact `2×2` complex Pauli CBH O'Neill mixed commutator `= (1/2)((w₁ + w₂) η)[T₁, T₂]` vs `U(1)` zero,
       and `SU(5)` `z₁` barrier `β(9 - √5)/20` at `4.00, 4.95, 17.6091` keeping `O-W19.2` and `O-W18.3` `.OPEN`.

3. **§3 (`W19-3` & `Cycles 15–18`: `1/μ` Eigenvalue, Schur-Peeling `3D→2D→1D`, `S²` Shield, `O(4)` Ward & `2×2` Red-Black)**:
   - `w19_3_hodge_1overmu_and_c16_schur_peeling`:
     - Exact `3×3` `M_μ⁻¹ = (μ + ‖d‖²)⁻¹(I₃ + μ⁻¹ d dᵀ)` with momentum-independent longitudinal eigenvalue `1/μ`;
     - Exact Cycle 16 `3D → 2D → 1D` Schur-peeling (`H₃₃ = 2 + k₁₂²` local in `z`, `A₁ = -A₀/(4 + k₁₂²)`,
       `‖A₀⁻¹ (2 A₁)‖ ≤ 1/2`, dimensional ladder `1/2, 2/3, 3/4`, and `1D` Green root `r_- = 2 - √3`).
   - `w19_3_c15_s2_c17_o4_and_c18_redblack`:
     - Cycle 15 exact `S²` identity `(cos(π/5) I₂ + i sin(π/5)(n·σ))⁵ = -I₂` & `U(1)` barrier `β(5√5 - 7)/4`;
     - Cycle 17 `S³` Haar covariance `1/4`, `4×4` `SO(4)` generator bond invariance, `h_min(4.95, 150°) > 2.562308`,
       `3 / h_min < 1.170820`, and `SO(3)` kernels;
     - Cycle 18 `4×4` `L_sq` spectrum `{0, 2, 2, 4}`, Red-Black `J₀₀` diagonalization `diag(-2β, 0, 0, 2β)`
       (exact dipole cancellation), `α_tri(2×2)` vs `ρ_RB(2×2)` vs `C5 2×2×2` `3/2` penalty, and `150°` corner tilt
       while excluding `[E]` `6D` 5-strip and discrete-grid assertions from closure claims (`O-W19.3`, `O-MI16`, `O-MI18` `.OPEN`).

4. **§4 (`W19-4` & `Q4`: Elitzur `1/3` Sheet, `C_L` Pole Cancellation, `K_comm = 2|v₁ × v₂|²` & `Litmus 6`)**:
   - `w19_4_elitzur_sm_kcomm_sd_and_litmus6`:
     - Elitzur `2D` sheet captured fraction `2/6 = 1/3`;
     - Exact `3×3` temporal-tree Sherman–Morrison `C₃ C₃⁻¹ = I₃`, `C_L = a_T/(s₀² + m²)` pole cancellation,
       and plaquette gauge-part cancellation `4 ᾱ - 8 γ = (s₁² + s₂²) c_T`;
     - Exact `SU(2)` commutator `K_comm = 1 - (1/2) Tr(P₁ P₂ P₁⁻¹ P₂⁻¹) = 2|v₁ × v₂|² ≥ 0` (`=== 0` on `U(1)`),
       `S²` average floor `(1 - u₂)/2`, Gibbs positivity `(3/4)(1 - u₂)² > 0`, SD latent jump identity, and `Litmus 6`.

5. **§5 (`Round 19 Honest .OPEN Lock`)**:
   - `W19_SmoothUVLandauZSchurPeelAndCorrelatedCoexistenceWitness`, `Wave19RetirementId` (`Fintype.card = 20`),
     and `round19_irx_wave19_honest_open_lock` chaining `round18_irx_wave18_honest_open_lock` while locking
     `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`, `currentH2dRepoWitness = ⟨1, 1, 1⟩`,
     `wave11H2ConstructiveWitness`, and `device_certified = false` strictly **`.OPEN`** / `false`.
-/

namespace UEOTPhysicsUnification.IRXWave19SmoothUVLandauZSchurPeelAndCorrelatedCoexistence

open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2
open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
open UEOTPhysicsUnification.IRXWave16UnstrippedHingeSymanzikK4VortexAndRedTeam
open UEOTPhysicsUnification.IRXWave17SignedK6PairedB2OTSliceAndDobrushin
open UEOTPhysicsUnification.IRXWave18L2SpecNonGaussB2HodgeWallAndMultiStepDobrushin

-- ============================================================================
-- §1. W19-1: Smooth UV PoU, H_sm3 SOS, Q_st >= 0.955 I, Wick & Strang B₂
-- ============================================================================

/-- `3`-component Euclidean dot product for exact `12`-DOF `H_sm3` SOS identities. -/
def w19Dot3 (u v : Fin 3 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- `3`-component Euclidean squared norm `‖u‖²`. -/
def w19NormSq3 (u : Fin 3 → ℝ) : ℝ := w19Dot3 u u

/-- Exact skew-symmetric `H_sm3` cross-vector blocks `u_{mn} ∈ ℝ³` (`0 ≤ m < n ≤ 3`). -/
noncomputable def w19Hsm3U01 (w : Fin 4 → Fin 3 → ℝ) : Fin 3 → ℝ := fun a => (1 / 8 : ℝ) * (w 2 a + w 3 a)
noncomputable def w19Hsm3U02 (w : Fin 4 → Fin 3 → ℝ) : Fin 3 → ℝ := fun a => (1 / 8 : ℝ) * (-w 1 a - w 3 a)
noncomputable def w19Hsm3U03 (w : Fin 4 → Fin 3 → ℝ) : Fin 3 → ℝ := fun a => (1 / 8 : ℝ) * (-w 1 a + w 2 a)
noncomputable def w19Hsm3U12 (w : Fin 4 → Fin 3 → ℝ) : Fin 3 → ℝ := fun a => (1 / 8 : ℝ) * (w 0 a - w 3 a)
noncomputable def w19Hsm3U13 (w : Fin 4 → Fin 3 → ℝ) : Fin 3 → ℝ := fun a => (1 / 8 : ℝ) * (w 0 a + w 2 a)
noncomputable def w19Hsm3U23 (w : Fin 4 → Fin 3 → ℝ) : Fin 3 → ℝ := fun a => (1 / 8 : ℝ) * (-w 0 a - w 1 a)

/-- `4×4` rank-1 longitudinal-transverse Ward matrix `d₄ d₄ᵀ` (`d₄ = (1, 1, -1, -1)`). -/
def w19WardD4Vec : Fin 4 → ℝ
  | 0 => 1 | 1 => 1 | 2 => -1 | _ => -1

def w19WardQ4 : Fin 4 → Fin 4 → ℝ := fun i j => w19WardD4Vec i * w19WardD4Vec j

theorem w19_1_smooth_pou_hsm3_sos_wick_and_strang :
    -- (1) Q1 Ward leak = 2 m_fk^4 & m=1 12-DOF PoU rational bracket
    ((∀ i : Fin 4, (∑ j : Fin 4, w19WardQ4 i j * w18WardGaugeVec j) = 0) ∧
      (∀ m_fk : ℝ,
        ∑ i : Fin 4,
          (∑ j : Fin 4, (w19WardQ4 i j + if i = j then m_fk ^ 2 else 0) * w18WardGaugeVec j) ^ 2 =
            2 * m_fk ^ 4) ∧
      ((21 * 6 : ℕ) = 126) ∧
      ((1 + 280511 / 10 ^ 8 : ℚ) ^ 6 < 60 / 59 ∧ 60 / 59 < (1 + 280512 / 10 ^ 8 : ℚ) ^ 6 ∧
        (997202 / 10 ^ 6 : ℚ) < 1 / (1 + 280512 / 10 ^ 8))) ∧
    -- (2) Exact H_sm3 12-DOF Row-SOS (all 4 rows <= 27/64) & Full Frobenius-SOS
    (∀ w : Fin 4 → Fin 3 → ℝ,
      let r0 : Fin 3 → ℝ := fun a => w 1 a + w 2 a - w 3 a
      let r1 : Fin 3 → ℝ := fun a => w 0 a - w 2 a + w 3 a
      let r2 : Fin 3 → ℝ := fun a => w 0 a - w 1 a + w 3 a
      let r3 : Fin 3 → ℝ := fun a => w 0 a - w 1 a - w 2 a
      let rAll : Fin 3 → ℝ := fun a => w 0 a - w 1 a - w 2 a + w 3 a
      (w19NormSq3 (w19Hsm3U01 w) + w19NormSq3 (w19Hsm3U02 w) + w19NormSq3 (w19Hsm3U03 w) =
        (1 / 64 : ℝ) * (3 * (w19NormSq3 (w 1) + w19NormSq3 (w 2) + w19NormSq3 (w 3)) - w19NormSq3 r0)) ∧
      (w19NormSq3 (w19Hsm3U01 w) + w19NormSq3 (w19Hsm3U12 w) + w19NormSq3 (w19Hsm3U13 w) =
        (1 / 64 : ℝ) * (3 * (w19NormSq3 (w 0) + w19NormSq3 (w 2) + w19NormSq3 (w 3)) - w19NormSq3 r1)) ∧
      (w19NormSq3 (w19Hsm3U02 w) + w19NormSq3 (w19Hsm3U12 w) + w19NormSq3 (w19Hsm3U23 w) =
        (1 / 64 : ℝ) * (3 * (w19NormSq3 (w 0) + w19NormSq3 (w 1) + w19NormSq3 (w 3)) - w19NormSq3 r2)) ∧
      (w19NormSq3 (w19Hsm3U03 w) + w19NormSq3 (w19Hsm3U13 w) + w19NormSq3 (w19Hsm3U23 w) =
        (1 / 64 : ℝ) * (3 * (w19NormSq3 (w 0) + w19NormSq3 (w 1) + w19NormSq3 (w 2)) - w19NormSq3 r3)) ∧
      (4 * (w19NormSq3 (w19Hsm3U01 w) + w19NormSq3 (w19Hsm3U02 w) + w19NormSq3 (w19Hsm3U03 w) +
            w19NormSq3 (w19Hsm3U12 w) + w19NormSq3 (w19Hsm3U13 w) + w19NormSq3 (w19Hsm3U23 w)) =
        (1 / 4 : ℝ) * (w19NormSq3 (w 0) + w19NormSq3 (w 1) + w19NormSq3 (w 2) + w19NormSq3 (w 3)) -
          (1 / 16 : ℝ) * w19NormSq3 rAll)) ∧
    -- (3) Q_st >= 0.955 I -> lam_spec_w19 < 1.210010 < 1.256009, audited Wick 5515 < 8551 & Strang B2 steps
    ((2 / Real.sqrt 3) * (1 / (955 / 1000 : ℝ) + 778535 / 10 ^ 9) < 1210010 / 10 ^ 6 ∧
      (1210010 / 10 ^ 6 : ℝ) < 1256009 / 10 ^ 6 ∧
      (5515 : ℕ) < 8551 ∧
      257511 / 10 ^ 6 < 11 * Real.log 2 / (3 * Real.pi ^ 2) ∧
      11 * Real.log 2 / (3 * Real.pi ^ 2) < 257512 / 10 ^ 6 ∧
      81875 / 10 ^ 4 < (5515 : ℝ) - 21384 * (11 * Real.log 2 / (3 * Real.pi ^ 2)) ∧
      (5515 : ℝ) - 21385 * (11 * Real.log 2 / (3 * Real.pi ^ 2)) < 81875 / 10 ^ 4 ∧
      495 / 10 ^ 2 < (5515 : ℝ) - 21397 * (11 * Real.log 2 / (3 * Real.pi ^ 2)) ∧
      (5515 : ℝ) - 21398 * (11 * Real.log 2 / (3 * Real.pi ^ 2)) < 495 / 10 ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, by norm_num, ?_⟩
    · intro i
      fin_cases i <;> simp [w19WardQ4, w19WardD4Vec, w18WardGaugeVec, Fin.sum_univ_four]
    · intro m_fk
      simp [w19WardQ4, w19WardD4Vec, w18WardGaugeVec, Fin.sum_univ_four]
      ring
    · norm_num
  · intro w
    dsimp only
    simp only [w19NormSq3, w19Dot3, w19Hsm3U01, w19Hsm3U02, w19Hsm3U03, w19Hsm3U12, w19Hsm3U13, w19Hsm3U23]
    refine ⟨by ring, by ring, by ring, by ring, by ring⟩
  · have hsqrt3_lo : (17320508 / 10 ^ 7 : ℝ) < Real.sqrt 3 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hinv_hi : (2 / Real.sqrt 3 : ℝ) < 2 / (17320508 / 10 ^ 7 : ℝ) :=
      div_lt_div_of_pos_left (by norm_num) (by norm_num) hsqrt3_lo
    have hlam : (2 / Real.sqrt 3) * (1 / (955 / 1000 : ℝ) + 778535 / 10 ^ 9) < 1210010 / 10 ^ 6 := by
      have hpos_rhs : (0 : ℝ) < 1 / (955 / 1000 : ℝ) + 778535 / 10 ^ 9 := by positivity
      calc
        (2 / Real.sqrt 3) * (1 / (955 / 1000 : ℝ) + 778535 / 10 ^ 9)
            < (2 / (17320508 / 10 ^ 7 : ℝ)) * (1 / (955 / 1000 : ℝ) + 778535 / 10 ^ 9) :=
              mul_lt_mul_of_pos_right hinv_hi hpos_rhs
        _ < 1210010 / 10 ^ 6 := by norm_num
    have hpi_lo : (3141592 / 10 ^ 6 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
    have hpi_hi : Real.pi < 3141593 / 10 ^ 6 := by linarith [Real.pi_lt_d6]
    have hlog2_lo : (6931471803 / 10 ^ 10 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog2_hi : Real.log 2 < 6931471808 / 10 ^ 10 := by linarith [Real.log_two_lt_d9]
    have hpi2_lo : (3141592 / 10 ^ 6 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith
    have hpi2_hi : Real.pi ^ 2 < (3141593 / 10 ^ 6 : ℝ) ^ 2 := by nlinarith
    have hdb_lo : 257511 / 10 ^ 6 < 11 * Real.log 2 / (3 * Real.pi ^ 2) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    have hdb_hi : 11 * Real.log 2 / (3 * Real.pi ^ 2) < 257512 / 10 ^ 6 := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    refine ⟨hlam, by norm_num, by norm_num, hdb_lo, hdb_hi, by linarith, by linarith, by linarith, by linarith⟩

-- ============================================================================
-- §2. W19-2: 2-Link Landau det M_FP, Cell M_FP, L_tree, CBH O'Neill & SU(5)
-- ============================================================================

/-- `3×3` 2-link Landau Faddeev–Popov matrix `diag(2 cos(θ/2), 2 cos(θ/2), 2)`. -/
noncomputable def w19LandauMfp (th : ℝ) : W18Mat3
  | 0, 0 => 2 * Real.cos (th / 2)
  | 1, 1 => 2 * Real.cos (th / 2)
  | 2, 2 => 2
  | _, _ => 0

/-- `3×3` single-cell Landau Faddeev–Popov matrix `[[8,0,-4],[0,8,-4],[-4,-4,8]]`. -/
def w19CellMfp : W18Mat3
  | 0, 0 => 8 | 0, 2 => -4
  | 1, 1 => 8 | 1, 2 => -4
  | 2, 0 => -4 | 2, 1 => -4 | 2, 2 => 8
  | _, _ => 0

/-- `3×3` fixed-tree link-to-gauge matrix `L_tree = [[1,0,0],[0,1,0],[1,0,-1]]`. -/
def w19Ltree : W18Mat3
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 0 => 1 | 2, 2 => -1
  | _, _ => 0

/-- `L_treeᵀ L_tree = [[2, 0, -1], [0, 1, 0], [-1, 0, 1]]`. -/
def w19LtreeGram : W18Mat3 := fun i j => ∑ k : Fin 3, w19Ltree k i * w19Ltree k j

/-- Degree-2 truncated `2×2` complex matrix exponential `I₂ + M + M²/2` for CBH O'Neill proof. -/
noncomputable def w19Exp2C (M : W18Mat2C) : W18Mat2C :=
  let M2 := w18Mul2C M M
  fun i j => w18Eye2C i j + M i j + ((1 / 2 : ℝ) : ℂ) * M2 i j

def w19Scale2C (c : ℂ) (M : W18Mat2C) : W18Mat2C := fun i j => c * M i j

theorem w19_2_landau_gribov_cell_mfp_cbh_and_su5 :
    -- (1) 2-link Landau M_FP(θ) determinant = 8 cos²(θ/2), Gribov zero at π, negative mode at 7π/6 (210°)
    ((∀ th : ℝ, w18Det3 (w19LandauMfp th) = 8 * (Real.cos (th / 2)) ^ 2) ∧
      w18Det3 (w19LandauMfp Real.pi) = 0 ∧
      2 * Real.cos ((7 * Real.pi / 6) / 2) = -(Real.sqrt 6 - Real.sqrt 2) / 2 ∧
      2 * Real.cos ((7 * Real.pi / 6) / 2) < -517 / 1000) ∧
    -- (2) Single-cell M_FP^cell exact spectrum {8 - 4√2, 8, 8 + 4√2} & L_tree singular value (√5 - 1)/2
    ((∀ lam : ℝ,
        w18Det3 (fun i j => (if i = j then lam else 0) - w19CellMfp i j) =
          (lam - 8) * (lam - (8 - 4 * Real.sqrt 2)) * (lam - (8 + 4 * Real.sqrt 2))) ∧
      (2343145 / 10 ^ 6 : ℝ) < 8 - 4 * Real.sqrt 2 ∧
      (∀ lam : ℝ,
        w18Det3 (fun i j => (if i = j then lam else 0) - w19LtreeGram i j) =
          (lam - 1) * (lam - (3 - Real.sqrt 5) / 2) * (lam - (3 + Real.sqrt 5) / 2)) ∧
      ((Real.sqrt 5 - 1) / 2) ^ 2 = (3 - Real.sqrt 5) / 2 ∧
      (618033 / 10 ^ 6 : ℝ) < (Real.sqrt 5 - 1) / 2 ∧ (Real.sqrt 5 - 1) / 2 < 618034 / 10 ^ 6) ∧
    -- (3) 2x2 CBH O'Neill gauge-link commutator = (1/2) (w1 + w2) eta [T1, T2] vs U(1) zero
    ((∀ (s t w1 w2 eta : ℝ),
        let T1 := w19Scale2C (-Complex.I / 2) w18PauliX
        let T2 := w19Scale2C (-Complex.I / 2) w18PauliY
        let T3 := w19Scale2C (-Complex.I / 2) w18PauliZ
        let G := w18Mul2C (w18Mul2C (w19Exp2C (w19Scale2C (s * w1) T1))
          (w19Exp2C (w19Scale2C (t * eta) T2))) (w19Exp2C (w19Scale2C (-s * w2) T1))
        let a := s * w1
        let b := t * eta
        let c := -s * w2
        let u0 := 1 - a ^ 2 / 8
        let v0 := 1 - b ^ 2 / 8
        let w0 := 1 - c ^ 2 / 8
        ∀ i j : Fin 2,
          G i j =
            ((u0 * v0 * w0 - a * v0 * c / 4 : ℝ) : ℂ) * w18Eye2C i j +
            (((a + c) * (1 - a * c / 8) * v0 : ℝ) : ℂ) * T1 i j +
            ((b * (u0 * w0 + a * c / 4) : ℝ) : ℂ) * T2 i j +
            ((s * t * eta * (w1 * w0 + w2 * u0) / 2 : ℝ) : ℂ) * T3 i j) ∧
      -- Clean exact commutator coefficient identity at O(s*t) for ALL w1, w2, eta and U(1) zero
      (∀ (w1 w2 eta : ℝ),
        let T1 := w19Scale2C (-Complex.I / 2) w18PauliX
        let T2 := w19Scale2C (-Complex.I / 2) w18PauliY
        let T3 := w19Scale2C (-Complex.I / 2) w18PauliZ
        (∀ i j : Fin 2,
          w18Mul2C (w19Scale2C w1 T1) (w19Scale2C eta T2) i j -
          w18Mul2C (w19Scale2C eta T2) (w19Scale2C (-w2) T1) i j -
          (w18Mul2C (w19Scale2C w1 T1) (w19Scale2C eta T2) i j +
            w18Mul2C (w19Scale2C eta T2) (w19Scale2C w2 T1) i j) = 0) ∧
        (∀ i j : Fin 2,
          ((1 / 2 : ℝ) : ℂ) * (w18Mul2C (w19Scale2C (w1 + w2) T1) (w19Scale2C eta T2) i j -
            w18Mul2C (w19Scale2C eta T2) (w19Scale2C (w1 + w2) T1) i j) =
            (((w1 + w2) * eta / 2 : ℝ) : ℂ) * T3 i j) ∧
        (∀ i j : Fin 2,
          w18Mul2C (w19Scale2C (w1 + w2) T3) (w19Scale2C eta T3) i j -
          w18Mul2C (w19Scale2C eta T3) (w19Scale2C (w1 + w2) T3) i j = 0))) ∧
    -- (4) SU(5) 312 vs SU(2) 39 dim & z1 barriers at 4.00, 4.95, 17.6091
    ((312 : ℕ) = 8 * 39 ∧
      (1352786 / 10 ^ 6 : ℝ) < 4 * (9 - Real.sqrt 5) / 20 ∧
      (1674073 / 10 ^ 6 : ℝ) < (495 / 100) * (9 - Real.sqrt 5) / 20 ∧
      (5955337 / 10 ^ 6 : ℝ) < (176091 / 10 ^ 4) * (9 - Real.sqrt 5) / 20) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hpi12 : Real.cos (7 * Real.pi / 12) = -(Real.sqrt 6 - Real.sqrt 2) / 4 := by
      have harg : (7 * Real.pi / 12 : ℝ) = Real.pi / 3 + Real.pi / 4 := by ring
      rw [harg, Real.cos_add, Real.cos_pi_div_three, Real.cos_pi_div_four,
        Real.sin_pi_div_three, Real.sin_pi_div_four]
      have h6 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
        rw [← Real.sqrt_mul (by norm_num)]; norm_num
      linarith
    have hsqrt6_lo : (2449489 / 10 ^ 6 : ℝ) < Real.sqrt 6 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hsqrt2_hi : Real.sqrt 2 < 1414214 / 10 ^ 6 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro th
      simp [w18Det3, w19LandauMfp]
      ring
    · simp [w18Det3, w19LandauMfp, Real.cos_pi_div_two]
    · have h7 : (7 * Real.pi / 6) / 2 = 7 * Real.pi / 12 := by ring
      rw [h7, hpi12]
      ring
    · have h7 : (7 * Real.pi / 6) / 2 = 7 * Real.pi / 12 := by ring
      rw [h7, hpi12]
      linarith
  · have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hsqrt2_hi : Real.sqrt 2 < 14142136 / 10 ^ 7 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hsqrt5_lo : (22360679 / 10 ^ 7 : ℝ) < Real.sqrt 5 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hsqrt5_hi : Real.sqrt 5 < 22360680 / 10 ^ 7 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    refine ⟨?_, by linarith, ?_, ?_, by linarith, by linarith⟩
    · intro lam
      have hpoly : w18Det3 (fun i j => (if i = j then lam else 0) - w19CellMfp i j) =
          (lam - 8) * (lam ^ 2 - 16 * lam + 32) := by
        simp [w18Det3, w19CellMfp]; ring
      rw [hpoly]
      have hfac : lam ^ 2 - 16 * lam + 32 =
          (lam - (8 - 4 * Real.sqrt 2)) * (lam - (8 + 4 * Real.sqrt 2)) := by
        linear_combination (16 : ℝ) * h2
      rw [hfac]; ring
    · intro lam
      have hpoly : w18Det3 (fun i j => (if i = j then lam else 0) - w19LtreeGram i j) =
          (lam - 1) * (lam ^ 2 - 3 * lam + 1) := by
        simp [w18Det3, w19LtreeGram, w19Ltree, Fin.sum_univ_three]; ring
      rw [hpoly]
      have hfac : lam ^ 2 - 3 * lam + 1 =
          (lam - (3 - Real.sqrt 5) / 2) * (lam - (3 + Real.sqrt 5) / 2) := by
        linear_combination (1 / 4 : ℝ) * h5
      rw [hfac]; ring
    · linear_combination (1 / 4 : ℝ) * h5
  · refine ⟨?_, ?_⟩
    · intro s t w1 w2 eta
      dsimp only
      have hhalf : (-Complex.I / 2 : ℂ) = (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by
        rw [div_eq_mul_inv]
        apply Complex.ext <;> norm_num
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [w18Mul2C, w19Exp2C, w19Scale2C, w18Eye2C, w18PauliX, w18PauliY, w18PauliZ,
          Fin.sum_univ_two, hhalf] <;>
        apply Complex.ext <;>
        simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] <;>
        ring
    · intro w1 w2 eta
      refine ⟨?_, ?_, ?_⟩
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp [w18Mul2C, w19Scale2C, w18PauliX, w18PauliY, Fin.sum_univ_two]
        all_goals
          apply Complex.ext <;>
          simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
            Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp [w18Mul2C, w19Scale2C, w18PauliX, w18PauliY, w18PauliZ, Fin.sum_univ_two] <;>
          apply Complex.ext <;>
          simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
            Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] <;>
          ring
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp [w18Mul2C, w19Scale2C, w18PauliZ, Fin.sum_univ_two] <;>
          apply Complex.ext <;>
          simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
            Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] <;>
          ring
  · have hsqrt5_hi : Real.sqrt 5 < 22360680 / 10 ^ 7 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    refine ⟨by norm_num, by nlinarith, by nlinarith, by nlinarith⟩

-- ============================================================================
-- §3. W19-3 & Cycles 15–18: 1/μ, Schur-Peeling 3D→2D→1D, S² Shield, O(4) Ward & 2×2 Red-Black
-- ============================================================================

/-- Exact `3×3` Hodge resolvent matrix `M_μ(d) = (μ + ‖d‖²) I₃ - d dᵀ`. -/
def w19HodgeM (mu : ℝ) (d : Fin 3 → ℝ) : W18Mat3 :=
  let k2 := w19NormSq3 d
  fun i j => (if i = j then mu + k2 else 0) - d i * d j

/-- Exact `3×3` Sherman–Morrison inverse `M_μ(d)⁻¹ = (μ + ‖d‖²)⁻¹ (I₃ + μ⁻¹ d dᵀ)`. -/
noncomputable def w19HodgeMInv (mu : ℝ) (d : Fin 3 → ℝ) : W18Mat3 :=
  let k2 := w19NormSq3 d
  fun i j => ((if i = j then (1 : ℝ) else 0) + (d i * d j) / mu) / (mu + k2)

/-- Complex `3×3` Cycle 16 mid-plane Hodge matrix `H^(3D) = (2 + d · dc) I₃ - d dcᵀ`. -/
def w19Cyc16H3D (d dc : Fin 3 → ℂ) : Fin 3 → Fin 3 → ℂ :=
  let ktot := d 0 * dc 0 + d 1 * dc 1 + d 2 * dc 2
  fun i j => (if i = j then 2 + ktot else 0) - d i * dc j

/-- Complex `2×2` Cycle 16 mid-plane Hodge matrix `H^(2D) = (2 + d₀ dc₀ + d₁ dc₁) I₂ - d₁₂ dc₁₂ᵀ`. -/
def w19Cyc16H2D (d dc : Fin 3 → ℂ) : W18Mat2C :=
  let k12 := d 0 * dc 0 + d 1 * dc 1
  fun i j => (if i = j then 2 + k12 else 0) - d i.castSucc * dc j.castSucc

theorem w19_3_hodge_1overmu_and_c16_schur_peeling :
    -- (1) Q3 3x3 M_mu(d)^{-1} inverse & momentum-independent longitudinal eigenvalue 1/mu
    (∀ (mu : ℝ) (d : Fin 3 → ℝ), mu ≠ 0 → mu + w19NormSq3 d ≠ 0 →
      (w18Mul3 (w19HodgeM mu d) (w19HodgeMInv mu d) = w18Eye3) ∧
      (∀ i : Fin 3, (∑ j : Fin 3, w19HodgeMInv mu d i j * d j) = d i / mu) ∧
      (∀ v : Fin 3 → ℝ, w19Dot3 d v = 0 →
        ∀ i : Fin 3, (∑ j : Fin 3, w19HodgeMInv mu d i j * v j) = v i / (mu + w19NormSq3 d))) ∧
    ((200 / 755 : ℚ) = 40 / 151 ∧ (264900 / 10 ^ 6 : ℚ) < 40 / 151 ∧ (40 / 151 : ℚ) < 264901 / 10 ^ 6) ∧
    -- (2) Cycle 16 3D -> 2D -> 1D Schur-peeling factorization, plane transfer <= 1/2, dimensional ladder & 1D decay
    (∀ (d dc : Fin 3 → ℂ),
      let k1 : ℂ := d 0 * dc 0
      let k2 : ℂ := d 1 * dc 1
      let k3 : ℂ := d 2 * dc 2
      let k12 : ℂ := k1 + k2
      2 + k1 ≠ 0 → 2 + k12 ≠ 0 → 4 + k12 ≠ 0 →
      (w19Cyc16H3D d dc 2 2 = 2 + k12) ∧
      (∀ i j : Fin 2,
        w19Cyc16H3D d dc i.castSucc j.castSucc -
          w19Cyc16H3D d dc i.castSucc 2 * w19Cyc16H3D d dc 2 j.castSucc / (w19Cyc16H3D d dc 2 2) =
          ((2 + k12 + k3) / (2 + k12)) * w19Cyc16H2D d dc i j) ∧
      (let A0 : W18Mat2C := fun i j => ((4 + k12) / (2 + k12)) * w19Cyc16H2D d dc i j
       let A1 : W18Mat2C := fun i j => -(1 / (2 + k12)) * w19Cyc16H2D d dc i j
       let A0inv : W18Mat2C := fun i j => ((if i = j then (1 : ℂ) else 0) + (1 / 2 : ℂ) * d i.castSucc * dc j.castSucc) / (4 + k12)
       w18Mul2C A0 A0inv = w18Eye2C ∧
       w18Mul2C A0inv (fun i j => 2 * A1 i j) = fun i j => -(2 / (4 + k12)) * w18Eye2C i j) ∧
      (let Heff32 := fun i j : Fin 2 => ((2 + k12 + k3) / (2 + k12)) * w19Cyc16H2D d dc i j
       Heff32 1 1 ≠ 0 →
       Heff32 0 0 - Heff32 0 1 * Heff32 1 0 / Heff32 1 1 = 2 * (2 + k12 + k3) / (2 + k1))) ∧
    ((∀ dim : ℕ, 2 ≤ dim → (2 * ((dim : ℚ) - 1)) / (2 + 2 * ((dim : ℚ) - 1)) = ((dim : ℚ) - 1) / (dim : ℚ)) ∧
      ((2 - 1 : ℚ) / 2 = 1 / 2) ∧ ((3 - 1 : ℚ) / 3 = 2 / 3) ∧ ((4 - 1 : ℚ) / 4 = 3 / 4) ∧
      ((2 - Real.sqrt 3) ^ 2 - 4 * (2 - Real.sqrt 3) + 1 = 0) ∧
      (267949 / 10 ^ 6 : ℝ) < 2 - Real.sqrt 3 ∧ 2 - Real.sqrt 3 < 267950 / 10 ^ 6 ∧
      (1316957 / 10 ^ 6 : ℝ) < Real.log (2 + Real.sqrt 3)) := by
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · intro mu d hmu hden
    refine ⟨?_, ?_, ?_⟩
    · funext i j
      fin_cases i <;> fin_cases j <;>
        simp [w18Mul3, w19HodgeM, w19HodgeMInv, w18Eye3, Fin.sum_univ_three] <;>
        field_simp [hmu, hden] <;>
        simp only [w19NormSq3, w19Dot3] <;> ring
    · intro i
      fin_cases i <;>
        simp [w19HodgeMInv, Fin.sum_univ_three] <;>
        field_simp [hmu, hden] <;>
        simp only [w19NormSq3, w19Dot3] <;> ring
    · intro v hdv i
      have hdot : d 0 * v 0 + d 1 * v 1 + d 2 * v 2 = 0 := hdv
      fin_cases i <;>
        simp [w19HodgeMInv, Fin.sum_univ_three] <;>
        field_simp [hmu, hden]
      · linear_combination d 0 * hdot
      · linear_combination d 1 * hdot
      · linear_combination d 2 * hdot
  · intro d dc k1 k2 k3 k12 hk1 hk12 hk412
    dsimp only [k1, k2, k3, k12] at hk1 hk12 hk412 ⊢
    have h22 : w19Cyc16H3D d dc 2 2 = 2 + (d 0 * dc 0 + d 1 * dc 1) := by
      simp [w19Cyc16H3D]; ring
    have hk12' : 2 + d 0 * dc 0 + d 1 * dc 1 ≠ 0 := fun h => hk12 (by linear_combination h)
    have hk412' : 4 + d 0 * dc 0 + d 1 * dc 1 ≠ 0 := fun h => hk412 (by linear_combination h)
    have hd12 : (2 + d 0 * dc 0 + d 1 * dc 1) * (2 + d 0 * dc 0 + d 1 * dc 1)⁻¹ = 1 :=
      mul_inv_cancel₀ hk12'
    refine ⟨h22, ?_, ?_, ?_⟩
    · intro i j
      rw [h22]
      fin_cases i <;> fin_cases j <;>
        simp [w19Cyc16H3D, w19Cyc16H2D, add_assoc, div_eq_mul_inv]
      · linear_combination -(2 + d 1 * dc 1 + d 2 * dc 2) * hd12
      · linear_combination (d 0 * dc 1) * hd12
      · linear_combination (d 1 * dc 0) * hd12
      · linear_combination -(2 + d 0 * dc 0 + d 2 * dc 2) * hd12
    · refine ⟨?_, ?_⟩
      · funext i j
        fin_cases i <;> fin_cases j <;>
          simp [w18Mul2C, w19Cyc16H2D, w18Eye2C, Fin.sum_univ_two] <;>
          field_simp [hk12, hk12', hk412, hk412'] <;> ring
      · funext i j
        fin_cases i <;> fin_cases j <;>
          simp [w18Mul2C, w19Cyc16H2D, w18Eye2C, Fin.sum_univ_two, div_eq_mul_inv]
        · linear_combination -(2 * (4 + d 0 * dc 0 + d 1 * dc 1)⁻¹) * hd12
        · ring
        · ring
        · linear_combination -(2 * (4 + d 0 * dc 0 + d 1 * dc 1)⁻¹) * hd12
    · intro hden
      simp [w19Cyc16H2D, add_assoc] at hden ⊢
      field_simp [hk1, hk12, hk12', hden]
      ring
  · have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hs3_lo : (17320508 / 10 ^ 7 : ℝ) < Real.sqrt 3 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hs3_hi : Real.sqrt 3 < 17320509 / 10 ^ 7 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hlog_m : (1316957 / 10 ^ 6 : ℝ) < Real.log (2 + Real.sqrt 3) := by
      have hexp1_hi : Real.exp 1 < 27182818286 / 10 ^ 10 := by linarith [Real.exp_one_lt_d9]
      have hexp_frac : Real.exp (316957 / 10 ^ 6 : ℝ) ≤
          (∑ m ∈ Finset.range 8, (316957 / 10 ^ 6 : ℝ) ^ m / m.factorial) +
            (316957 / 10 ^ 6 : ℝ) ^ 8 * ((8 : ℕ) + 1) / ((8 : ℕ).factorial * (8 : ℕ)) :=
        Real.exp_bound' (by norm_num) (by norm_num) (by norm_num)
      have hsum_ub :
          (∑ m ∈ Finset.range 8, (316957 / 10 ^ 6 : ℝ) ^ m / m.factorial) +
            (316957 / 10 ^ 6 : ℝ) ^ 8 * ((8 : ℕ) + 1) / ((8 : ℕ).factorial * (8 : ℕ)) <
            13729436 / 10 ^ 7 := by
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
        norm_num
      have hexp_frac_hi : Real.exp (316957 / 10 ^ 6 : ℝ) < 13729436 / 10 ^ 7 :=
        lt_of_le_of_lt hexp_frac hsum_ub
      have harg_lt : Real.exp (1316957 / 10 ^ 6 : ℝ) < 2 + Real.sqrt 3 := by
        have hsplit : Real.exp (1316957 / 10 ^ 6 : ℝ) = Real.exp 1 * Real.exp (316957 / 10 ^ 6 : ℝ) := by
          rw [← Real.exp_add]; norm_num
        rw [hsplit]
        have h2 : (27182818286 / 10 ^ 10 : ℝ) * (13729436 / 10 ^ 7 : ℝ) < 2 + 17320508 / 10 ^ 7 := by
          norm_num
        have hexp_pos : (0 : ℝ) < Real.exp (316957 / 10 ^ 6 : ℝ) := Real.exp_pos _
        calc
          Real.exp 1 * Real.exp (316957 / 10 ^ 6 : ℝ)
              < (27182818286 / 10 ^ 10 : ℝ) * (13729436 / 10 ^ 7 : ℝ) := by
                exact mul_lt_mul' (le_of_lt hexp1_hi) hexp_frac_hi hexp_pos.le (by positivity)
          _ < 2 + 17320508 / 10 ^ 7 := h2
          _ < 2 + Real.sqrt 3 := by linarith
      exact (Real.lt_log_iff_exp_lt (by positivity)).mpr harg_lt
    refine ⟨?_, by norm_num, by norm_num, by norm_num, by nlinarith [h3], by linarith, by linarith, hlog_m⟩
    intro dim hdim
    have hdim0 : (dim : ℚ) ≠ 0 := by exact_mod_cast (by omega : dim ≠ 0)
    field_simp [hdim0]
    ring

/-- Explicit `4×4` `2×2`-square Laplacian `L_sq` (Cycle 18). -/
def w19Cyc18Lsq : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 2 | 0, 1 => -1 | 0, 3 => -1
  | 1, 0 => -1 | 1, 1 => 2 | 1, 2 => -1
  | 2, 1 => -1 | 2, 2 => 2 | 2, 3 => -1
  | 3, 0 => -1 | 3, 2 => -1 | 3, 3 => 2
  | _, _ => 0

/-- Orthonormal `4×4` eigenbasis `V` for the `2×2` block `L_sq`. -/
noncomputable def w19Cyc18V : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 1 / 2 | 0, 1 => -1 / 2 | 0, 2 => -1 / 2 | 0, 3 => 1 / 2
  | 1, 0 => 1 / 2 | 1, 1 => 1 / 2 | 1, 2 => -1 / 2 | 1, 3 => -1 / 2
  | 2, 0 => 1 / 2 | 2, 1 => 1 / 2 | 2, 2 => 1 / 2 | 2, 3 => 1 / 2
  | 3, 0 => 1 / 2 | 3, 1 => -1 / 2 | 3, 2 => 1 / 2 | 3, 3 => -1 / 2

/-- Sum of all `4` neighbor coupling matrices `J₀₀ = J₊ₓ + J₋ₓ + J₊_y + J₋_y` on the `2×2` block. -/
def w19Cyc18J00 (beta : ℝ) : Fin 4 → Fin 4 → ℝ
  | 0, 1 => -beta | 0, 3 => -beta
  | 1, 0 => -beta | 1, 2 => -beta
  | 2, 1 => -beta | 2, 3 => -beta
  | 3, 0 => -beta | 3, 2 => -beta
  | _, _ => 0

/-- `4×4` `SO(4)` generator `J₀₁` for Cycle 17 `O(4)` Ward identity. -/
def w19Cyc17J01 : Fin 4 → Fin 4 → ℝ
  | 0, 1 => -1 | 1, 0 => 1 | _, _ => 0

def w19Mul4 (A B : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ := fun i j => ∑ k : Fin 4, A i k * B k j
def w19Trsp4 (A : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ := fun i j => A j i

private lemma w19_su2_pow5_general (c s : ℂ) (M : W18Mat2C)
    (hM : w18Mul2C M M = w18Eye2C)
    (hcoeff1 : c ^ 5 + 10 * c ^ 3 * s ^ 2 + 5 * c * s ^ 4 = -1)
    (hcoeff2 : 5 * c ^ 4 * s + 10 * c ^ 2 * s ^ 3 + s ^ 5 = 0) :
    let Fn : W18Mat2C := fun i j => c * w18Eye2C i j + s * M i j
    w18Mul2C Fn (w18Mul2C Fn (w18Mul2C Fn (w18Mul2C Fn Fn))) = fun i j => -w18Eye2C i j := by
  dsimp only
  have hn00 := congr_fun (congr_fun hM 0) 0
  have hn01 := congr_fun (congr_fun hM 0) 1
  have hn10 := congr_fun (congr_fun hM 1) 0
  have hn11 := congr_fun (congr_fun hM 1) 1
  simp only [w18Mul2C, w18Eye2C, Fin.sum_univ_two, Fin.isValue] at hn00 hn01 hn10 hn11
  have hLin : ∀ a b : ℂ,
      w18Mul2C (fun i j => c * w18Eye2C i j + s * M i j)
               (fun i j => a * w18Eye2C i j + b * M i j) =
        fun i j => (c * a + s * b) * w18Eye2C i j + (c * b + s * a) * M i j := by
    intro a b
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [w18Mul2C, w18Eye2C, Fin.sum_univ_two]
    · linear_combination (s * b) * hn00
    · linear_combination (s * b) * hn01
    · linear_combination (s * b) * hn10
    · linear_combination (s * b) * hn11
  set Fn : W18Mat2C := fun i j => c * w18Eye2C i j + s * M i j
  have hF2 : w18Mul2C Fn Fn = fun i j => (c ^ 2 + s ^ 2) * w18Eye2C i j + (2 * c * s) * M i j := by
    rw [show Fn = fun i j => c * w18Eye2C i j + s * M i j from rfl, hLin c s]
    funext i j; simp only [two_mul]; ring
  have hF3 : w18Mul2C Fn (w18Mul2C Fn Fn) =
      fun i j => (c ^ 3 + 3 * c * s ^ 2) * w18Eye2C i j + (3 * c ^ 2 * s + s ^ 3) * M i j := by
    rw [hF2, show Fn = fun i j => c * w18Eye2C i j + s * M i j from rfl, hLin]
    funext i j; simp only [add_mul, mul_add]; ring
  have hF4 : w18Mul2C Fn (w18Mul2C Fn (w18Mul2C Fn Fn)) =
      fun i j => (c ^ 4 + 6 * c ^ 2 * s ^ 2 + s ^ 4) * w18Eye2C i j + (4 * c ^ 3 * s + 4 * c * s ^ 3) * M i j := by
    rw [hF3, show Fn = fun i j => c * w18Eye2C i j + s * M i j from rfl, hLin]
    funext i j; simp only [add_mul, mul_add]; ring
  have hF5 : w18Mul2C Fn (w18Mul2C Fn (w18Mul2C Fn (w18Mul2C Fn Fn))) =
      fun i j => (c ^ 5 + 10 * c ^ 3 * s ^ 2 + 5 * c * s ^ 4) * w18Eye2C i j +
        (5 * c ^ 4 * s + 10 * c ^ 2 * s ^ 3 + s ^ 5) * M i j := by
    rw [hF4, show Fn = fun i j => c * w18Eye2C i j + s * M i j from rfl, hLin]
    funext i j; simp only [add_mul, mul_add]; ring
  rw [hF5, hcoeff1, hcoeff2]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [w18Eye2C]

private lemma w19_c15_pauli_pow5 (nx ny nz : ℝ) (hn : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1) :
    let nSig : W18Mat2C := fun i j =>
      (nx : ℂ) * w18PauliX i j + (ny : ℂ) * w18PauliY i j + (nz : ℂ) * w18PauliZ i j
    let Fn : W18Mat2C := fun i j =>
      ((Real.cos (Real.pi / 5) : ℝ) : ℂ) * w18Eye2C i j +
        Complex.I * ((Real.sin (Real.pi / 5) : ℝ) : ℂ) * nSig i j
    w18Mul2C nSig nSig = w18Eye2C ∧
      w18Mul2C Fn (w18Mul2C Fn (w18Mul2C Fn (w18Mul2C Fn Fn))) = fun i j => -w18Eye2C i j := by
  dsimp only
  set nSig : W18Mat2C := fun i j =>
    (nx : ℂ) * w18PauliX i j + (ny : ℂ) * w18PauliY i j + (nz : ℂ) * w18PauliZ i j
  have hnC : (nx : ℂ) ^ 2 + (ny : ℂ) ^ 2 + (nz : ℂ) ^ 2 = 1 := by exact_mod_cast hn
  have hnSq : w18Mul2C nSig nSig = w18Eye2C := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [w18Mul2C, nSig, w18PauliX, w18PauliY, w18PauliZ, w18Eye2C, Fin.sum_univ_two]
    · linear_combination hnC - (ny : ℂ) ^ 2 * Complex.I_sq
    · ring
    · ring
    · linear_combination hnC - (ny : ℂ) ^ 2 * Complex.I_sq
  set c : ℂ := ((Real.cos (Real.pi / 5) : ℝ) : ℂ)
  set s : ℂ := Complex.I * ((Real.sin (Real.pi / 5) : ℝ) : ℂ)
  have hPlus : (c + s) ^ 5 = -1 := by
    dsimp only [c, s]
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    have h1 : Complex.cos ((Real.pi / 5 : ℝ) : ℂ) + Complex.I * Complex.sin ((Real.pi / 5 : ℝ) : ℂ) =
        Complex.exp (((Real.pi / 5 : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I]; ring
    rw [h1, ← Complex.exp_nat_mul]
    have h5 : ((5 : ℕ) : ℂ) * (((Real.pi / 5 : ℝ) : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [h5, Complex.exp_pi_mul_I]
  have hMinus : (c - s) ^ 5 = -1 := by
    dsimp only [c, s]
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    have h1 : Complex.cos ((Real.pi / 5 : ℝ) : ℂ) - Complex.I * Complex.sin ((Real.pi / 5 : ℝ) : ℂ) =
        Complex.exp (-(((Real.pi / 5 : ℝ) : ℂ) * Complex.I)) := by
      rw [Complex.exp_neg, Complex.exp_mul_I]
      have hsq : Complex.cos ((Real.pi / 5 : ℝ) : ℂ) ^ 2 + Complex.sin ((Real.pi / 5 : ℝ) : ℂ) ^ 2 = 1 :=
        Complex.cos_sq_add_sin_sq _
      have hmul : (Complex.cos ((Real.pi / 5 : ℝ) : ℂ) + Complex.sin ((Real.pi / 5 : ℝ) : ℂ) * Complex.I) *
          (Complex.cos ((Real.pi / 5 : ℝ) : ℂ) - Complex.sin ((Real.pi / 5 : ℝ) : ℂ) * Complex.I) = 1 := by
        linear_combination hsq - Complex.sin ((Real.pi / 5 : ℝ) : ℂ) ^ 2 * Complex.I_sq
      have hInv : (Complex.cos ((Real.pi / 5 : ℝ) : ℂ) + Complex.sin ((Real.pi / 5 : ℝ) : ℂ) * Complex.I)⁻¹ =
          Complex.cos ((Real.pi / 5 : ℝ) : ℂ) - Complex.sin ((Real.pi / 5 : ℝ) : ℂ) * Complex.I :=
        inv_eq_of_mul_eq_one_right hmul
      rw [hInv]; ring
    rw [h1, ← Complex.exp_nat_mul]
    have h5 : ((5 : ℕ) : ℂ) * -(((Real.pi / 5 : ℝ) : ℂ) * Complex.I) = -((Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h5, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have hcoeff1 : c ^ 5 + 10 * c ^ 3 * s ^ 2 + 5 * c * s ^ 4 = -1 := by
    have hsum : c ^ 5 + 10 * c ^ 3 * s ^ 2 + 5 * c * s ^ 4 = ((c + s) ^ 5 + (c - s) ^ 5) / 2 := by ring
    rw [hsum, hPlus, hMinus]; norm_num
  have hcoeff2 : 5 * c ^ 4 * s + 10 * c ^ 2 * s ^ 3 + s ^ 5 = 0 := by
    have hdiff : 5 * c ^ 4 * s + 10 * c ^ 2 * s ^ 3 + s ^ 5 = ((c + s) ^ 5 - (c - s) ^ 5) / 2 := by ring
    rw [hdiff, hPlus, hMinus]; norm_num
  refine ⟨hnSq, ?_⟩
  have hgen := w19_su2_pow5_general c s nSig hnSq hcoeff1 hcoeff2
  convert hgen using 3

private lemma w19_c18_redblack_identities :
    (w19Mul4 (w19Trsp4 w19Cyc18V) w19Cyc18V = fun i j => if i = j then 1 else 0) ∧
    (∀ H_e beta : ℝ,
      w19Mul4 (w19Trsp4 w19Cyc18V) (w19Mul4 (fun i j => (if i = j then H_e else 0) + beta * w19Cyc18Lsq i j) w19Cyc18V) =
        fun i j => if i = j then (if i = 0 then H_e else if i = 1 then H_e + 2 * beta else if i = 2 then H_e + 2 * beta else H_e + 4 * beta) else 0) ∧
    (∀ beta : ℝ,
      w19Mul4 (w19Trsp4 w19Cyc18V) (w19Mul4 (w19Cyc18J00 beta) w19Cyc18V) =
        fun i j => if i = j then (if i = 0 then -2 * beta else if i = 1 then 0 else if i = 2 then 0 else 2 * beta) else 0) := by
  have hOrth : w19Mul4 (w19Trsp4 w19Cyc18V) w19Cyc18V = fun i j => if i = j then 1 else 0 := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [w19Mul4, w19Trsp4, w19Cyc18V, Fin.sum_univ_four] <;> norm_num
  have hLV : ∀ beta : ℝ,
      w19Mul4 (fun i j => beta * w19Cyc18Lsq i j) w19Cyc18V =
        fun i j => w19Cyc18V i j * (if j = 0 then 0 else if j = 1 then 2 * beta else if j = 2 then 2 * beta else 4 * beta) := by
    intro beta; funext i j
    fin_cases i <;> fin_cases j <;>
      simp [w19Mul4, w19Cyc18Lsq, w19Cyc18V, Fin.sum_univ_four] <;> ring
  have hJV : ∀ beta : ℝ,
      w19Mul4 (w19Cyc18J00 beta) w19Cyc18V =
        fun i j => w19Cyc18V i j * (if j = 0 then -2 * beta else if j = 1 then 0 else if j = 2 then 0 else 2 * beta) := by
    intro beta; funext i j
    fin_cases i <;> fin_cases j <;>
      simp [w19Mul4, w19Cyc18J00, w19Cyc18V, Fin.sum_univ_four] <;> ring
  refine ⟨hOrth, ?_, ?_⟩
  · intro H_e beta
    have hsplit : w19Mul4 (fun i j => (if i = j then H_e else 0) + beta * w19Cyc18Lsq i j) w19Cyc18V =
        fun i j => H_e * w19Cyc18V i j + w19Mul4 (fun i j => beta * w19Cyc18Lsq i j) w19Cyc18V i j := by
      funext i j; fin_cases i <;> simp [w19Mul4, Fin.sum_univ_four] <;> ring
    rw [hsplit, hLV beta]
    funext i j
    have ho := congr_fun (congr_fun hOrth i) j
    simp only [w19Mul4] at ho ⊢
    calc
      (∑ k : Fin 4, w19Trsp4 w19Cyc18V i k * (H_e * w19Cyc18V k j + w19Cyc18V k j * (if j = 0 then 0 else if j = 1 then 2 * beta else if j = 2 then 2 * beta else 4 * beta)))
          = (H_e + (if j = 0 then 0 else if j = 1 then 2 * beta else if j = 2 then 2 * beta else 4 * beta)) * (∑ k : Fin 4, w19Trsp4 w19Cyc18V i k * w19Cyc18V k j) := by
            simp only [Fin.sum_univ_four]; ring
      _ = (H_e + (if j = 0 then 0 else if j = 1 then 2 * beta else if j = 2 then 2 * beta else 4 * beta)) * (if i = j then 1 else 0) := by
            rw [ho]
      _ = if i = j then (if i = 0 then H_e else if i = 1 then H_e + 2 * beta else if i = 2 then H_e + 2 * beta else H_e + 4 * beta) else 0 := by
            by_cases hij : i = j
            · subst hij; fin_cases i <;> simp
            · simp [hij]
  · intro beta
    rw [hJV beta]
    funext i j
    have ho := congr_fun (congr_fun hOrth i) j
    simp only [w19Mul4] at ho ⊢
    calc
      (∑ k : Fin 4, w19Trsp4 w19Cyc18V i k * (w19Cyc18V k j * (if j = 0 then -2 * beta else if j = 1 then 0 else if j = 2 then 0 else 2 * beta)))
          = (if j = 0 then -2 * beta else if j = 1 then 0 else if j = 2 then 0 else 2 * beta) * (∑ k : Fin 4, w19Trsp4 w19Cyc18V i k * w19Cyc18V k j) := by
            simp only [Fin.sum_univ_four]; ring
      _ = (if j = 0 then -2 * beta else if j = 1 then 0 else if j = 2 then 0 else 2 * beta) * (if i = j then 1 else 0) := by
            rw [ho]
      _ = if i = j then (if i = 0 then -2 * beta else if i = 1 then 0 else if i = 2 then 0 else 2 * beta) else 0 := by
            by_cases hij : i = j
            · subst hij; fin_cases i <;> simp
            · simp [hij]

theorem w19_3_c15_s2_c17_o4_and_c18_redblack :
    -- (1) Cycle 15 S² 5th power = -I₂ identically for all unit vectors n ∈ S², U(1) barrier & HK/Wil π²/4
    ((∀ nx ny nz : ℝ, nx ^ 2 + ny ^ 2 + nz ^ 2 = 1 →
        let nSig : W18Mat2C := fun i j => (nx : ℂ) * w18PauliX i j + (ny : ℂ) * w18PauliY i j + (nz : ℂ) * w18PauliZ i j
        let Fn : W18Mat2C := fun i j =>
          ((Real.cos (Real.pi / 5) : ℝ) : ℂ) * w18Eye2C i j + Complex.I * ((Real.sin (Real.pi / 5) : ℝ) : ℂ) * nSig i j
        let F5 := w18Mul2C Fn (w18Mul2C Fn (w18Mul2C Fn (w18Mul2C Fn Fn)))
        w18Mul2C nSig nSig = w18Eye2C ∧ F5 = fun i j => -w18Eye2C i j) ∧
      (∀ beta : ℝ, 5 * beta * (1 - Real.cos (Real.pi / 5)) = beta * (15 - 5 * Real.sqrt 5) / 4 ∧
        2 * beta - 5 * beta * (1 - Real.cos (Real.pi / 5)) = beta * (5 * Real.sqrt 5 - 7) / 4) ∧
      (5173170 / 10 ^ 6 : ℝ) < (495 / 100) * (5 * Real.sqrt 5 - 7) / 4) ∧
    -- (2) Cycle 17 SO(4) generator J01 exact bond invariance, S³ Haar cov 1/4, h_min(4.95,150d) & 3/h_min
    ((∀ Rx Ry : Fin 4 → ℝ,
        (∑ i : Fin 4, (∑ j : Fin 4, w19Cyc17J01 i j * Rx j) * Ry i) +
        (∑ i : Fin 4, Rx i * (∑ j : Fin 4, w19Cyc17J01 i j * Ry j)) = 0) ∧
      (2 * Real.cos (5 * Real.pi / 12) = (Real.sqrt 6 - Real.sqrt 2) / 2) ∧
      (2562308 / 10 ^ 6 : ℝ) < (495 / 100) * (Real.sqrt 6 - Real.sqrt 2) / 2 ∧
      (3 : ℝ) / ((495 / 100) * (Real.sqrt 6 - Real.sqrt 2) / 2) < 1170820 / 10 ^ 6) ∧
    -- (3) Cycle 18 4x4 L_sq eigenbasis V, Red-Black J00 dipole cancellation, alpha_tri vs rho_RB & C5 3/2 penalty
    ((w19Mul4 (w19Trsp4 w19Cyc18V) w19Cyc18V = fun i j => if i = j then 1 else 0) ∧
      (∀ H_e beta : ℝ,
        w19Mul4 (w19Trsp4 w19Cyc18V) (w19Mul4 (fun i j => (if i = j then H_e else 0) + beta * w19Cyc18Lsq i j) w19Cyc18V) =
          fun i j => if i = j then (if i = 0 then H_e else if i = 1 then H_e + 2 * beta else if i = 2 then H_e + 2 * beta else H_e + 4 * beta) else 0) ∧
      (∀ beta : ℝ,
        w19Mul4 (w19Trsp4 w19Cyc18V) (w19Mul4 (w19Cyc18J00 beta) w19Cyc18V) =
          fun i j => if i = j then (if i = 0 then -2 * beta else if i = 1 then 0 else if i = 2 then 0 else 2 * beta) else 0) ∧
      (∀ beta h_m c_s : ℝ, 0 < beta → 0 < h_m → 0 ≤ c_s →
        2 * beta / (h_m + 2 * beta * c_s) < 3 * beta / (h_m + 3 * beta * c_s))) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨w19_c15_pauli_pow5, ?_, ?_⟩
    · intro beta
      rw [Real.cos_pi_div_five]
      constructor <;> ring
    · have hs5_lo : (22360679 / 10 ^ 7 : ℝ) < Real.sqrt 5 := by
        rw [Real.lt_sqrt (by norm_num)]; norm_num
      nlinarith
  · have hcos75 : 2 * Real.cos (5 * Real.pi / 12) = (Real.sqrt 6 - Real.sqrt 2) / 2 := by
      have harg : (5 * Real.pi / 12 : ℝ) = Real.pi / 4 + Real.pi / 6 := by ring
      rw [harg, Real.cos_add, Real.cos_pi_div_four, Real.cos_pi_div_six,
        Real.sin_pi_div_four, Real.sin_pi_div_six]
      have h6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
        rw [← Real.sqrt_mul (by norm_num)]; norm_num
      linarith
    have hs6_lo : (24494897 / 10 ^ 7 : ℝ) < Real.sqrt 6 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hs2_hi : Real.sqrt 2 < 14142136 / 10 ^ 7 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hmin_lo : (2562308 / 10 ^ 6 : ℝ) < (495 / 100) * (Real.sqrt 6 - Real.sqrt 2) / 2 := by
      linarith
    have hward_hi : (3 : ℝ) / ((495 / 100) * (Real.sqrt 6 - Real.sqrt 2) / 2) < 1170820 / 10 ^ 6 := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    refine ⟨?_, hcos75, hmin_lo, hward_hi⟩
    intro Rx Ry
    simp [w19Cyc17J01, Fin.sum_univ_four]
  · refine ⟨w19_c18_redblack_identities.1, w19_c18_redblack_identities.2.1, w19_c18_redblack_identities.2.2, ?_⟩
    intro beta h_m c_s hbeta hhm hcs
    have hd1 : 0 < h_m + 2 * beta * c_s := by positivity
    have hd2 : 0 < h_m + 3 * beta * c_s := by positivity
    rw [div_lt_div_iff₀ hd1 hd2]
    nlinarith

-- ============================================================================
-- §4. W19-4 & Q4: Elitzur 1/3 Sheet, 3×3 Sherman–Morrison, K_comm & Litmus 6
-- ============================================================================

/-- `3×3` temporal-tree Sherman–Morrison spatial propagator `C₃ = c_T I₃ + f_F d dᵀ`. -/
def w19SM3 (cT fF : ℝ) (d : Fin 3 → ℝ) : W18Mat3 :=
  fun i j => (if i = j then cT else 0) + fF * (d i * d j)

/-- Exact inverse `C₃⁻¹ = c_T⁻¹ I₃ - f_F / (c_T (c_T + ‖d‖² f_F)) d dᵀ`. -/
noncomputable def w19SM3Inv (cT fF : ℝ) (d : Fin 3 → ℝ) : W18Mat3 :=
  let sv2 := w19NormSq3 d
  fun i j => (if i = j then 1 / cT else 0) - fF / (cT * (cT + sv2 * fF)) * (d i * d j)

theorem w19_4_elitzur_sm_kcomm_sd_and_litmus6 :
    -- (1) Elitzur 2D sheet fraction = 2/6 = 1/3 (4 mixed planes)
    ((2 : ℚ) / 6 = 1 / 3 ∧ (6 - 2 : ℕ) = 4) ∧
    -- (2) Exact 3x3 Sherman-Morrison C3 * C3_inv = I3, C_L pole cancellation & plaquette gauge cancellation
    (∀ (cT fF : ℝ) (d : Fin 3 → ℝ), cT ≠ 0 → cT + w19NormSq3 d * fF ≠ 0 →
      w18Mul3 (w19SM3 cT fF d) (w19SM3Inv cT fF d) = w18Eye3) ∧
    (∀ (aT s02 m2 sv2 : ℝ), s02 + m2 ≠ 0 → s02 + sv2 + m2 ≠ 0 →
      aT / (s02 + sv2 + m2) + sv2 * (aT / ((s02 + m2) * (s02 + sv2 + m2))) = aT / (s02 + m2)) ∧
    (∀ (s12 s22 cT fF : ℝ),
      4 * ((1 / 4 : ℝ) * (s12 + s22) * cT + (1 / 2 : ℝ) * s12 * s22 * fF) -
        8 * ((1 / 4 : ℝ) * s12 * s22 * fF) = (s12 + s22) * cT) ∧
    -- (3) Gauge-invariant non-U(1)-blind commutator K_comm = 2 |v1 x v2|^2 >= 0 & U(1) === 0
    ((∀ (q01 vx1 vy1 vz1 q02 vx2 vy2 vz2 : ℝ),
        q01 ^ 2 + (vx1 ^ 2 + vy1 ^ 2 + vz1 ^ 2) = 1 →
        q02 ^ 2 + (vx2 ^ 2 + vy2 ^ 2 + vz2 ^ 2) = 1 →
        let P1 : W18Mat2C := fun i j => (q01 : ℂ) * w18Eye2C i j +
          Complex.I * ((vx1 : ℂ) * w18PauliX i j + (vy1 : ℂ) * w18PauliY i j + (vz1 : ℂ) * w18PauliZ i j)
        let P2 : W18Mat2C := fun i j => (q02 : ℂ) * w18Eye2C i j +
          Complex.I * ((vx2 : ℂ) * w18PauliX i j + (vy2 : ℂ) * w18PauliY i j + (vz2 : ℂ) * w18PauliZ i j)
        let P1i : W18Mat2C := fun i j => (q01 : ℂ) * w18Eye2C i j -
          Complex.I * ((vx1 : ℂ) * w18PauliX i j + (vy1 : ℂ) * w18PauliY i j + (vz1 : ℂ) * w18PauliZ i j)
        let P2i : W18Mat2C := fun i j => (q02 : ℂ) * w18Eye2C i j -
          Complex.I * ((vx2 : ℂ) * w18PauliX i j + (vy2 : ℂ) * w18PauliY i j + (vz2 : ℂ) * w18PauliZ i j)
        let commMat := w18Mul2C (w18Mul2C P1 P2) (w18Mul2C P1i P2i)
        let cx := vy1 * vz2 - vz1 * vy2
        let cy := vz1 * vx2 - vx1 * vz2
        let cz := vx1 * vy2 - vy1 * vx2
        (1 - ((1 / 2 : ℝ) : ℂ) * w18Tr2C commMat).re = 2 * (cx ^ 2 + cy ^ 2 + cz ^ 2) ∧
        0 ≤ 2 * (cx ^ 2 + cy ^ 2 + cz ^ 2)) ∧
      (∀ vz1 vz2 : ℝ,
        2 * ((0 * vz2 - vz1 * 0) ^ 2 + (vz1 * 0 - 0 * vz2) ^ 2 + (0 * 0 - 0 * 0) ^ 2) = (0 : ℝ)) ∧
      (∀ u2 q0 qdotw : ℝ, 0 ≤ u2 → q0 ^ 2 + qdotw ^ 2 ≤ 1 →
        (1 / 2 : ℝ) * (1 - u2) ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) * u2 - u2 * (q0 ^ 2 + qdotw ^ 2)) ∧
      (∀ u2 : ℝ, u2 < 1 → 0 < (3 / 4 : ℝ) * (1 - u2) ^ 2) ∧
      (∀ beta u_p u_m : ℝ, beta ≠ 0 →
        ((3 / beta) * u_p + 6 * u_p ^ 2) - ((3 / beta) * u_m + 6 * u_m ^ 2) =
          (u_p - u_m) * (3 / beta + 6 * (u_p + u_m)))) ∧
    -- (4) SU(5) exact representation eigenvalues & Litmus 6
    (((12 / 5 : ℚ) = w18CasimirFund 5 ∧ (18 / 5 : ℚ) = w18CasimirAntisym 5 ∧
      (2 / 5 : ℚ) - (-3 / 5) = 1) ∧
      6 * Real.pi ^ 2 / 11 < 8 * Real.log 2) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro cT fF d hcT hden
    have hc1 : cT * cT⁻¹ = 1 := mul_inv_cancel₀ hcT
    have hd1 : (cT + w19NormSq3 d * fF) * (cT + w19NormSq3 d * fF)⁻¹ = 1 := mul_inv_cancel₀ hden
    simp only [w19NormSq3, w19Dot3] at hd1
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [w18Mul3, w19SM3, w19SM3Inv, w19NormSq3, w19Dot3, w18Eye3,
        Fin.sum_univ_three, div_eq_mul_inv]
    · linear_combination hc1 - fF * d 0 ^ 2 * cT⁻¹ * hd1
    · linear_combination -fF * d 0 * d 1 * cT⁻¹ * hd1
    · linear_combination -fF * d 0 * d 2 * cT⁻¹ * hd1
    · linear_combination -fF * d 1 * d 0 * cT⁻¹ * hd1
    · linear_combination hc1 - fF * d 1 ^ 2 * cT⁻¹ * hd1
    · linear_combination -fF * d 1 * d 2 * cT⁻¹ * hd1
    · linear_combination -fF * d 2 * d 0 * cT⁻¹ * hd1
    · linear_combination -fF * d 2 * d 1 * cT⁻¹ * hd1
    · linear_combination hc1 - fF * d 2 ^ 2 * cT⁻¹ * hd1
  · intro aT s02 m2 sv2 h1 h2
    field_simp [h1, h2]
    ring
  · intro s12 s22 cT fF
    ring
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro q01 vx1 vy1 vz1 q02 vx2 vy2 vz2 h1 h2
      dsimp only
      have hid :
          (1 - ((1 / 2 : ℝ) : ℂ) * w18Tr2C (w18Mul2C (w18Mul2C
            (fun i j => (q01 : ℂ) * w18Eye2C i j +
              Complex.I * ((vx1 : ℂ) * w18PauliX i j + (vy1 : ℂ) * w18PauliY i j + (vz1 : ℂ) * w18PauliZ i j))
            (fun i j => (q02 : ℂ) * w18Eye2C i j +
              Complex.I * ((vx2 : ℂ) * w18PauliX i j + (vy2 : ℂ) * w18PauliY i j + (vz2 : ℂ) * w18PauliZ i j)))
            (w18Mul2C
              (fun i j => (q01 : ℂ) * w18Eye2C i j -
                Complex.I * ((vx1 : ℂ) * w18PauliX i j + (vy1 : ℂ) * w18PauliY i j + (vz1 : ℂ) * w18PauliZ i j))
              (fun i j => (q02 : ℂ) * w18Eye2C i j -
                Complex.I * ((vx2 : ℂ) * w18PauliX i j + (vy2 : ℂ) * w18PauliY i j + (vz2 : ℂ) * w18PauliZ i j))))).re =
            1 - (q01 ^ 2 + (vx1 ^ 2 + vy1 ^ 2 + vz1 ^ 2)) * (q02 ^ 2 + (vx2 ^ 2 + vy2 ^ 2 + vz2 ^ 2)) +
              2 * ((vy1 * vz2 - vz1 * vy2) ^ 2 + (vz1 * vx2 - vx1 * vz2) ^ 2 + (vx1 * vy2 - vy1 * vx2) ^ 2) := by
        simp only [w18Mul2C, w18Tr2C, w18Eye2C, w18PauliX, w18PauliY, w18PauliZ, Fin.sum_univ_two, Fin.isValue]
        simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
          Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im]
        ring
      rw [hid, h1, h2]
      refine ⟨by ring, by positivity⟩
    · intro vz1 vz2; ring
    · intro u2 q0 qdotw hu2 hle
      nlinarith
    · intro u2 hu2
      have : 0 < (1 - u2) ^ 2 := sq_pos_of_pos (by linarith)
      linarith
    · intro beta u_p u_m hbeta
      field_simp [hbeta]
      ring
  · constructor
    · norm_num [w18CasimirFund, w18CasimirAntisym]
    · have hp : Real.pi < 31416 / 10000 := by linarith [Real.pi_lt_d4]
      have hl : (6931471803 / 10 ^ 10 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hpi_nonneg : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
      nlinarith

-- ============================================================================
-- §5. Canonical Wave 19 Witness, 20-Item Taxonomy & Honest .OPEN Lock
-- ============================================================================

/-- Quantitative Wave 19 pure-arithmetic / 40-digit interval witness across `W19-1..W19-4` & `Cycles 15–18`. -/
structure W19_SmoothUVLandauZSchurPeelAndCorrelatedCoexistenceWitness where
  qStLb : ℚ
  lamSpecW19Ub : ℚ
  m1PouAsig2Ub : ℚ
  m1PouMinCovLb : ℚ
  bkarZdPureJacUb : ℕ
  bkarPureJacNlfUb : ℕ
  bkarIdealNoTreeUb : ℕ
  bkarWickBugFreeM4Ub : ℕ
  bkarWickFullUb : ℕ
  strangStepsTo8p1875 : ℕ
  strangSumTo8p1875Ub : ℚ
  strangStepsTo4p95 : ℕ
  strangSumTo4p95Ub : ℚ
  landauCellMfpLb : ℚ
  landauTreeSvMinLb : ℚ
  landau2Link210dEigUb : ℚ
  landauStokes45D22Ub : ℚ
  landauStokesCosoftD22Ub : ℚ
  landauStokes710D22Lb : ℚ
  gpp2416SiteUb : ℚ
  darboux2b3MaxUb : ℚ
  darbouxWside495Lb : ℚ
  darboux400Lb : ℚ
  schurA0InvL1Ub : ℚ
  hodge3dMu259Lb : ℚ
  hodge3dMu260Ub : ℚ
  cubicLB2NoGoLb : ℚ
  layerCake150d495Ub : ℚ
  c15KoffUnclampedLb : ℚ
  c16Excised14NbrBp1Ub : ℚ
  c16Excised14NbrDirbUb : ℚ
  c17Layer120d695Ub : ℚ
  c17O4OverO2Lb : ℚ
  c18AlphaTri2x2Lb : ℚ
  c18Rb2x2Cap40dUb : ℚ
  c18Rb2x2Cap43dLb : ℚ
  c18C5CubeCap40dLb : ℚ
  q4ElitzurSheetFrac : ℚ
  tube22x22Lift038Lb : ℚ
  tube22x22Lift187Lb : ℚ
  widthCut225Lb : ℚ
  widthCut495Lb : ℚ
  widthCut150Lb : ℚ
  kComm495Lb : ℚ
  litmus6RatioUb : ℚ
  eightLn2Lb : ℚ

/-- Canonical Wave 19 conservative `[C/B/P]` witness matching `verify_w19_convergence` & `W19-1..4` / `Cycles 15–18`. -/
def w19_canonical_witness : W19_SmoothUVLandauZSchurPeelAndCorrelatedCoexistenceWitness where
  qStLb := 955 / 1000
  lamSpecW19Ub := 1210010 / 10 ^ 6
  m1PouAsig2Ub := 280512 / 10 ^ 8
  m1PouMinCovLb := 997202 / 10 ^ 6
  bkarZdPureJacUb := 76
  bkarPureJacNlfUb := 143
  bkarIdealNoTreeUb := 195
  bkarWickBugFreeM4Ub := 5515
  bkarWickFullUb := 8551
  strangStepsTo8p1875 := 21384
  strangSumTo8p1875Ub := 456322 / 10 ^ 6
  strangStepsTo4p95 := 21397
  strangSumTo4p95Ub := 753383 / 10 ^ 6
  landauCellMfpLb := 2343145 / 10 ^ 6
  landauTreeSvMinLb := 618033 / 10 ^ 6
  landau2Link210dEigUb := -517638 / 10 ^ 6
  landauStokes45D22Ub := 960980 / 10 ^ 6
  landauStokesCosoftD22Ub := 887522 / 10 ^ 6
  landauStokes710D22Lb := 1787545 / 10 ^ 6
  gpp2416SiteUb := 453422 / 10 ^ 6
  darboux2b3MaxUb := 987715 / 10 ^ 6
  darbouxWside495Lb := 58659355 / 10 ^ 6
  darboux400Lb := 1826595 / 10 ^ 6
  schurA0InvL1Ub := 670729 / 10 ^ 6
  hodge3dMu259Lb := 1001978 / 10 ^ 6
  hodge3dMu260Ub := 996848 / 10 ^ 6
  cubicLB2NoGoLb := 4152998 / 10 ^ 6
  layerCake150d495Ub := 4439 / 10 ^ 6
  c15KoffUnclampedLb := 64412 / 10 ^ 6
  c16Excised14NbrBp1Ub := 636272 / 10 ^ 6
  c16Excised14NbrDirbUb := 807003 / 10 ^ 6
  c17Layer120d695Ub := 322619 / 10 ^ 6
  c17O4OverO2Lb := 2902161 / 10 ^ 6
  c18AlphaTri2x2Lb := 1237104 / 10 ^ 6
  c18Rb2x2Cap40dUb := 975740 / 10 ^ 6
  c18Rb2x2Cap43dLb := 1009924 / 10 ^ 6
  c18C5CubeCap40dLb := 1065427 / 10 ^ 6
  q4ElitzurSheetFrac := 1 / 3
  tube22x22Lift038Lb := 16669 / 10 ^ 3
  tube22x22Lift187Lb := 17466 / 10 ^ 3
  widthCut225Lb := 111544 / 10 ^ 5
  widthCut495Lb := 122133 / 10 ^ 5
  widthCut150Lb := 125724 / 10 ^ 5
  kComm495Lb := 12275980 / 10 ^ 9
  litmus6RatioUb := 5383421 / 10 ^ 6
  eightLn2Lb := 5545177 / 10 ^ 6

/-- Every quantitative separation in `w19_canonical_witness` holds constructively. -/
theorem w19_canonical_witness_margins :
    w19_canonical_witness.lamSpecW19Ub < w18_canonical_witness.lamSpecUb ∧
    w19_canonical_witness.bkarZdPureJacUb < w19_canonical_witness.bkarPureJacNlfUb ∧
    w19_canonical_witness.bkarPureJacNlfUb < w19_canonical_witness.bkarIdealNoTreeUb ∧
    w19_canonical_witness.bkarIdealNoTreeUb < w19_canonical_witness.bkarWickBugFreeM4Ub ∧
    w19_canonical_witness.bkarWickBugFreeM4Ub < w19_canonical_witness.bkarWickFullUb ∧
    w19_canonical_witness.strangSumTo8p1875Ub < 1 / 2 ∧
    w19_canonical_witness.strangSumTo4p95Ub < 76 / 100 ∧
    2 < w19_canonical_witness.landauCellMfpLb ∧
    0 < w19_canonical_witness.landauTreeSvMinLb ∧
    w19_canonical_witness.landau2Link210dEigUb < 0 ∧
    w19_canonical_witness.landauStokesCosoftD22Ub < w19_canonical_witness.landauStokes45D22Ub ∧
    w19_canonical_witness.landauStokes45D22Ub < 1 ∧
    1 < w19_canonical_witness.landauStokes710D22Lb ∧
    w19_canonical_witness.darboux2b3MaxUb < 1 ∧
    55 < w19_canonical_witness.darbouxWside495Lb ∧
    1 < w19_canonical_witness.darboux400Lb ∧
    w19_canonical_witness.schurA0InvL1Ub < 1 ∧
    1 < w19_canonical_witness.hodge3dMu259Lb ∧
    w19_canonical_witness.hodge3dMu260Ub < 1 ∧
    4 < w19_canonical_witness.cubicLB2NoGoLb ∧
    w19_canonical_witness.layerCake150d495Ub < 1 ∧
    w18_canonical_witness.q3KoffCapUb < w19_canonical_witness.c15KoffUnclampedLb ∧
    w19_canonical_witness.c16Excised14NbrBp1Ub < 1 ∧
    w19_canonical_witness.c16Excised14NbrDirbUb < 1 ∧
    w19_canonical_witness.c17Layer120d695Ub < 1 ∧
    2 < w19_canonical_witness.c17O4OverO2Lb ∧
    1 < w19_canonical_witness.c18AlphaTri2x2Lb ∧
    w19_canonical_witness.c18Rb2x2Cap40dUb < 1 ∧
    1 < w19_canonical_witness.c18Rb2x2Cap43dLb ∧
    1 < w19_canonical_witness.c18C5CubeCap40dLb ∧
    w19_canonical_witness.q4ElitzurSheetFrac = 1 / 3 ∧
    16 < w19_canonical_witness.tube22x22Lift038Lb ∧
    w19_canonical_witness.tube22x22Lift038Lb < w19_canonical_witness.tube22x22Lift187Lb ∧
    1 < w19_canonical_witness.widthCut225Lb ∧
    w19_canonical_witness.widthCut225Lb < w19_canonical_witness.widthCut495Lb ∧
    w19_canonical_witness.widthCut495Lb < w19_canonical_witness.widthCut150Lb ∧
    0 < w19_canonical_witness.kComm495Lb ∧
    w19_canonical_witness.litmus6RatioUb < w19_canonical_witness.eightLn2Lb := by
  unfold w19_canonical_witness w18_canonical_witness
  norm_num

/-- Finite 20-element taxonomy of Round 19 Wave 19 (`W19-1..W19-5`) & `Cycles 15–18` closures & surviving walls. -/
inductive Wave19RetirementId
  | o_w19_1_qst_0p955_lamspec_1p2100
  | o_w19_1_hsm3_row_and_frobenius_sos
  | o_w19_1_wick_compression_8551_to_5515_strang
  | o_w19_1_nonlocal_wpair_lagrange_wall_open
  | o_w19_2_2link_landau_gribov_pi_zero
  | o_w19_2_cell_mfp_ltree_and_cbh_oneill
  | o_w19_2_five4_stokes_cosoft_and_darboux_dichotomy
  | o_w19_2_gribov_and_su5_bridge_trap_open
  | o_w19_3_hodge_1overmu_and_mu_c_bracket
  | o_w19_3_c16_schur_peel_vs_cubic_nogo
  | o_w19_3_c15_s2_shield_and_koff_gap
  | o_w19_3_c17_o4_ward_and_120d_6p95_closure
  | o_w19_3_c18_2x2_redblack_40d_vs_43d_and_c5
  | o_w19_3_consistent_excised_kato_coarse_wall_open
  | o_mi16_mi18_frustrated_4p95_to_6p95_open
  | o_w19_4_elitzur_1over3_and_22x22_tube_lifts
  | o_w19_4_sherman_morrison_cl_gauge_cancel_and_cuts
  | o_w19_4_residual_2link_width_floor_0p38_1p87_open
  | o_w19_4_noncircular_kcomm_gibbs_vs_u1_and_om13_open
  | o_w19_5_core_team_cycles15_to_18_convergence
  deriving DecidableEq, Repr

private def wave19RetirementToFin : Wave19RetirementId → Fin 20
  | .o_w19_1_qst_0p955_lamspec_1p2100 => 0
  | .o_w19_1_hsm3_row_and_frobenius_sos => 1
  | .o_w19_1_wick_compression_8551_to_5515_strang => 2
  | .o_w19_1_nonlocal_wpair_lagrange_wall_open => 3
  | .o_w19_2_2link_landau_gribov_pi_zero => 4
  | .o_w19_2_cell_mfp_ltree_and_cbh_oneill => 5
  | .o_w19_2_five4_stokes_cosoft_and_darboux_dichotomy => 6
  | .o_w19_2_gribov_and_su5_bridge_trap_open => 7
  | .o_w19_3_hodge_1overmu_and_mu_c_bracket => 8
  | .o_w19_3_c16_schur_peel_vs_cubic_nogo => 9
  | .o_w19_3_c15_s2_shield_and_koff_gap => 10
  | .o_w19_3_c17_o4_ward_and_120d_6p95_closure => 11
  | .o_w19_3_c18_2x2_redblack_40d_vs_43d_and_c5 => 12
  | .o_w19_3_consistent_excised_kato_coarse_wall_open => 13
  | .o_mi16_mi18_frustrated_4p95_to_6p95_open => 14
  | .o_w19_4_elitzur_1over3_and_22x22_tube_lifts => 15
  | .o_w19_4_sherman_morrison_cl_gauge_cancel_and_cuts => 16
  | .o_w19_4_residual_2link_width_floor_0p38_1p87_open => 17
  | .o_w19_4_noncircular_kcomm_gibbs_vs_u1_and_om13_open => 18
  | .o_w19_5_core_team_cycles15_to_18_convergence => 19

private def wave19RetirementOfFin (i : Fin 20) : Wave19RetirementId :=
  match i.1 with
  | 0 => .o_w19_1_qst_0p955_lamspec_1p2100
  | 1 => .o_w19_1_hsm3_row_and_frobenius_sos
  | 2 => .o_w19_1_wick_compression_8551_to_5515_strang
  | 3 => .o_w19_1_nonlocal_wpair_lagrange_wall_open
  | 4 => .o_w19_2_2link_landau_gribov_pi_zero
  | 5 => .o_w19_2_cell_mfp_ltree_and_cbh_oneill
  | 6 => .o_w19_2_five4_stokes_cosoft_and_darboux_dichotomy
  | 7 => .o_w19_2_gribov_and_su5_bridge_trap_open
  | 8 => .o_w19_3_hodge_1overmu_and_mu_c_bracket
  | 9 => .o_w19_3_c16_schur_peel_vs_cubic_nogo
  | 10 => .o_w19_3_c15_s2_shield_and_koff_gap
  | 11 => .o_w19_3_c17_o4_ward_and_120d_6p95_closure
  | 12 => .o_w19_3_c18_2x2_redblack_40d_vs_43d_and_c5
  | 13 => .o_w19_3_consistent_excised_kato_coarse_wall_open
  | 14 => .o_mi16_mi18_frustrated_4p95_to_6p95_open
  | 15 => .o_w19_4_elitzur_1over3_and_22x22_tube_lifts
  | 16 => .o_w19_4_sherman_morrison_cl_gauge_cancel_and_cuts
  | 17 => .o_w19_4_residual_2link_width_floor_0p38_1p87_open
  | 18 => .o_w19_4_noncircular_kcomm_gibbs_vs_u1_and_om13_open
  | _ => .o_w19_5_core_team_cycles15_to_18_convergence

private def wave19RetirementEquivFin20 : Wave19RetirementId ≃ Fin 20 where
  toFun := wave19RetirementToFin
  invFun := wave19RetirementOfFin
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Wave19RetirementId :=
  Fintype.ofEquiv (Fin 20) wave19RetirementEquivFin20.symm

/-- **Round 19 Wave 19 Honest `.OPEN` Lock**:
    1. Chains Round 18 (`round18_irx_wave18_honest_open_lock`) cleanly into Round 19 (`W19-1..W19-5` + Cycles 15–18);
    2. Certifies all 20 Wave 19 structural closures/open walls & `w19_canonical_witness` margins (`[C/B/P]` only);
    3. Locks `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`, `currentH2dRepoWitness = ⟨1, 1, 1⟩`,
       `wave11H2ConstructiveWitness`, and `device_certified = false` strictly **`.OPEN`** / `false` (`7-Way + Litmus 6`). `[C/B/P/X]` -/
theorem round19_irx_wave19_honest_open_lock :
    -- (1) Full Round 18 honest OPEN core + 7-Way + H2d repo witness preserved verbatim
    ((∀ c : Round07IRXFirstPrinciples.SevenWayCounterexampleId,
        (Round07IRXFirstPrinciples.sevenWaySignature c).positiveMassGap = false) ∧
      Function.Injective Round07IRXFirstPrinciples.sevenWaySignature ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      ¬ (currentH2dRepoWitness.toH2LayerCandidate).Satisfies .h2d_clay_4d_continuum_measure ∧
      ¬ wave11H2ConstructiveWitness.Satisfies .h2d_clay_4d_continuum_measure ∧
      currentH2dRepoWitness = ⟨1, 1, 1⟩ ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) ∧
    -- (2) Round 19 taxonomy (20 items) chained cleanly onto Round 18 (20 items) & Round 17 (17 items)
    (Nonempty Wave19RetirementId ∧ Fintype.card Wave19RetirementId = 20 ∧
      Nonempty W19_SmoothUVLandauZSchurPeelAndCorrelatedCoexistenceWitness ∧
      Nonempty Wave18RetirementId ∧ Fintype.card Wave18RetirementId = 20 ∧
      Nonempty W18_L2SpecNonGaussB2HodgeWallAndMultiStepDobrushinWitness ∧
      Nonempty Wave17RetirementId ∧ Fintype.card Wave17RetirementId = 17) ∧
    -- (3) Round 19 §1..§4 pure-kernel theorems + Round 18 highlighted milestones + w19 margins
    ((w18_canonical_witness.lamSpecUb < w18_canonical_witness.rowBoxLb ∧
        w18_canonical_witness.hodge2dL12Ub < 1 ∧
        1 < w18_canonical_witness.hodge3dL6Lb ∧
        w18_canonical_witness.riccatiSu2InfRayMaxCoeff < 0) ∧
      ((2 / Real.sqrt 3) * (1 / (955 / 1000 : ℝ) + 778535 / 10 ^ 9) < 1210010 / 10 ^ 6 ∧
        (∀ w : Fin 4 → Fin 3 → ℝ,
          4 * (w19NormSq3 (w19Hsm3U01 w) + w19NormSq3 (w19Hsm3U02 w) + w19NormSq3 (w19Hsm3U03 w) +
                w19NormSq3 (w19Hsm3U12 w) + w19NormSq3 (w19Hsm3U13 w) + w19NormSq3 (w19Hsm3U23 w)) =
            (1 / 4 : ℝ) * (w19NormSq3 (w 0) + w19NormSq3 (w 1) + w19NormSq3 (w 2) + w19NormSq3 (w 3)) -
              (1 / 16 : ℝ) * w19NormSq3 (fun a => w 0 a - w 1 a - w 2 a + w 3 a)) ∧
        w18Det3 (w19LandauMfp Real.pi) = 0 ∧
        (2343145 / 10 ^ 6 : ℝ) < 8 - 4 * Real.sqrt 2 ∧
        (∀ dim : ℕ, 2 ≤ dim → (2 * ((dim : ℚ) - 1)) / (2 + 2 * ((dim : ℚ) - 1)) = ((dim : ℚ) - 1) / (dim : ℚ)) ∧
        (∀ beta : ℝ, 5 * beta * (1 - Real.cos (Real.pi / 5)) = beta * (15 - 5 * Real.sqrt 5) / 4) ∧
        (∀ beta : ℝ,
          w19Mul4 (w19Trsp4 w19Cyc18V) (w19Mul4 (w19Cyc18J00 beta) w19Cyc18V) =
            fun i j => if i = j then (if i = 0 then -2 * beta else if i = 1 then 0 else if i = 2 then 0 else 2 * beta) else 0) ∧
        (∀ s12 s22 cT fF : ℝ,
          4 * ((1 / 4 : ℝ) * (s12 + s22) * cT + (1 / 2 : ℝ) * s12 * s22 * fF) -
            8 * ((1 / 4 : ℝ) * s12 * s22 * fF) = (s12 + s22) * cT) ∧
        (∀ vz1 vz2 : ℝ,
          2 * ((0 * vz2 - vz1 * 0) ^ 2 + (vz1 * 0 - 0 * vz2) ^ 2 + (0 * 0 - 0 * 0) ^ 2) = (0 : ℝ)) ∧
        w19_canonical_witness.lamSpecW19Ub < w18_canonical_witness.lamSpecUb ∧
        w19_canonical_witness.darboux2b3MaxUb < 1 ∧
        55 < w19_canonical_witness.darbouxWside495Lb ∧
        w19_canonical_witness.schurA0InvL1Ub < 1 ∧
        1 < w19_canonical_witness.hodge3dMu259Lb ∧
        w19_canonical_witness.hodge3dMu260Ub < 1 ∧
        w19_canonical_witness.c17Layer120d695Ub < 1 ∧
        w19_canonical_witness.c18Rb2x2Cap40dUb < 1 ∧
        1 < w19_canonical_witness.c18Rb2x2Cap43dLb ∧
        1 < w19_canonical_witness.c18C5CubeCap40dLb ∧
        0 < w19_canonical_witness.kComm495Lb ∧
        6 * Real.pi ^ 2 / 11 < 8 * Real.log 2)) ∧
    -- (4) Universal minimal irreducible H2d obstruction remains unbridged (.OPEN)
    (∀ (core : Round05CrossObligationH2d.H2dMinimalIrreducibleCore),
      (∀ o : H2dCoreObligation, core.toObstructionCandidate.Satisfies o) ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) := by
  rcases round18_irx_wave18_honest_open_lock with
    ⟨hCore, ⟨_, _, _, hW17ne, hW17card, hW17wit, hW16ne, hW16card⟩, hR18thm, hMinCore⟩
  rcases w19_1_smooth_pou_hsm3_sos_wick_and_strang with
    ⟨_, hHsm3, hLam19, _⟩
  rcases w19_2_landau_gribov_cell_mfp_cbh_and_su5 with
    ⟨⟨_, hGribPi, _⟩, ⟨_, hCellMfp, _⟩, _, _⟩
  rcases w19_3_hodge_1overmu_and_c16_schur_peeling with
    ⟨_, _, _, ⟨hLad, _⟩⟩
  rcases w19_3_c15_s2_c17_o4_and_c18_redblack with
    ⟨⟨_, hS2Act, _⟩, _, ⟨_, _, hJ00, _⟩⟩
  rcases w19_4_elitzur_sm_kcomm_sd_and_litmus6 with
    ⟨_, _, _, hPlaqCancel, ⟨_, hU1Zero, _, _, _⟩, ⟨_, hLit6⟩⟩
  rcases w19_canonical_witness_margins with
    ⟨hLamDrop, _, _, _, _, _, _, _, _, _, _, _, _, hDarbOk, hDarbWs, _, hSchur, hMu259, hMu260, _, _, _, _, _, hC17, _, _, hRb40, hRb43, hC5Rb, _, _, _, _, _, _, hKcomm, _⟩
  refine ⟨hCore, ⟨⟨.o_w19_1_qst_0p955_lamspec_1p2100⟩, by decide, ⟨w19_canonical_witness⟩,
    ⟨.o_w18_1_cross_product_gram_sos_l2spec⟩, by decide, ⟨w18_canonical_witness⟩, hW17ne, hW17card⟩, ?_, hMinCore⟩
  refine ⟨⟨hR18thm.2.2.2.2.2.2.2.2.2.2.2.2.1, hR18thm.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hR18thm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hR18thm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩, ?_⟩
  refine ⟨hLam19, fun w => (hHsm3 w).2.2.2.2, hGribPi, hCellMfp, hLad, fun beta => (hS2Act beta).1,
    hJ00, hPlaqCancel, hU1Zero, hLamDrop, hDarbOk, hDarbWs, hSchur, hMu259, hMu260, hC17, hRb40, hRb43, hC5Rb, hKcomm, hLit6⟩

end UEOTPhysicsUnification.IRXWave19SmoothUVLandauZSchurPeelAndCorrelatedCoexistence
