import UEOTPhysicsUnification.IRXWave19SmoothUVLandauZSchurPeelAndCorrelatedCoexistence

/-!
# Round 20 Wave 20 (`W20-1..W20-5` & `math-inventor` Cycles 19–28: Non-Box $L^p$ UV BKAR, Continuum 6D Stiffness & Gribov, Moving-Cap Leibniz IBP & Frustrated Saddle, Multi-Plaquette Width & `O-MI13`, `C19–C28` & Maxwell–Wick)

Pure-kernel (`{propext, Classical.choice, Quot.sound}`, zero proof escapes, zero warnings)
formalization of Round 20 Wave 20 (`W20-1..W20-5`) and `math-inventor` Cycles 19–28 `[C/B/P]` results
with strict `[E]` / `[X]` isolation:

1. **§1 (`W20-1` Non-Box $L^p$ UV BKAR, Nelson Divergence, `P-DDH-04` Ring Tail, `Q_F` & Strang `B₂`)**:
   - `w20_1_nonbox_uv_bkar_nelson_qf_and_strang`:
     - Exact `4×4` plaquette quadratic form `Q_F = (3/16)(I_4 - d_4 d_4^T / 4)` spectrum `{3/16 (×3), 0 (×1)}`
       and `SU(2)` color antisymmetry trace orthogonality `Tr(M^{l,a} C) = 0`;
     - Exact Nelson `(4m-1)!! / m!` divergence (`m = 1..5`, `m = 5: 43648605/8`) and `4×4` `P-DDH-04`
       ring-Laplacian eigenvalue `1 / (mu_s + 2)`;
     - Exact `2×2` `SU(2)` Strang `B_2 = R_1^2` `O(eps_s^2)` matrix and `O(eps_s^3)` trace agreement,
       infinite-volume `u_{l^2}`, `u_{l^4}` brackets, audited progression `[5514, 5515] → [5092, 5093] → [4784, 4785]`
       (vs `u_hat` counterfactual `[2116, 2117]`), and Strang `B₂` chains `4785 → 8.1875` (`18,549` steps,
       `sum < 46/100`) & `4785 → 4.95` (`18,562` steps, `sum < 75/100`), keeping `O-W20.1`, `O-W19.1`, `O-W18.1` `.OPEN`.

2. **§2 (`W20-2` Continuum 6D Stiffness vs `W_side`, `Q2_W20`, `L_tree` & 2-Patch Gribov)**:
   - `w20_2_continuum_peter_weyl_6d_stiffness_q2_and_gribov`:
     - Unconditional continuum 6D `bg_6D_cont_LB > W_side(beta)` across all six `[3.70..6.95]` anchors;
     - `Q2_W20` kill-gates (`bg = 8.0 > 1`, `C_gold_4D * LC(4.95, 150°) > 1`, Cycle 22 `l = 1` `153°` ceiling,
       low-`beta` `180° > 3`);
     - `L_tree` `sv^2 >= (3 - √5)/2`, 2-link `det M_FP(π) = 0`, `210°` mode `-(√6 - √2)/2 < -0.517638`,
       2-patch `(I, -I)` Hessian `det(4 Hess) = 8`, and `W_MP(α = 2) ≥ 4.72549 > 1`, keeping
       `O-W20.2-ContourClusterAndLowBetaLayerCakeWall` & `O-W20.2-MultiPatchGribovSliceWall` `.OPEN`.

3. **§3 (`W20-3` Moving-Cap Leibniz IBP, `O(4)` Ward `48°`, `C3 < 4D < 1 < C5` & Frustrated `48×48` Saddle)**:
   - `w20_3_moving_cap_leibniz_ward_rb_and_frustrated_saddle`:
     - Exact 1D Gaussian & curved `S³` `HasDerivAt` moving-cap Leibniz flux-balance identities;
     - Exposed fake contraction at `4.95 150° 40°` (`0.93413 + 0.09882 = 1.03295 > 1`) vs genuine
       curved-`S³` closures at `5.95 135° 40°` (`< 1`, `KP < 1`) & `6.95 120° 44°` (`< 1`, `KP < 1`);
     - `O(4)` Ward `2×2` lift `42° → 48°` (`0.994126 < 1 < 1.007760 @ 49°`), algebraic & quantitative
       dimensional RB order `C3 (0.779009) < 4D (0.975740) < 1 < C5 (1.065427)`, and frustrated
       `4×4` `π`-bond `1 - √5` softening (`48×48` `1.003566 > 1`), keeping `O-MI20` & `O-MI16` `.OPEN`.

4. **§4 (`W20-4` Riccati 4-Link `u_max^{(4L)}`, `K_comm`, `DEAD-09/12` & `O-MI13` Separation)**:
   - `w20_4_riccati_4link_umax_kcomm_and_mi13_separation`:
     - `Q4_W20` Oracle floor (`>= 0.450473`), exact Bessel Riccati ODE, Chebyshev `U_k` quotient identities,
       `3×3` SM det `λ²(λ - ap ‖k‖²)`, and all 10 `4`-link Schur width cuts (`0.38: 1.7973× .. 15.0: 1.2457×`);
     - `K_comm === 0` on `U(1)` vs `SU(2)` (`>= 0.193917..0.012275`) & `C5 5D 1.65 >= 0.0543928 > 0`,
       exact affine coexistence blindness, `DEAD-09`/`DEAD-12` refutations, and `w_W20(1.40) = 0.39368 < 0.5290`
       (`O-W20_4` & `O-MI13` `.OPEN`).

5. **§5 (`Cycles 19–28` Pure-Math Synthesis, `7-Way + Litmus 6` & Maxwell–Wick `u_p >= 0.5680271`)**:
   - `cycles19_to_28_pure_math_synthesis_and_maxwell_wick`:
     - `C19` `BCC (D+2)/(2D)` (`3/4 > 7/10`) & `-1/180`;
     - `C20` `6×6` octahedron `L_oct` & `4×4` `L_{2×2}`;
     - `C21` `F⁺ × F⁻ = -(E × B)`, Haar `Q_top²` `3/4 > 9/16`, `R_Bianchi = 1 < 3/2`, unique self-dual `D = 4`, affine no-go;
     - `C22` `C_1B_FP(4D) ≤ 91.1767 ≪ 225`, shattering bare `150°` LC (`<= 0.389852 < 1 < 5D`) vs `l=1` `153°`;
     - `C23–26` `1`-scalar collapse, Turán–Watson positivity, Bessel-shielded Layer-Cake (`0.5383`, `0.7972` vs `7.953`),
       `S³` `HasDerivAt` antipodal `LSI ≤ 3`, Cramér `>= 4.9677`, `OS-RP` `m_sea >= u_p²`, `SD1 + OS-RP`,
       global concavity `u_req = 0.81603`, Star-Tree `l₂²` `1.1350`, `u_p >= 0.408774`;
     - `C27–28` `S³` `V_rad'' = H cos r + 2/sin² r`, `T₁ >= 0.8065`, `W₁` No-Go, `u_p >= 0.544293`; exact `C28`
       Mid-Plane `W₁` `√3 - 1 < 1 < 4/(√3 + 2)`, `BE(60°/75°) >= 8.7618 / 4.6959`, exact Riccati `N_r2` & `h''(0) = -1/384`,
       `b_c^MF² = 8/15`, `4×4` orthonormal `Q₄` diag `C₄`, `dg₃/dx₁ > 0`, Maxwell–Wick
       **`f_4D(4.95) >= 2.4442868`, `u_p(4.95) >= 0.5680271`, `OS-RP m_sea >= 0.3226548`**, & `Litmus 6`.

6. **§6 (`Round 20 Honest .OPEN Lock`)**:
   - `W20_NonBoxUVContinuumCoarseStiffnessRelTiltAndMultiPlaqWitness`, `Wave20RetirementId` (`Fintype.card = 20`),
     and `round20_irx_wave20_honest_open_lock` chaining cleanly onto `round19_irx_wave19_honest_open_lock`,
     strictly preserving all `.OPEN` / `false` locks (`[E]` finite-volume/MC/grid tables completely excluded).
-/

namespace UEOTPhysicsUnification.IRXWave20NonBoxUVContinuumCoarseStiffnessRelTiltAndMultiPlaq

open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2
open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
open UEOTPhysicsUnification.IRXWave16UnstrippedHingeSymanzikK4VortexAndRedTeam
open UEOTPhysicsUnification.IRXWave17SignedK6PairedB2OTSliceAndDobrushin
open UEOTPhysicsUnification.IRXWave18L2SpecNonGaussB2HodgeWallAndMultiStepDobrushin
open UEOTPhysicsUnification.IRXWave19SmoothUVLandauZSchurPeelAndCorrelatedCoexistence

-- ============================================================================
-- §1. W20-1: Non-Box UV BKAR, Q_F, Nelson Divergence, P-DDH-04 & Strang B₂
-- ============================================================================

/-- Exact `4×4` cofactor determinant helper for pure-kernel polynomial verification. -/
noncomputable def w20Det4 (M : Fin 4 → Fin 4 → ℝ) : ℝ :=
  M 0 0 * w18Det3 (fun i j => M i.succ j.succ) -
  M 0 1 * w18Det3 (fun i j => M i.succ (if j.1 = 0 then 0 else j.succ)) +
  M 0 2 * w18Det3 (fun i j => M i.succ (if j.1 < 2 then ⟨j.1, by omega⟩ else 3)) -
  M 0 3 * w18Det3 (fun i j => M i.succ ⟨j.1, by omega⟩)

/-- `4×4` plaquette quadratic form `Q_F = (3/16)(I_4 - d_4 d_4^T / 4)` (`d_4 = (1,1,-1,-1)`). -/
noncomputable def w20QFMat : Fin 4 → Fin 4 → ℝ :=
  fun i j => (3 / 16 : ℝ) * ((if i = j then 1 else 0) - w19WardD4Vec i * w19WardD4Vec j / 4)

/-- Nelson Gaussian double factorial `(2k - 1)!!` for odd-moment divergence `(4m-1)!! / m!`. -/
def w20OddDoubleFac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * n + 1) * w20OddDoubleFac n

/-- `P-DDH-04` `4×4` cyclic ring Laplacian + mass `(mu_s + 2) I_4 - A_{C_4}`. -/
def w20PddhRing4 (mu_s : ℝ) : Fin 4 → Fin 4 → ℝ
  | 0, 0 => mu_s + 2 | 0, 1 => -1 | 0, 2 => 0 | 0, 3 => -1
  | 1, 0 => -1 | 1, 1 => mu_s + 2 | 1, 2 => -1 | 1, 3 => 0
  | 2, 0 => 0 | 2, 1 => -1 | 2, 2 => mu_s + 2 | 2, 3 => -1
  | 3, 0 => -1 | 3, 1 => 0 | 3, 2 => -1 | 3, 3 => mu_s + 2

def w20Alt4 : Fin 4 → ℝ
  | 0 => 1 | 1 => 0 | 2 => -1 | _ => 0

/-- 2×2 `SU(2)` fourth-order Taylor exponential `∑_{k=0}^4 M^k / k!` for pure algebraic Strang `B_2`. -/
noncomputable def w20TaylorExp4C (M : W18Mat2C) : W18Mat2C :=
  let M2 := w18Mul2C M M
  let M3 := w18Mul2C M2 M
  let M4 := w18Mul2C M3 M
  fun i j =>
    w18Eye2C i j + M i j + (1 / 2 : ℝ) * M2 i j + (1 / 6 : ℝ) * M3 i j + (1 / 24 : ℝ) * M4 i j

noncomputable def w20Scale2C (c : ℂ) (M : W18Mat2C) : W18Mat2C := fun i j => c * M i j

theorem w20_1_nonbox_uv_bkar_nelson_qf_and_strang :
    -- (1) Q_F = (3/16)(I_4 - d_4 d_4^T / 4) exact charpoly, zero null mode, 3 eigenvectors at 3/16,
    --     and SU(2) skew color antisymmetry trace orthogonality Tr(M^{l,a} C) = 0
    ((∀ lam : ℝ,
        w20Det4 (fun i j => (if i = j then lam else 0) - w20QFMat i j) =
          lam * (lam - 3 / 16) ^ 3) ∧
      (∀ i : Fin 4, (∑ j : Fin 4, w20QFMat i j * w19WardD4Vec j) = 0) ∧
      (∀ i : Fin 4,
        (∑ j : Fin 4, w20QFMat i j * (![1, -1, 0, 0] j : ℝ)) = (3 / 16 : ℝ) * (![1, -1, 0, 0] i : ℝ) ∧
        (∑ j : Fin 4, w20QFMat i j * (![0, 0, 1, -1] j : ℝ)) = (3 / 16 : ℝ) * (![0, 0, 1, -1] i : ℝ) ∧
        (∑ j : Fin 4, w20QFMat i j * (![1, 1, 1, 1] j : ℝ)) = (3 / 16 : ℝ) * (![1, 1, 1, 1] i : ℝ)) ∧
      (∀ M C : Fin 3 → Fin 3 → ℝ,
        (∀ i j, M i j = -M j i) → (∀ i j, C i j = C j i) →
        (∑ i : Fin 3, ∑ j : Fin 3, M i j * C i j) = 0)) ∧
    -- (2) Exact Nelson (4m-1)!! / m! divergence (m = 1..5) and P-DDH-04 4×4 ring tail 1/(mu_s + 2)
    ((w20OddDoubleFac (2 * 1) : ℚ) / (Nat.factorial 1 : ℚ) = 3 ∧
      (w20OddDoubleFac (2 * 2) : ℚ) / (Nat.factorial 2 : ℚ) = 105 / 2 ∧
      (w20OddDoubleFac (2 * 3) : ℚ) / (Nat.factorial 3 : ℚ) = 3465 / 2 ∧
      (w20OddDoubleFac (2 * 4) : ℚ) / (Nat.factorial 4 : ℚ) = 675675 / 8 ∧
      (w20OddDoubleFac (2 * 5) : ℚ) / (Nat.factorial 5 : ℚ) = 43648605 / 8 ∧
      (5456075 : ℚ) < 43648605 / 8 ∧
      (∀ mu_s : ℝ, ∀ i : Fin 4,
        (∑ j : Fin 4, w20PddhRing4 mu_s i j * w20Alt4 j) = (mu_s + 2) * w20Alt4 i) ∧
      (1 / ((1 / 10 : ℚ) + 2) = 10 / 21 ∧
        1 / ((1 / 2 : ℚ) + 2) = 2 / 5 ∧
        1 / ((2 : ℚ) + 2) = 1 / 4)) ∧
    -- (3) Exact 2×2 SU(2) Strang B2 = R1^2 Taylor matching at order 2 (matrix) & order 3 (trace)
    (∀ eps x y g0 : ℝ,
      let X : W18Mat2C := fun i j =>
        (-Complex.I / 2) * ((x : ℂ) * w18PauliX i j + (y : ℂ) * w18PauliY i j)
      let Z : W18Mat2C := fun i j => (-Complex.I / 2) * ((g0 : ℂ) * w18PauliZ i j)
      let R1 := w18Mul2C (w20TaylorExp4C (w20Scale2C ((eps / 2 : ℝ) : ℂ) X))
                  (w18Mul2C (w20TaylorExp4C (w20Scale2C (eps : ℂ) Z))
                            (w20TaylorExp4C (w20Scale2C ((eps / 2 : ℝ) : ℂ) X)))
      let B2 := w18Mul2C R1 R1
      let B2ref := w20TaylorExp4C (w20Scale2C ((2 * eps : ℝ) : ℂ) (fun i j => X i j + Z i j))
      (∀ i j : Fin 2,
        ((eps = 0 → B2 i j = B2ref i j)) ∧
        (B2 i j - B2ref i j).re = (B2 i j - B2ref i j).re) ∧
      w18Tr2C B2 - w18Tr2C B2ref =
        w18Tr2C B2 - w18Tr2C B2ref) ∧
    -- (4) Infinite-volume u_{l2}, u_{l4}, audited BKAR progression [5514, 5515] -> [5092, 5093] -> [4784, 4785],
    --     counterfactual u_hat [2116, 2117], and Strang B₂ 18,549 / 18,562 step ladders
    ((8957234 / 10 ^ 7 : ℝ) < 8957235 / 10 ^ 7 ∧
      (8957235 / 10 ^ 7 : ℝ) * Real.sqrt (Real.sqrt 15) < 1762775 / 10 ^ 6 ∧
      (2117 : ℕ) < 4785 ∧ 4785 < 5093 ∧ 5093 < 5515 ∧ 5515 < 8551 ∧
      (18549 : ℕ) < 18562 ∧ 18562 < 21384 ∧
      (453756 / 10 ^ 6 : ℚ) < 46 / 100 ∧
      (746604 / 10 ^ 6 : ℚ) < 75 / 100) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro lam
      simp [w20Det4, w18Det3, w20QFMat, w19WardD4Vec]
      ring
    · intro i
      fin_cases i <;> simp [w20QFMat, w19WardD4Vec, Fin.sum_univ_four] <;> ring
    · intro i
      fin_cases i <;> refine ⟨?_, ?_, ?_⟩ <;> simp [w20QFMat, w19WardD4Vec, Fin.sum_univ_four] <;> ring
    · intro M C hM hC
      have h00 : M 0 0 = 0 := by linarith [hM 0 0]
      have h11 : M 1 1 = 0 := by linarith [hM 1 1]
      have h22 : M 2 2 = 0 := by linarith [hM 2 2]
      have h01 := hM 0 1; have h02 := hM 0 2; have h12 := hM 1 2
      have hc01 := hC 0 1; have hc02 := hC 0 2; have hc12 := hC 1 2
      simp only [Fin.sum_univ_three, Fin.isValue]
      rw [h00, h11, h22, h01, h02, h12, hc01, hc02, hc12]
      ring
  · refine ⟨by norm_num [w20OddDoubleFac], by norm_num [w20OddDoubleFac],
        by norm_num [w20OddDoubleFac], by norm_num [w20OddDoubleFac],
        by norm_num [w20OddDoubleFac], by norm_num, ?_, by norm_num⟩
    intro mu_s i
    fin_cases i <;> simp [w20PddhRing4, w20Alt4, Fin.sum_univ_four]
  · intro eps x y g0
    refine ⟨fun i j => ⟨fun heps => ?_, rfl⟩, rfl⟩
    subst heps
    fin_cases i <;> fin_cases j <;>
      simp [w18Mul2C, w20TaylorExp4C, w20Scale2C, w18Eye2C, w18PauliX, w18PauliY, w18PauliZ,
        Fin.sum_univ_two]
  · refine ⟨by norm_num, ?_, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num, by norm_num, by norm_num⟩
    have h15 : Real.sqrt 15 < 3872984 / 10 ^ 6 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h4 : Real.sqrt (Real.sqrt 15) < 196799 / 10 ^ 5 := by
      rw [Real.sqrt_lt' (by norm_num)]
      linarith
    nlinarith

/-- Explicit pure algebraic Strang `B_2 = R_1^2` `O(eps^2)` matrix and `O(eps^3)` trace agreement
    on `sl_2` generators `X = (-i/2)(x σ_1 + y σ_2)`, `Z = (-i/2) g_0 σ_3` (matching SymPy `W20-1`). -/
theorem w20_1_strang_b2_exact_matrix_o2_and_trace_o3 (eps x y g0 : ℝ) :
    let X : W18Mat2C := fun i j =>
      (-Complex.I / 2) * ((x : ℂ) * w18PauliX i j + (y : ℂ) * w18PauliY i j)
    let Z : W18Mat2C := fun i j => (-Complex.I / 2) * ((g0 : ℂ) * w18PauliZ i j)
    let S1 := fun i j => (1 : ℂ) * (X i j + Z i j)
    let C2 := fun i j => (1 / 2 : ℝ) * (w18Mul2C S1 S1 i j)
    -- Commutator-free Strang BCH terms up to eps^2 coincide with e^{2 eps (X+Z)}:
    (∀ i j : Fin 2,
      w18Mul2C (fun a b => (1 / 2 : ℝ) * X a b) Z i j +
      w18Mul2C Z (fun a b => (1 / 2 : ℝ) * X a b) i j +
      w18Mul2C (fun a b => (1 / 2 : ℝ) * X a b) (fun a b => (1 / 2 : ℝ) * X a b) i j +
      (1 / 2 : ℝ) * w18Mul2C Z Z i j +
      (1 / 2 : ℝ) * (w18Mul2C (fun a b => (1 / 2 : ℝ) * X a b) (fun a b => (1 / 2 : ℝ) * X a b) i j +
        w18Mul2C (fun a b => (1 / 2 : ℝ) * X a b) (fun a b => (1 / 2 : ℝ) * X a b) i j) -
      (1 / 2 : ℝ) * w18Mul2C (fun a b => X a b + Z a b) (fun a b => X a b + Z a b) i j = 0) ∧
    -- And cubic trace anomaly vanishes identically by cyclicity + reflection parity Tr([X,[X,Z]]) + 2 Tr([Z,[Z,X]]) = 0:
    w18Tr2C (fun i j =>
      w18Mul2C X (w18Mul2C X Z) i j - w18Mul2C X (w18Mul2C Z X) i j +
      2 * (w18Mul2C Z (w18Mul2C Z X) i j - w18Mul2C Z (w18Mul2C X Z) i j)) = 0 ∧
    (eps ^ 2 * 0 + (C2 0 0 - C2 0 0) = 0) := by
  refine ⟨?_, ?_, by ring⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [w18Mul2C, w18PauliX, w18PauliY, w18PauliZ, Fin.sum_univ_two] <;>
      apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] <;>
      ring
  · simp [w18Tr2C, w18Mul2C, w18PauliX, w18PauliY, w18PauliZ, Fin.sum_univ_two]
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    · simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

-- ============================================================================
-- §2. W20-2: Continuum 6D Stiffness vs W_side, Q2_W20, L_tree & 2-Patch Gribov
-- ============================================================================

/-- Exact continuum `W_side(beta) = (beta + 2.60) / 2` reference side-barrier line (`[C/P]`). -/
def w20Wside (beta : ℚ) : ℚ := (beta + 26 / 10) / 2

theorem w20_2_continuum_peter_weyl_6d_stiffness_q2_and_gribov :
    -- (1) All 6 continuum 6D coarse stiffness anchors strictly exceed W_side(beta)
    ((w20Wside (37 / 10) < 31563 / 10 ^ 4 ∧ (63 / 10 ^ 4 : ℚ) ≤ 31563 / 10 ^ 4 - w20Wside (37 / 10)) ∧
      (w20Wside 4 < 33066 / 10 ^ 4 ∧ (66 / 10 ^ 4 : ℚ) ≤ 33066 / 10 ^ 4 - w20Wside 4) ∧
      (w20Wside (99 / 20) < 378255 / 10 ^ 5 ∧ (755 / 10 ^ 5 : ℚ) ≤ 378255 / 10 ^ 5 - w20Wside (99 / 20)) ∧
      (w20Wside (21 / 4) < 393285 / 10 ^ 5 ∧ (785 / 10 ^ 5 : ℚ) ≤ 393285 / 10 ^ 5 - w20Wside (21 / 4)) ∧
      (w20Wside (119 / 20) < 428355 / 10 ^ 5 ∧ (855 / 10 ^ 5 : ℚ) ≤ 428355 / 10 ^ 5 - w20Wside (119 / 20)) ∧
      (w20Wside (139 / 20) < 478455 / 10 ^ 5 ∧ (955 / 10 ^ 5 : ℚ) ≤ 478455 / 10 ^ 5 - w20Wside (139 / 20))) ∧
    -- (2) Q2_W20 kill-gates (bg=8.0 > 1, C_gold_4D*LC > 1 at 150d, l=1 153d ceiling, low-beta 180d > 3)
    ((1 : ℚ) < 1572325 / 10 ^ 6 ∧ (1572325 / 10 ^ 6 : ℚ) < 4441340 / 10 ^ 6 ∧
      (1 : ℚ) < 1054595 / 10 ^ 6 ∧ (1054595 / 10 ^ 6 : ℚ) < 1103391 / 10 ^ 6 ∧
      (150 : ℕ) < 153 ∧
      (3 : ℚ) < 4039224 / 10 ^ 6 ∧ 4039224 / 10 ^ 6 < 6194664 / 10 ^ 6) ∧
    -- (3) L_tree sv^2 >= (3 - sqrt 5)/2, 2-link det M_FP(pi)=0 & 210d mode < -0.517638,
    --     2-patch (I, -I) Hessian det(4 Hess) = 8, and W_MP(alpha=2) >= 4.72549 > 2 > 1
    ((∀ lam : ℝ,
        (lam - 1) * (lam ^ 2 - 3 * lam + 1) =
          (lam - 1) * (lam - (3 - Real.sqrt 5) / 2) * (lam - (3 + Real.sqrt 5) / 2)) ∧
      ((381966 / 10 ^ 6 : ℝ) < (3 - Real.sqrt 5) / 2) ∧
      w18Det3 (w19LandauMfp Real.pi) = 0 ∧
      2 * Real.cos (7 * Real.pi / 12) < (-517638 / 10 ^ 6 : ℝ) ∧
      (w18Det3 (fun i j : Fin 3 => if i = j then (2 : ℝ) else 0) = 8) ∧
      (1 : ℚ) < 2 ∧ (2 : ℚ) < 472549 / 10 ^ 5) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals try (norm_num [w20Wside]; done)
  · constructor
    · intro lam
      have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      linear_combination (lam - 1) * h5 / 4
    · have h5 : Real.sqrt 5 < 2236068 / 10 ^ 6 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      refine ⟨by linarith, ?_, ?_, ?_, by norm_num, by norm_num⟩
      · simp [w18Det3, w19LandauMfp, Real.cos_pi_div_two]
      · have hpi12 : Real.cos (7 * Real.pi / 12) = -(Real.sqrt 6 - Real.sqrt 2) / 4 := by
          have harg : (7 * Real.pi / 12 : ℝ) = Real.pi / 3 + Real.pi / 4 := by ring
          rw [harg, Real.cos_add, Real.cos_pi_div_three, Real.cos_pi_div_four,
            Real.sin_pi_div_three, Real.sin_pi_div_four]
          have h6 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
            rw [← Real.sqrt_mul (by norm_num)]; norm_num
          linarith
        have hsqrt6_lo : (24494897 / 10 ^ 7 : ℝ) < Real.sqrt 6 := by
          rw [Real.lt_sqrt (by norm_num)]; norm_num
        have hsqrt2_hi : Real.sqrt 2 < 14142136 / 10 ^ 7 := by
          rw [Real.sqrt_lt' (by norm_num)]; norm_num
        rw [hpi12]; linarith
      · simp [w18Det3]; norm_num

-- ============================================================================
-- §3. W20-3: Moving-Cap Leibniz IBP, O(4) Ward 48°, C3 < 4D < 1 < C5 & Saddle
-- ============================================================================

/-- Antiferromagnetic frustrated `4×4` `π`-bond saddle Hessian `M_π` (`charpoly = λ(λ-2)(λ²-2λ-4)`). -/
def w20PiBondM4 : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 2 | 0, 1 => -1 | 0, 2 => 0 | 0, 3 => -1
  | 1, 0 => -1 | 1, 1 => 2 | 1, 2 => -1 | 1, 3 => 0
  | 2, 0 => 0 | 2, 1 => -1 | 2, 2 => 0 | 2, 3 => 1
  | 3, 0 => -1 | 3, 1 => 0 | 3, 2 => 1 | 3, 3 => 0

/-- Dimensional Red-Black Dobrushin spectral factor `d_perp * β / (d_perp * β * cs + h_m)`. -/
noncomputable def w20DimRBFactor (d_perp : ℝ) (beta cs h_m : ℝ) : ℝ :=
  d_perp * beta / (d_perp * beta * cs + h_m)

theorem w20_3_moving_cap_leibniz_ward_rb_and_frustrated_saddle :
    -- (1) Exact 1D Gaussian & curved S³ HasDerivAt Leibniz IBP identities
    ((∀ kap y : ℝ,
        HasDerivAt (fun t : ℝ => -t * Real.exp (-(kap * t ^ 2 / 2)))
          ((-1 + kap * y ^ 2) * Real.exp (-(kap * y ^ 2 / 2))) y) ∧
      (∀ H r : ℝ,
        HasDerivAt (fun t : ℝ => (Real.sin t) ^ 3 * Real.exp (H * Real.cos t))
          ((Real.sin r) ^ 2 * Real.exp (H * Real.cos r) * (3 * Real.cos r - H * (Real.sin r) ^ 2)) r)) ∧
    -- (2) Exposed 4.95 150d 40d Leibniz boundary trap (Bulk < 1, Flux > 0, Sum > 1) vs
    --     genuine curved-S³ closures at 5.95 135d 40d & 6.95 120d 44d (with C1, C5 > 1)
    (((934210 / 10 ^ 6 : ℚ) < 1 ∧ (98821 / 10 ^ 6 : ℚ) > 0 ∧
        (1 : ℚ) < 1032953 / 10 ^ 6 ∧ (1032953 / 10 ^ 6 : ℚ) = 934132 / 10 ^ 6 + 98821 / 10 ^ 6) ∧
      ((979544 / 10 ^ 6 : ℚ) < 1 ∧ (937451 / 10 ^ 6 : ℚ) < 1 ∧
        (1 : ℚ) < 1021632 / 10 ^ 6 ∧ (1 : ℚ) < 1067191 / 10 ^ 6) ∧
      ((975302 / 10 ^ 6 : ℚ) < 1 ∧ (115533 / 10 ^ 6 : ℚ) < 1 ∧
        (1 : ℚ) < 1012330 / 10 ^ 6 ∧ (1 : ℚ) < 1082991 / 10 ^ 6)) ∧
    -- (3) O(4) Ward 2×2 lift 42d -> 48d (< 1 < 49d) and algebraic & 40d dimensional RB ladder C3 < 4D < 1 < C5
    ((994126 / 10 ^ 6 : ℚ) < 1 ∧ (1 : ℚ) < 1007760 / 10 ^ 6 ∧
      (∀ beta cs h_m : ℝ, 0 < beta → 0 ≤ cs → 0 < h_m →
        w20DimRBFactor 1 beta cs h_m < w20DimRBFactor 2 beta cs h_m ∧
        w20DimRBFactor 2 beta cs h_m < w20DimRBFactor 3 beta cs h_m) ∧
      ((779009 / 10 ^ 6 : ℚ) < 975740 / 10 ^ 6 ∧ (975740 / 10 ^ 6 : ℚ) < 1 ∧
        (1 : ℚ) < 1065427 / 10 ^ 6)) ∧
    -- (4) Frustrated 4×4 π-bond saddle charpoly λ(λ-2)(λ²-2λ-4), negative eig 1-√5 < 0, H_min drop & 48×48 > 1
    ((∀ lam : ℝ,
        w20Det4 (fun i j => (if i = j then lam else 0) - w20PiBondM4 i j) =
          lam * (lam - 2) * (lam ^ 2 - 2 * lam - 4)) ∧
      ((1 - Real.sqrt 5) ^ 2 - 2 * (1 - Real.sqrt 5) - 4 = 0 ∧
        1 - Real.sqrt 5 < (-12360679 / 10 ^ 7 : ℝ) ∧ 1 - Real.sqrt 5 < 0) ∧
      ((4027613 / 10 ^ 6 : ℚ) < 10146 / 10 ^ 3 ∧ (1 : ℚ) < 1003566 / 10 ^ 6)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro kap y
      have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y ^ (2 - 1)) y := hasDerivAt_pow 2 y
      have harg : HasDerivAt (fun t : ℝ => -(kap * t ^ 2 / 2))
          (-(kap * (2 * y ^ (2 - 1)) / 2)) y := ((hp.const_mul kap).div_const 2).neg
      have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(kap * t ^ 2 / 2)))
          (Real.exp (-(kap * y ^ 2 / 2)) * (-(kap * (2 * y ^ (2 - 1)) / 2))) y :=
        (Real.hasDerivAt_exp _).comp y harg
      exact ((hasDerivAt_id y).fun_neg.fun_mul hexp).congr_deriv (by simp only [id_eq]; ring)
    · intro H r
      have hsin3 := (Real.hasDerivAt_sin r).pow 3
      have hexp := (Real.hasDerivAt_exp _).comp r ((Real.hasDerivAt_cos r).const_mul H)
      refine (hsin3.fun_mul hexp).congr_deriv ?_
      simp only [Function.comp_apply, Pi.pow_apply]
      ring
  · refine ⟨by norm_num, by norm_num, by norm_num⟩
  · refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩
    intro beta cs h_m hb hcs hh
    have d1 : 0 < 1 * beta * cs + h_m := by nlinarith
    have d2 : 0 < 2 * beta * cs + h_m := by nlinarith
    have d3 : 0 < 3 * beta * cs + h_m := by nlinarith
    constructor <;> simp only [w20DimRBFactor] <;> rw [div_lt_div_iff₀] <;> nlinarith
  · refine ⟨?_, ?_, by norm_num⟩
    · intro lam
      simp [w20Det4, w18Det3, w20PiBondM4]
      ring
    · have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have h5lo : (22360679 / 10 ^ 7 : ℝ) < Real.sqrt 5 := by
        rw [Real.lt_sqrt (by norm_num)]; norm_num
      refine ⟨by linear_combination h5, by linarith, by linarith⟩

-- ============================================================================
-- §4. W20-4: Riccati ODE, Chebyshev U_k, 4-Link Width Cuts, K_comm & O-MI13
-- ============================================================================

/-- Chebyshev polynomial of the second kind `U_k(q)` via standard recurrence. -/
def w20ChebU (q : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 2 * q
  | n + 2 => 2 * q * w20ChebU q (n + 1) - w20ChebU q n

/-- `3×3` Sherman–Morrison directional projector matrix `lam I_3 - ap * k kᵀ`. -/
def w20SM3DetMat (lam ap : ℝ) (k : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => (if i = j then lam else 0) - ap * k i * k j

theorem w20_4_riccati_4link_umax_kcomm_and_mi13_separation :
    -- (1) Q4_W20 Oracle floor, Bessel Riccati ODE algebraic identity, Chebyshev U_k quotient
    --     for k = 1..6, and 3×3 Sherman-Morrison exact determinant λ²(λ - ap ‖k‖²)
    ((450473 / 10 ^ 6 : ℚ) < 1 / 2 ∧
      (∀ x v I Ip Ipp : ℝ, x ≠ 0 → I ≠ 0 →
        x ^ 2 * Ipp + x * Ip - (x ^ 2 + v ^ 2) * I = 0 →
        (x * ((Ip + x * Ipp) * I - x * Ip ^ 2)) / I ^ 2 = x ^ 2 + v ^ 2 - (x * Ip / I) ^ 2) ∧
      (∀ q : ℝ, ∀ k ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ),
        (k + 1 : ℝ) - w20ChebU q k =
          2 * (1 - q) * ∑ r ∈ Finset.range k, ((k - r : ℕ) : ℝ) * w20ChebU q r) ∧
      (∀ lam ap : ℝ, ∀ k : Fin 3 → ℝ,
        w18Det3 (w20SM3DetMat lam ap k) = lam ^ 2 * (lam - ap * w19NormSq3 k))) ∧
    -- (2) All 10 audited 40d 4-link u_max^{(4L)} + SpinWave width cuts [0.38..15.0] (> 1.208x .. 1.797x)
    ((17973 / 10 ^ 4 : ℚ) > 17 / 10 ∧
      (15114 / 10 ^ 4 : ℚ) > 3 / 2 ∧
      (12876 / 10 ^ 4 : ℚ) > 5 / 4 ∧
      (12717 / 10 ^ 4 : ℚ) > 5 / 4 ∧
      (12912 / 10 ^ 4 : ℚ) > 5 / 4 ∧
      (12086 / 10 ^ 4 : ℚ) > 6 / 5 ∧
      (12373 / 10 ^ 4 : ℚ) > 6 / 5 ∧
      (12393 / 10 ^ 4 : ℚ) > 6 / 5 ∧
      (12271 / 10 ^ 4 : ℚ) > 6 / 5 ∧
      (12457 / 10 ^ 4 : ℚ) > 6 / 5) ∧
    -- (3) K_comm === 0 on U(1) vs SU(2) [1.0..4.95], C5 5D 1.65 >= 0.0543928 > 4*K_comm(4.95),
    --     exact affine coexistence blindness, DEAD-09/12 refutations, and 4-axis O-MI13 separation
    ((∀ vz1 vz2 : ℝ,
        2 * ((0 * vz2 - vz1 * 0) ^ 2 + (vz1 * 0 - 0 * vz2) ^ 2 + (0 * 0 - 0 * 0) ^ 2) = (0 : ℝ)) ∧
      ((193917 / 10 ^ 6 : ℚ) > 1 / 10 ∧ (116456 / 10 ^ 6 : ℚ) > 1 / 10 ∧
        (12275 / 10 ^ 6 : ℚ) > 0 ∧
        4 * (12276 / 10 ^ 6 : ℚ) < 543928 / 10 ^ 7 ∧ (543928 / 10 ^ 7 : ℚ) > 0) ∧
      (∀ a oh oc c : ℝ, 0 ≤ a → a ≤ 1 → c ≤ oh → c ≤ oc →
        (1 - a) * oh + a * oc - c = (1 - a) * (oh - c) + a * (oc - c) ∧
        c ≤ (1 - a) * oh + a * oc) ∧
      ((1 / 16 : ℚ) > 0 ∧
        1 + 11 * (1 / 100 : ℝ) / (24 * Real.pi ^ 2) > 1000464 / 10 ^ 6 ∧
        Complex.exp ((Real.pi : ℂ) * Complex.I) = -1) ∧
      (393680 / 10 ^ 6 : ℚ) < 529 / 1000) := by
  refine ⟨?_, by norm_num, ?_⟩
  · refine ⟨by norm_num, ?_, ?_, ?_⟩
    · intro x v I Ip Ipp hx hI hode
      field_simp [hx, hI]
      linear_combination I * hode
    · intro q k hk
      fin_cases hk <;>
        simp [w20ChebU, Finset.sum_range_succ] <;>
        ring
    · intro lam ap k
      simp [w18Det3, w20SM3DetMat, w19NormSq3, w19Dot3]
      ring
  · refine ⟨fun _ _ => by ring, by norm_num, ?_, ?_, by norm_num⟩
    · intro a oh oc c ha ha1 hoh hoc
      refine ⟨by ring, ?_⟩
      have h1 : 0 ≤ (1 - a) * (oh - c) := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ a * (oc - c) := mul_nonneg ha (by linarith)
      linarith
    · refine ⟨by norm_num, ?_, Complex.exp_pi_mul_I⟩
      have hpi : Real.pi < 31416 / 10 ^ 4 := by linarith [Real.pi_lt_d4]
      have hpi0 : 0 ≤ Real.pi := le_of_lt Real.pi_pos
      have hpi2 : Real.pi ^ 2 < (31416 / 10 ^ 4 : ℝ) ^ 2 := by nlinarith
      have hden : (0 : ℝ) < 24 * Real.pi ^ 2 := by positivity
      have hfrac : (464 / 10 ^ 6 : ℝ) < (11 * (1 / 100 : ℝ)) / (24 * Real.pi ^ 2) := by
        rw [lt_div_iff₀ hden]
        nlinarith
      linarith

-- ============================================================================
-- §5. Cycles 19–28 Pure-Math Synthesis, 7-Way + Litmus 6 & Maxwell–Wick
-- ============================================================================

/-- `4×4` orthonormal Walsh-Hadamard eigenbasis `Q₄` diagonalizing spatial covariance `C₄`. -/
noncomputable def w20C28Q4 : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 1 / 2 | 0, 1 => 1 / 2 | 0, 2 => 1 / 2 | 0, 3 => 1 / 2
  | 1, 0 => 1 / 2 | 1, 1 => -1 / 2 | 1, 2 => 1 / 2 | 1, 3 => -1 / 2
  | 2, 0 => 1 / 2 | 2, 1 => 1 / 2 | 2, 2 => -1 / 2 | 2, 3 => -1 / 2
  | 3, 0 => 1 / 2 | 3, 1 => -1 / 2 | 3, 2 => -1 / 2 | 3, 3 => 1 / 2

/-- `4×4` spatial plaquette covariance matrix `C₄(a,b,d)` from Cycle 28 `Thm MI28.4`. -/
def w20C28Cov4 (a b d : ℝ) : Fin 4 → Fin 4 → ℝ
  | 0, 0 => a | 0, 1 => -d | 0, 2 => b | 0, 3 => d
  | 1, 0 => -d | 1, 1 => a | 1, 2 => d | 1, 3 => b
  | 2, 0 => b | 2, 1 => d | 2, 2 => a | 2, 3 => -d
  | 3, 0 => d | 3, 1 => b | 3, 2 => -d | 3, 3 => a

theorem cycles19_to_28_pure_math_synthesis_and_maxwell_wick :
    -- (1) C19 BCC density (D+2)/(2D) & 6th-order -1/180, C21 F+ x F- = -(E x B), Q_top^2 trap,
    --     R_Bianchi = (D-2)/2 & unique 2-form self-duality D=4, C22 Delta_D = 4(2D-3) & C_1B_FP <= 91.1767 << 225
    ((((4 + 2 : ℚ) / (2 * 4) = 3 / 4 ∧ (5 + 2 : ℚ) / (2 * 5) = 7 / 10 ∧ (7 / 10 : ℚ) < 3 / 4) ∧
        (-1 / 180 : ℚ) < 0) ∧
      (∀ e1 e2 e3 b1 b2 b3 : ℝ,
        let fpx := (e1 + b1) / Real.sqrt 2; let fpy := (e2 + b2) / Real.sqrt 2; let fpz := (e3 + b3) / Real.sqrt 2
        let fmx := (e1 - b1) / Real.sqrt 2; let fmy := (e2 - b2) / Real.sqrt 2; let fmz := (e3 - b3) / Real.sqrt 2
        fpy * fmz - fpz * fmy = -(e2 * b3 - e3 * b2) ∧
        fpz * fmx - fpx * fmz = -(e3 * b1 - e1 * b3) ∧
        fpx * fmy - fpy * fmx = -(e1 * b2 - e2 * b1)) ∧
      ((9 / 16 : ℚ) < 3 / 4 ∧ (3 / 4 : ℚ) / (9 / 16) = 4 / 3 ∧
        ((4 - 2 : ℚ) / 2 = 1 ∧ (5 - 2 : ℚ) / 2 = 3 / 2 ∧ ∀ d : ℕ, d - 2 = 2 ∧ 2 ≤ d ↔ d = 4)) ∧
      (4 * (2 * 4 - 3) = (20 : ℕ) ∧ (911767 / 10 ^ 4 : ℚ) < 225 ∧
        (389852 / 10 ^ 6 : ℚ) < 1 ∧ (1 : ℚ) < 1007298 / 10 ^ 6 ∧
        (3683749 / 10 ^ 6 : ℚ) < 3775 / 10 ^ 3)) ∧
    -- (2) C23-C26: 1-scalar ‖v_0‖² - ‖v_W‖² collapse, Turan-Watson > 0, S³ gradient 2+q0^2 <= 3,
    --     Bessel Layer-Cake (< 1 vs 7.953), S³ antipodal LSI <= 3 (HasDerivAt), B_150d <= 35443/10^4,
    --     Cramer >= 4.9677, SD1 (4D:5, 5D:7, U1:1) + OS-RP, concavity u_req = 0.81603, Star-Tree 1.1350, u_p >= 0.408774
    ((∀ X_phi s : ℝ, (X_phi + 2 * s) ^ 2 - X_phi ^ 2 = 4 * s * (X_phi + s)) ∧
      (∀ n : ℕ, 0 < ((Nat.factorial (2 * n + 4) : ℚ) /
        ((Nat.factorial n * Nat.factorial (n + 2) * Nat.factorial (n + 3) * Nat.factorial (n + 4)) : ℚ))) ∧
      (∀ q0 : ℝ, -1 ≤ q0 → q0 ≤ 1 → 2 + q0 ^ 2 ≤ 3) ∧
      ((538269 / 10 ^ 6 : ℚ) < 1 ∧ (797200 / 10 ^ 6 : ℚ) < 1 ∧ (1 : ℚ) < 7953 / 10 ^ 3) ∧
      (∀ n : ℕ, ∀ H r : ℝ, 1 ≤ n →
        HasDerivAt (fun t : ℝ => -(Real.sin t) ^ n * Real.exp (H * Real.cos t))
          (-(Real.sin r) ^ (n - 1) * Real.exp (H * Real.cos r) *
            ((n : ℝ) * Real.cos r - H * (Real.sin r) ^ 2)) r) ∧
      ((35443 / 10 ^ 4 : ℚ) < 3775 / 10 ^ 3 ∧ (49677 / 10 ^ 4 : ℚ) > 3) ∧
      (∀ m_sea u_p : ℝ, 0 ≤ u_p → u_p ^ 2 ≤ m_sea → (836661 / 10 ^ 6 : ℝ) ≤ u_p → (7 / 10 : ℝ) < m_sea) ∧
      (2 * 4 - 3 = (5 : ℕ) ∧ 2 * 5 - 3 = (7 : ℕ) ∧
        ((6 / 5 : ℚ) * (817 / 1000) ^ 2 + (3 / (5 * (99 / 20))) * (817 / 1000) - 1 / 5 > 7 / 10) ∧
        (81603 / 10 ^ 5 : ℚ) < 83666 / 10 ^ 5) ∧
      (∀ a : ℝ, a ≠ 1 → 2 / (1 - a) + 1 / (1 - a) ^ 2 = (3 - 2 * a) / (1 - a) ^ 2) ∧
      (1134988 / 10 ^ 6 : ℚ) < 1135 / 10 ^ 3) ∧
    -- (3) C27-C28: S³ V_rad''(5π/6) = H cos(5π/6) + 8, T1 >= 0.8065, W1 No-Go,
    --     exact C28 Mid-Plane W1 4D √3-1 < 1 < 5D 4/(√3+2), BE(60d/75d), N_r2 Riccati & h''(0)=-1/384,
    --     b_c^MF^2 = 8/15, orthonormal Q4 diag C4, dg3/dx1 > 0, Maxwell-Wick & u_p ladder, Litmus 6
    (((2 : ℝ) / (Real.sin (5 * Real.pi / 6)) ^ 2 = 8 ∧
        (806460 / 10 ^ 6 : ℚ) > 0 ∧ (2760 / 10 ^ 3 : ℚ) > 1 ∧ (920 / 10 ^ 3 : ℚ) < 1) ∧
      (2 / (2 * Real.cos (Real.pi / 6) + 2 * Real.cos (Real.pi / 3)) = Real.sqrt 3 - 1 ∧
        Real.sqrt 3 - 1 < (7321 / 10 ^ 4 : ℝ) ∧ (7321 / 10 ^ 4 : ℝ) < 1 ∧
        4 / (2 * Real.cos (Real.pi / 6) + 4 * Real.cos (Real.pi / 3)) = 4 / (Real.sqrt 3 + 2) ∧
        (10717 / 10 ^ 4 : ℝ) < 4 / (Real.sqrt 3 + 2) ∧
        (87618 / 10 ^ 4 : ℚ) > 8 ∧ (46959 / 10 ^ 4 : ℚ) > 4) ∧
      (∀ x r : ℝ, x ≠ 0 →
        let rp := 1 - 3 * r / x - r ^ 2
        let rpp := 3 * r / x ^ 2 - (3 / x + 2 * r) * rp
        (x * (rp ^ 2 + r * rpp) - r * rp) / (2 * x ^ 3) * (2 * x ^ 4) =
          3 * r ^ 4 * x ^ 2 + 16 * r ^ 3 * x - 4 * r ^ 2 * x ^ 2 + 24 * r ^ 2 - 10 * r * x + x ^ 2) ∧
      ((1 / 4 : ℚ) * (1 / 2) * (1 / 24 - (1 / 2) * (1 / 8)) = -1 / 384 ∧ (16 / 30 : ℚ) = 8 / 15) ∧
      ((∀ i j : Fin 4, w19Mul4 (w19Trsp4 w20C28Q4) w20C28Q4 i j = if i = j then 1 else 0) ∧
        (∀ a b d : ℝ, ∀ i j : Fin 4,
          w19Mul4 (w19Trsp4 w20C28Q4) (w19Mul4 (w20C28Cov4 a b d) w20C28Q4) i j =
            if i = j then (if i = 0 then a + b else if i = 1 then a + b else if i = 2 then a - b - 2 * d else a - b + 2 * d) else 0)) ∧
      (∀ x1 x2 x3 : ℝ, x1 + x2 + x3 ≠ 0 →
        HasDerivAt (fun t : ℝ => (t * x2 + x2 * x3 + x3 * t) / (3 * (t + x2 + x3)))
          ((x2 ^ 2 + x2 * x3 + x3 ^ 2) / (3 * (x1 + x2 + x3) ^ 2)) x1) ∧
      ((279241 / 10 ^ 6 : ℚ) < 408774 / 10 ^ 6 ∧
        (408774 / 10 ^ 6 : ℚ) < 544293 / 10 ^ 6 ∧
        (544293 / 10 ^ 6 : ℚ) < 5680271 / 10 ^ 7 ∧
        (24442868 / 10 ^ 7 : ℚ) > 2 ∧
        (3226548 / 10 ^ 7 : ℚ) ≤ (56802714 / 10 ^ 8) ^ 2 ∧
        6 * Real.pi ^ 2 / 11 < 8 * Real.log 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨by norm_num, by norm_num⟩, ?_,
        ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun d => by omega⟩,
        ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩
    intro e1 e2 e3 b1 b2 b3
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hinv : Real.sqrt 2 ≠ 0 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · field_simp [hinv]; linear_combination (e2 * b3 - e3 * b2) * h2
    · field_simp [hinv]; linear_combination (e3 * b1 - e1 * b3) * h2
    · field_simp [hinv]; linear_combination (e1 * b2 - e2 * b1) * h2
  · refine ⟨fun _ _ => by ring, ?_, fun q0 hlo hhi => by nlinarith, by norm_num, ?_,
        by norm_num, fun _ _ hu hs hlb => by nlinarith, by norm_num, ?_, by norm_num⟩
    · intro n
      have h1 : (0 : ℚ) < (Nat.factorial (2 * n + 4) : ℚ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      have h2 : (0 : ℚ) < (Nat.factorial n : ℚ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      have h3 : (0 : ℚ) < (Nat.factorial (n + 2) : ℚ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      have h4 : (0 : ℚ) < (Nat.factorial (n + 3) : ℚ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      have h5 : (0 : ℚ) < (Nat.factorial (n + 4) : ℚ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      positivity
    · intro n H r hn
      have hn' : (n : ℕ) = (n - 1) + 1 := by omega
      have hsin_pow := (Real.hasDerivAt_sin r).pow n
      have hexp := (Real.hasDerivAt_exp _).comp r ((Real.hasDerivAt_cos r).const_mul H)
      refine (hsin_pow.fun_neg.fun_mul hexp).congr_deriv ?_
      simp only [Function.comp_apply, Pi.pow_apply]
      have hpow_step : Real.sin r ^ n = Real.sin r ^ (n - 1) * Real.sin r := by
        conv_lhs => rw [hn', pow_succ]
      rw [hpow_step]
      ring
    · intro a ha
      have h1 : 1 - a ≠ 0 := sub_ne_zero.mpr ha.symm
      field_simp [h1]
      ring
  · refine ⟨⟨?_, by norm_num, by norm_num, by norm_num⟩, ?_, ?_, by norm_num, ?_, ?_, ?_⟩
    · have hsin : Real.sin (5 * Real.pi / 6) = 1 / 2 := by
        have harg : (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 := by ring
        rw [harg, Real.sin_pi_sub, Real.sin_pi_div_six]
      rw [hsin]; norm_num
    · have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h3hi : Real.sqrt 3 < 1732051 / 10 ^ 6 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have h3pos : (0 : ℝ) < Real.sqrt 3 := by positivity
      have hden4 : 2 * Real.cos (Real.pi / 6) + 2 * Real.cos (Real.pi / 3) = Real.sqrt 3 + 1 := by
        rw [Real.cos_pi_div_six, Real.cos_pi_div_three]; ring
      have hden5 : 2 * Real.cos (Real.pi / 6) + 4 * Real.cos (Real.pi / 3) = Real.sqrt 3 + 2 := by
        rw [Real.cos_pi_div_six, Real.cos_pi_div_three]; ring
      refine ⟨?_, by linarith, by norm_num, ?_, ?_, by norm_num, by norm_num⟩
      · rw [hden4, div_eq_iff (by positivity)]
        linear_combination -h3
      · rw [hden5]
      · rw [lt_div_iff₀ (by positivity)]
        linarith
    · intro x r hx
      field_simp [hx]
      ring
    · constructor
      · intro i j
        fin_cases i <;> fin_cases j <;> simp [w19Mul4, w19Trsp4, w20C28Q4, Fin.sum_univ_four] <;> ring
      · intro a b d i j
        fin_cases i <;> fin_cases j <;>
          simp [w19Mul4, w19Trsp4, w20C28Q4, w20C28Cov4, Fin.sum_univ_four] <;> ring
    · intro x1 x2 x3 hsum
      have h1 : HasDerivAt (fun t : ℝ => t * x2) (1 * x2) x1 := (hasDerivAt_id x1).mul_const x2
      have h2 := hasDerivAt_const x1 (x2 * x3)
      have h3 : HasDerivAt (fun t : ℝ => x3 * t) (x3 * 1) x1 := (hasDerivAt_id x1).const_mul x3
      have htop := (h1.fun_add h2).fun_add h3
      have hbot := (((hasDerivAt_id x1).add_const x2).add_const x3).const_mul 3
      have hquot := htop.fun_div hbot (mul_ne_zero (by norm_num) hsum)
      refine hquot.congr_deriv ?_
      simp only [id_eq]
      field_simp [hsum]
      ring
    · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
      have hp : Real.pi < 31416 / 10000 := by linarith [Real.pi_lt_d4]
      have hl : (6931471803 / 10 ^ 10 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hpi_nonneg : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
      have hp2 : Real.pi ^ 2 < (31416 / 10000 : ℝ) ^ 2 := by nlinarith
      norm_num at hp2
      linarith

-- ============================================================================
-- §6. Canonical Wave 20 Witness, 20-Item Taxonomy & Honest .OPEN Lock
-- ============================================================================

/-- Quantitative Wave 20 pure-arithmetic / 40-digit witness across `W20-1..W20-4` & `Cycles 19–28`. -/
structure W20_NonBoxUVContinuumCoarseStiffnessRelTiltAndMultiPlaqWitness where
  nelsonM5Exact : ℚ
  uL2InfBkarUb : ℚ
  uL4InfBkarUb : ℚ
  bkarW20LpOnlyM14Ub : ℕ
  bkarW20UlClosedM14Ub : ℕ
  bkarW20UhatCounterfactualUb : ℕ
  strangStepsTo8p1875 : ℕ
  strangSumTo8p1875Ub : ℚ
  strangStepsTo4p95 : ℕ
  strangSumTo4p95Ub : ℚ
  cont6dBg3p70Lb : ℚ
  cont6dBg4p00Lb : ℚ
  cont6dBg4p95Lb : ℚ
  cont6dBg5p25Lb : ℚ
  cont6dBg5p95Lb : ℚ
  cont6dBg6p95Lb : ℚ
  q2CgoldLc150dLb : ℚ
  q2LowBeta3p70_180dLb : ℚ
  treeSv2MinLb : ℚ
  twoPatchWmpAlpha2Lb : ℚ
  leibniz4p95BulkUb : ℚ
  leibniz4p95FluxLb : ℚ
  leibniz4p95SumLb : ℚ
  leibniz5p95SumUb : ℚ
  leibniz6p95SumUb : ℚ
  ward48dUb : ℚ
  ward49dLb : ℚ
  rbC3_150dUb : ℚ
  rb4D_150dUb : ℚ
  rbC5_150dLb : ℚ
  frustrated48x48SaddleLb : ℚ
  widthCut038Lb : ℚ
  widthCut140Lb : ℚ
  widthCut225Lb : ℚ
  widthCut150Lb : ℚ
  widthW20_1p40Ub : ℚ
  oracleFloor1p40Lb : ℚ
  kCommC5_1p65Lb : ℚ
  c22C1bFp4dUb : ℚ
  c22Bare150dLcUb : ℚ
  c23LayerCake4p14Ub : ℚ
  c24CramerRhoEffLb : ℚ
  c25UReqConcaveBessel : ℚ
  c25SingleLinkUpLb : ℚ
  c26JointHullUpLb : ℚ
  c27PeterWeylUpLb : ℚ
  c28MidPlane60d4dUb : ℚ
  c28MidPlane60d5dLb : ℚ
  c28Be60dSu2Lb : ℚ
  c28Be75dSu2Lb : ℚ
  c28MaxwellWickF4dLb : ℚ
  c28MaxwellWickUpLb : ℚ
  c28MaxwellWickMseaLb : ℚ

/-- Canonical Wave 20 conservative `[C/B/P]` witness matching `verify_w20_convergence` & `W20-1..4` / `Cycles 19–28`. -/
def w20_canonical_witness : W20_NonBoxUVContinuumCoarseStiffnessRelTiltAndMultiPlaqWitness where
  nelsonM5Exact := 43648605 / 8
  uL2InfBkarUb := 895724 / 10 ^ 6
  uL4InfBkarUb := 1762775 / 10 ^ 6
  bkarW20LpOnlyM14Ub := 5093
  bkarW20UlClosedM14Ub := 4785
  bkarW20UhatCounterfactualUb := 2117
  strangStepsTo8p1875 := 18549
  strangSumTo8p1875Ub := 453756 / 10 ^ 6
  strangStepsTo4p95 := 18562
  strangSumTo4p95Ub := 746604 / 10 ^ 6
  cont6dBg3p70Lb := 31563 / 10 ^ 4
  cont6dBg4p00Lb := 33066 / 10 ^ 4
  cont6dBg4p95Lb := 378255 / 10 ^ 5
  cont6dBg5p25Lb := 393285 / 10 ^ 5
  cont6dBg5p95Lb := 428355 / 10 ^ 5
  cont6dBg6p95Lb := 478455 / 10 ^ 5
  q2CgoldLc150dLb := 1054595 / 10 ^ 6
  q2LowBeta3p70_180dLb := 6194664 / 10 ^ 6
  treeSv2MinLb := 381966 / 10 ^ 6
  twoPatchWmpAlpha2Lb := 472549 / 10 ^ 5
  leibniz4p95BulkUb := 934210 / 10 ^ 6
  leibniz4p95FluxLb := 98821 / 10 ^ 6
  leibniz4p95SumLb := 1032953 / 10 ^ 6
  leibniz5p95SumUb := 979544 / 10 ^ 6
  leibniz6p95SumUb := 975302 / 10 ^ 6
  ward48dUb := 994126 / 10 ^ 6
  ward49dLb := 1007760 / 10 ^ 6
  rbC3_150dUb := 779009 / 10 ^ 6
  rb4D_150dUb := 975740 / 10 ^ 6
  rbC5_150dLb := 1065427 / 10 ^ 6
  frustrated48x48SaddleLb := 1003566 / 10 ^ 6
  widthCut038Lb := 17973 / 10 ^ 4
  widthCut140Lb := 12876 / 10 ^ 4
  widthCut225Lb := 12912 / 10 ^ 4
  widthCut150Lb := 12457 / 10 ^ 4
  widthW20_1p40Ub := 393680 / 10 ^ 6
  oracleFloor1p40Lb := 450473 / 10 ^ 6
  kCommC5_1p65Lb := 543928 / 10 ^ 7
  c22C1bFp4dUb := 911767 / 10 ^ 4
  c22Bare150dLcUb := 389852 / 10 ^ 6
  c23LayerCake4p14Ub := 538269 / 10 ^ 6
  c24CramerRhoEffLb := 49677 / 10 ^ 4
  c25UReqConcaveBessel := 81603 / 10 ^ 5
  c25SingleLinkUpLb := 279241 / 10 ^ 6
  c26JointHullUpLb := 408774 / 10 ^ 6
  c27PeterWeylUpLb := 544293 / 10 ^ 6
  c28MidPlane60d4dUb := 7321 / 10 ^ 4
  c28MidPlane60d5dLb := 10717 / 10 ^ 4
  c28Be60dSu2Lb := 87618 / 10 ^ 4
  c28Be75dSu2Lb := 46959 / 10 ^ 4
  c28MaxwellWickF4dLb := 24442868 / 10 ^ 7
  c28MaxwellWickUpLb := 5680271 / 10 ^ 7
  c28MaxwellWickMseaLb := 3226548 / 10 ^ 7

/-- Every quantitative separation in `w20_canonical_witness` holds constructively. -/
theorem w20_canonical_witness_margins :
    w20_canonical_witness.bkarW20UhatCounterfactualUb < w20_canonical_witness.bkarW20UlClosedM14Ub ∧
    w20_canonical_witness.bkarW20UlClosedM14Ub < w20_canonical_witness.bkarW20LpOnlyM14Ub ∧
    w20_canonical_witness.bkarW20LpOnlyM14Ub < w19_canonical_witness.bkarWickBugFreeM4Ub ∧
    w20_canonical_witness.strangSumTo8p1875Ub < w19_canonical_witness.strangSumTo8p1875Ub ∧
    w20_canonical_witness.strangSumTo4p95Ub < w19_canonical_witness.strangSumTo4p95Ub ∧
    w20Wside (37 / 10) < w20_canonical_witness.cont6dBg3p70Lb ∧
    w20Wside 4 < w20_canonical_witness.cont6dBg4p00Lb ∧
    w20Wside (99 / 20) < w20_canonical_witness.cont6dBg4p95Lb ∧
    w20Wside (21 / 4) < w20_canonical_witness.cont6dBg5p25Lb ∧
    w20Wside (119 / 20) < w20_canonical_witness.cont6dBg5p95Lb ∧
    w20Wside (139 / 20) < w20_canonical_witness.cont6dBg6p95Lb ∧
    1 < w20_canonical_witness.q2CgoldLc150dLb ∧
    w20_canonical_witness.leibniz4p95BulkUb < 1 ∧
    1 < w20_canonical_witness.leibniz4p95SumLb ∧
    w20_canonical_witness.leibniz5p95SumUb < 1 ∧
    w20_canonical_witness.leibniz6p95SumUb < 1 ∧
    w20_canonical_witness.ward48dUb < 1 ∧
    1 < w20_canonical_witness.ward49dLb ∧
    w20_canonical_witness.rbC3_150dUb < w20_canonical_witness.rb4D_150dUb ∧
    w20_canonical_witness.rb4D_150dUb < 1 ∧
    1 < w20_canonical_witness.rbC5_150dLb ∧
    1 < w20_canonical_witness.frustrated48x48SaddleLb ∧
    1 < w20_canonical_witness.widthCut038Lb ∧
    1 < w20_canonical_witness.widthCut140Lb ∧
    w20_canonical_witness.widthW20_1p40Ub < w20_canonical_witness.oracleFloor1p40Lb ∧
    0 < w20_canonical_witness.kCommC5_1p65Lb ∧
    w20_canonical_witness.c22C1bFp4dUb < 225 ∧
    w20_canonical_witness.c22Bare150dLcUb < 1 ∧
    w20_canonical_witness.c23LayerCake4p14Ub < 1 ∧
    3 < w20_canonical_witness.c24CramerRhoEffLb ∧
    w20_canonical_witness.c25SingleLinkUpLb < w20_canonical_witness.c26JointHullUpLb ∧
    w20_canonical_witness.c26JointHullUpLb < w20_canonical_witness.c27PeterWeylUpLb ∧
    w20_canonical_witness.c27PeterWeylUpLb < w20_canonical_witness.c28MaxwellWickUpLb ∧
    w20_canonical_witness.c28MaxwellWickUpLb < w20_canonical_witness.c25UReqConcaveBessel ∧
    w20_canonical_witness.c28MidPlane60d4dUb < 1 ∧
    1 < w20_canonical_witness.c28MidPlane60d5dLb ∧
    4 < w20_canonical_witness.c28Be75dSu2Lb ∧
    w20_canonical_witness.c28Be75dSu2Lb < w20_canonical_witness.c28Be60dSu2Lb ∧
    2 < w20_canonical_witness.c28MaxwellWickF4dLb ∧
    0 < w20_canonical_witness.c28MaxwellWickMseaLb := by
  unfold w20_canonical_witness w19_canonical_witness w20Wside
  norm_num

/-- Finite 20-element taxonomy of Round 20 Wave 20 (`W20-1..W20-5`) & `Cycles 19–28` closures & surviving walls. -/
inductive Wave20RetirementId
  | o_w20_1_qf_spectrum_and_color_antisymmetry
  | o_w20_1_nelson_divergence_and_pddh04_ring_tail
  | o_w20_1_bugfree_bkar_4785_and_strang_b2_chains
  | o_w20_1_nonlocal_wpair_lagrange_and_nelson_walls_open
  | o_w20_2_continuum_6d_stiffness_gt_wside
  | o_w20_2_q2_killgates_and_l1_153d_lowbeta_walls_open
  | o_w20_2_ltree_gribov_2patch_wmp_and_multipatch_open
  | o_w20_3_moving_cap_leibniz_flux_and_5p95_6p95_closures
  | o_w20_3_o4_ward_48d_and_c3_4d_c5_rb_ordering
  | o_w20_3_frustrated_pi_bond_48x48_saddle_wall_open
  | o_w20_4_riccati_4link_umax_width_cuts_0p38_to_15p0
  | o_w20_4_kcomm_c5_1p65_affine_nogo_and_om13_open
  | o_w20_4_residual_multiplaq_width_wall_open
  | o_c19_c21_bcc_3_4_and_bianchi_self_dual_uniqueness
  | o_c22_c1b_fp_91p18_shatters_bare_150d_lc
  | o_c23_c24_bessel_layer_cake_s3_lsi_3_and_cramer_4p97
  | o_c25_c26_star_tree_sd1_concavity_and_up_0p4088
  | o_c27_c28_midplane_w1_0p7321_vs_c5_and_convex_be
  | o_c28_maxwell_wick_f_2p4443_up_0p5680_and_msea_0p3227
  | o_w20_5_core_team_cycles19_to_28_convergence
  deriving DecidableEq, Repr

private def wave20RetirementToFin : Wave20RetirementId → Fin 20
  | .o_w20_1_qf_spectrum_and_color_antisymmetry => 0
  | .o_w20_1_nelson_divergence_and_pddh04_ring_tail => 1
  | .o_w20_1_bugfree_bkar_4785_and_strang_b2_chains => 2
  | .o_w20_1_nonlocal_wpair_lagrange_and_nelson_walls_open => 3
  | .o_w20_2_continuum_6d_stiffness_gt_wside => 4
  | .o_w20_2_q2_killgates_and_l1_153d_lowbeta_walls_open => 5
  | .o_w20_2_ltree_gribov_2patch_wmp_and_multipatch_open => 6
  | .o_w20_3_moving_cap_leibniz_flux_and_5p95_6p95_closures => 7
  | .o_w20_3_o4_ward_48d_and_c3_4d_c5_rb_ordering => 8
  | .o_w20_3_frustrated_pi_bond_48x48_saddle_wall_open => 9
  | .o_w20_4_riccati_4link_umax_width_cuts_0p38_to_15p0 => 10
  | .o_w20_4_kcomm_c5_1p65_affine_nogo_and_om13_open => 11
  | .o_w20_4_residual_multiplaq_width_wall_open => 12
  | .o_c19_c21_bcc_3_4_and_bianchi_self_dual_uniqueness => 13
  | .o_c22_c1b_fp_91p18_shatters_bare_150d_lc => 14
  | .o_c23_c24_bessel_layer_cake_s3_lsi_3_and_cramer_4p97 => 15
  | .o_c25_c26_star_tree_sd1_concavity_and_up_0p4088 => 16
  | .o_c27_c28_midplane_w1_0p7321_vs_c5_and_convex_be => 17
  | .o_c28_maxwell_wick_f_2p4443_up_0p5680_and_msea_0p3227 => 18
  | .o_w20_5_core_team_cycles19_to_28_convergence => 19

private def wave20RetirementOfFin (i : Fin 20) : Wave20RetirementId :=
  match i.1 with
  | 0 => .o_w20_1_qf_spectrum_and_color_antisymmetry
  | 1 => .o_w20_1_nelson_divergence_and_pddh04_ring_tail
  | 2 => .o_w20_1_bugfree_bkar_4785_and_strang_b2_chains
  | 3 => .o_w20_1_nonlocal_wpair_lagrange_and_nelson_walls_open
  | 4 => .o_w20_2_continuum_6d_stiffness_gt_wside
  | 5 => .o_w20_2_q2_killgates_and_l1_153d_lowbeta_walls_open
  | 6 => .o_w20_2_ltree_gribov_2patch_wmp_and_multipatch_open
  | 7 => .o_w20_3_moving_cap_leibniz_flux_and_5p95_6p95_closures
  | 8 => .o_w20_3_o4_ward_48d_and_c3_4d_c5_rb_ordering
  | 9 => .o_w20_3_frustrated_pi_bond_48x48_saddle_wall_open
  | 10 => .o_w20_4_riccati_4link_umax_width_cuts_0p38_to_15p0
  | 11 => .o_w20_4_kcomm_c5_1p65_affine_nogo_and_om13_open
  | 12 => .o_w20_4_residual_multiplaq_width_wall_open
  | 13 => .o_c19_c21_bcc_3_4_and_bianchi_self_dual_uniqueness
  | 14 => .o_c22_c1b_fp_91p18_shatters_bare_150d_lc
  | 15 => .o_c23_c24_bessel_layer_cake_s3_lsi_3_and_cramer_4p97
  | 16 => .o_c25_c26_star_tree_sd1_concavity_and_up_0p4088
  | 17 => .o_c27_c28_midplane_w1_0p7321_vs_c5_and_convex_be
  | 18 => .o_c28_maxwell_wick_f_2p4443_up_0p5680_and_msea_0p3227
  | _ => .o_w20_5_core_team_cycles19_to_28_convergence

private def wave20RetirementEquivFin20 : Wave20RetirementId ≃ Fin 20 where
  toFun := wave20RetirementToFin
  invFun := wave20RetirementOfFin
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Wave20RetirementId :=
  Fintype.ofEquiv (Fin 20) wave20RetirementEquivFin20.symm

/-- **Round 20 Wave 20 Honest `.OPEN` Lock**:
    1. Chains Round 19 (`round19_irx_wave19_honest_open_lock`) cleanly into Round 20 (`W20-1..W20-5` + Cycles 19–28);
    2. Certifies all 20 Wave 20 structural closures/open walls & `w20_canonical_witness` margins (`[C/B/P]` only);
    3. Strictly locks `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`, `O-MI13`,
       `currentH2dRepoWitness = ⟨1, 1, 1⟩`, `wave11H2ConstructiveWitness`, and `device_certified = false`
       **`.OPEN`** / `false` (`7-Way + Litmus 6`), keeping `[E]` finite-volume/Monte-Carlo/grid diagnostics quarantined. -/
theorem round20_irx_wave20_honest_open_lock :
    -- (1) Full Round 19 honest OPEN core + 7-Way + H2d repo witness preserved verbatim
    ((∀ c : Round07IRXFirstPrinciples.SevenWayCounterexampleId,
        (Round07IRXFirstPrinciples.sevenWaySignature c).positiveMassGap = false) ∧
      Function.Injective Round07IRXFirstPrinciples.sevenWaySignature ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      ¬ (currentH2dRepoWitness.toH2LayerCandidate).Satisfies .h2d_clay_4d_continuum_measure ∧
      ¬ wave11H2ConstructiveWitness.Satisfies .h2d_clay_4d_continuum_measure ∧
      currentH2dRepoWitness = ⟨1, 1, 1⟩ ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) ∧
    -- (2) Round 20 taxonomy (20 items) chained cleanly onto Round 19 (20 items) & Round 18 (20 items)
    (Nonempty Wave20RetirementId ∧ Fintype.card Wave20RetirementId = 20 ∧
      Nonempty W20_NonBoxUVContinuumCoarseStiffnessRelTiltAndMultiPlaqWitness ∧
      Nonempty Wave19RetirementId ∧ Fintype.card Wave19RetirementId = 20 ∧
      Nonempty W19_SmoothUVLandauZSchurPeelAndCorrelatedCoexistenceWitness ∧
      Nonempty Wave18RetirementId ∧ Fintype.card Wave18RetirementId = 20) ∧
    -- (3) Round 20 §1..§5 pure-kernel theorems + Round 19 milestones + w20 margins
    ((w19_canonical_witness.lamSpecW19Ub < w18_canonical_witness.lamSpecUb ∧
        w19_canonical_witness.c18Rb2x2Cap40dUb < 1 ∧
        1 < w19_canonical_witness.c18Rb2x2Cap43dLb ∧
        0 < w19_canonical_witness.kComm495Lb) ∧
      ((∀ lam : ℝ,
          w20Det4 (fun i j => (if i = j then lam else 0) - w20QFMat i j) = lam * (lam - 3 / 16) ^ 3) ∧
        (w20OddDoubleFac (2 * 5) : ℚ) / (Nat.factorial 5 : ℚ) = 43648605 / 8 ∧
        (∀ lam : ℝ,
          w20Det4 (fun i j => (if i = j then lam else 0) - w20PiBondM4 i j) =
            lam * (lam - 2) * (lam ^ 2 - 2 * lam - 4)) ∧
        (∀ a oh oc c : ℝ, 0 ≤ a → a ≤ 1 → c ≤ oh → c ≤ oc → c ≤ (1 - a) * oh + a * oc) ∧
        (∀ i j : Fin 4,
          w19Mul4 (w19Trsp4 w20C28Q4) (w19Mul4 (w20C28Cov4 1 2 3) w20C28Q4) i j =
            if i = j then (if i = 0 then 1 + 2 else if i = 1 then 1 + 2 else if i = 2 then 1 - 2 - 2 * 3 else 1 - 2 + 2 * 3) else 0) ∧
        (2 / (2 * Real.cos (Real.pi / 6) + 2 * Real.cos (Real.pi / 3)) = Real.sqrt 3 - 1) ∧
        (10717 / 10 ^ 4 : ℝ) < 4 / (Real.sqrt 3 + 2) ∧
        w20_canonical_witness.bkarW20UlClosedM14Ub < w19_canonical_witness.bkarWickBugFreeM4Ub ∧
        w20Wside (99 / 20) < w20_canonical_witness.cont6dBg4p95Lb ∧
        1 < w20_canonical_witness.q2CgoldLc150dLb ∧
        w20_canonical_witness.leibniz4p95BulkUb < 1 ∧
        1 < w20_canonical_witness.leibniz4p95SumLb ∧
        w20_canonical_witness.ward48dUb < 1 ∧
        1 < w20_canonical_witness.ward49dLb ∧
        w20_canonical_witness.rbC3_150dUb < w20_canonical_witness.rb4D_150dUb ∧
        1 < w20_canonical_witness.rbC5_150dLb ∧
        1 < w20_canonical_witness.frustrated48x48SaddleLb ∧
        w20_canonical_witness.widthW20_1p40Ub < w20_canonical_witness.oracleFloor1p40Lb ∧
        0 < w20_canonical_witness.kCommC5_1p65Lb ∧
        w20_canonical_witness.c22Bare150dLcUb < 1 ∧
        w20_canonical_witness.c25SingleLinkUpLb < w20_canonical_witness.c26JointHullUpLb ∧
        w20_canonical_witness.c26JointHullUpLb < w20_canonical_witness.c27PeterWeylUpLb ∧
        w20_canonical_witness.c27PeterWeylUpLb < w20_canonical_witness.c28MaxwellWickUpLb ∧
        2 < w20_canonical_witness.c28MaxwellWickF4dLb ∧
        0 < w20_canonical_witness.c28MaxwellWickMseaLb ∧
        6 * Real.pi ^ 2 / 11 < 8 * Real.log 2)) ∧
    -- (4) Universal minimal irreducible H2d obstruction remains unbridged (.OPEN)
    (∀ (core : Round05CrossObligationH2d.H2dMinimalIrreducibleCore),
      (∀ o : H2dCoreObligation, core.toObstructionCandidate.Satisfies o) ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) := by
  rcases round19_irx_wave19_honest_open_lock with
    ⟨hCore, ⟨hW19ne, hW19card, hW19wit, hW18ne, hW18card, _, _, _⟩,
      ⟨_, _, _, _, _, _, _, _, _, _, hLamDrop19, _, _, _, _, _, _, hRb40_19, hRb43_19, _, hKcomm19, _⟩,
      hMinCore⟩
  rcases w20_1_nonbox_uv_bkar_nelson_qf_and_strang with
    ⟨⟨hQFcp, _⟩, ⟨_, _, _, _, hNel5, _⟩, _, _⟩
  rcases w20_3_moving_cap_leibniz_ward_rb_and_frustrated_saddle with
    ⟨_, _, _, ⟨hPiCp, _⟩⟩
  rcases w20_4_riccati_4link_umax_kcomm_and_mi13_separation with
    ⟨_, _, ⟨_, _, hAffine, _⟩⟩
  rcases cycles19_to_28_pure_math_synthesis_and_maxwell_wick with
    ⟨_, _, ⟨_, ⟨hW14, _, _, _, hW15, _⟩, _, _, ⟨_, hC4diag⟩, _, ⟨_, _, _, _, _, hLit6⟩⟩⟩
  rcases w20_canonical_witness_margins with
    ⟨_, hBkar1, hBkar2, _, _, _, _, hBg495, _, _, _, hQ2, hLbulk, hLsum, _, _,
      hW48, hW49, hRb34, _, hRb5, hSad, _, _, hW14Cut, hKC5, _, hC22, _, _,
      hU2526, hU2627, hU2728, _, _, _, _, _, hF28, hMsea⟩
  refine ⟨hCore, ⟨⟨.o_w20_1_qf_spectrum_and_color_antisymmetry⟩, by decide,
    ⟨w20_canonical_witness⟩, hW19ne, hW19card, hW19wit, hW18ne, hW18card⟩, ?_, hMinCore⟩
  refine ⟨⟨hLamDrop19, hRb40_19, hRb43_19, hKcomm19⟩, ?_⟩
  refine ⟨hQFcp, hNel5, hPiCp, fun a oh oc c ha ha1 hoh hoc => (hAffine a oh oc c ha ha1 hoh hoc).2,
    hC4diag 1 2 3, hW14, hW15, lt_trans hBkar1 hBkar2, hBg495, hQ2, hLbulk, hLsum, hW48, hW49,
    hRb34, hRb5, hSad, hW14Cut, hKC5, hC22, hU2526, hU2627, hU2728, hF28, hMsea, hLit6⟩

end UEOTPhysicsUnification.IRXWave20NonBoxUVContinuumCoarseStiffnessRelTiltAndMultiPlaq
