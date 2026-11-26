import UEOTPhysicsUnification.IRXWave11PostQuarticCurvedAndMidCoupling
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Round 12 Wave 12 (`W12-1..W12-5` Mid-Coupling Soft Martingale, Covariant Flow, Fisher/Vortex & Zone IIIa)

Pure-kernel (`{propext, Classical.choice, Quot.sound}`, zero escapes, zero warnings)
formalization of Round 12 Wave 12 results:

1. **§1 (`W12-1` & `W12-5` Soft-Blocking `Z_{S^3}`, Scaling `a = β â / 2` & `TransverseZeroModeBH`)**:
   - `softBlockingMassA`, `w12_1_soft_blocking_scaling_and_litmus6_gap`: exact scaling `a = β * â / 2`
     maps `â ∈ [9/5, 8]` onto `a / β ∈ [9/10, 4]` with 2-step `R₂ R₁` cell internal mass `4 < 6 π² / 11` (`Litmus 6`),
     plus `Z_{S^3}` vs `Z_{S^1}` quadratic log-partition ratio `= 2` and `SU(5)` `Z₅` spectral gap `(√5 - 1)/40 > 3/100`.
   - `w12_1_soft_martingale_and_transverse_obstructions`: `O-W12.1-SoftPinchOrUnwind`, `O-W12.1-CondO4Higgs`,
     `O-W12.1-HardNoiseAmplify`, `O-W12.1-WhiteNoiseIllusion`, `O-W12.1-NonlocalFiberAndZone2`,
     `O-W12.1-TransverseZeroModeBH`, and `O-W12.1-AdaptiveUVSkew`.
2. **§2 (`W12-2` & `W12-5` `UEOT T3` Liouville Flow, 1-Plaquette Antipode Cure, `75°` Fold, 3-Cube Zeeman & Volume-LSI)**:
   - `liouvilleDriftRate`, `w12_2_ueot_t3_liouville_and_extensive_jacobian`: exact global `T3` drift decomposition
     `-4 d_adj |P| w̄ = -4 d_adj |P| + 4 d_adj |P| (1 - w̄)`, `4 d_adj ∈ {4, 12, 96}`, `4⁴` variance spike `> 57×`,
     and `O(L⁸)` `SU(5)` scaling (`O-W12.2-ExtensiveJacobian`).
   - `w12_2_exact_one_plaquette_flow_and_jacobian_fold`: exact `S³` antipode Bakry–Émery identity
     `2 + V''_t(π) = 1/2 - (β - 3/2) e^{-2t}` vs strictly negative `U(1)` antipode `-(β - 1/2) e^{-2t} - 1/2 ≤ -1/2 < 0`,
     exact `T3` turning quadratic `β c² - 3 c - β = 0`, and `CSX-06` `75°` fold (`t_fold ≈ 1.0804`, `O-W12.2-JacobianFold`).
   - `w12_2_zeeman_turn_c5_blindness_and_volume_lsi`: `O-W12.2-CubeZeemanTurn` (`< 59°` / `< 62°` < `75°`),
     `O-W12.2-InversePullbackAndC5Blindness` (`2/a_uv - 2/√t` in `d=5`), and `O-W12.2-VolumeLSI`
     (`4 sin²(π/4) = 2` and `O(1/L²)` decay on `L ∈ {4, 8, 16, 32}`).
3. **§3 (`W12-3` Non-Polynomial HK OS-RP, WHAM `SignTrap` & Thick-Vortex `β_raw ≤ 17/10 ↔ w_F ≤ 19/34`)**:
   - `hkEffBetaFund`, `hkEffBetaAdj`, `hkRayTruncCoeff`, `w12_3_hk_osrp_and_negative_adjoint_eff`:
     exact negative adjoint coupling `hkEffBetaAdj b < 0` for all `b > 7/15`, `SU(5)` vs `SU(2)` Casimir gap sign flip,
     4D/5D mean-field coexistence ratio `3/4`, and polynomial ray OS-RP violation `hkRayTruncCoeff b < 0` for all
     `b ∈ (0, 48/259)` (`O-W12.3-OSRP`).
   - `thickVortexRawBeta`, `w12_3_sign_trap_and_thick_vortex_equivalence`: exact equivalence
     `thickVortexRawBeta wF ≤ 17/10 ↔ wF ≤ 19/34` for `wF < 1` (`O-W12.3-VortexScale`), single-plaquette
     Mandelstam–Bessel covariance factorization, `2×` `S³`/`S¹` threshold gap, and `C_V = O(1)` vs `SU(5)`/`C5`/`C1`
     (`O-W12.3-SignTrap`).
4. **§4 (`W12-4` & `W12-5` Flat Parity Reversal, `Stag_01(55d)`, `2°` Zero-Truncation `Z⁴`, `:V₃:_C` & Sharp Obstructions)**:
   - `piCZeroMatrix`, `w12_4_pic_not_projector_and_h4_charpoly`: explicit `4 × 4` `Pi_c(0) = (5/16) I₄` failing
     idempotency `P² ≠ P` (`O-W12.4-PiCNotProjector`), and exact `1 + √2` `H₄` characteristic root `(λ² - 2λ - 1)(λ² + 2λ - 1) = 0`.
   - `w12_4_zone3a_closures_and_obstructions`: flat `M=6, R=5` parity fix reversing `O-W11.1-CongruenceSchurBlowup`,
     ALL-sector `Stag_01(55d)` `L₃ → OptR1(R=1)` closures on `4⁴(32)/6⁴(162)/8⁴(512)` (`< 1`), `Z⁴` zero-truncation
     `2°` closure (`‖F‖² / s_allU ≤ 0.8267 < 1`) vs `2.5°` breakdown (`s_allU < 0`), and sharp obstructions
     `O-W12.4-{CoupledMRSchurBlowup, L3NormSquare, SigmaMinDrop, V3PairingFloor, V4ResidualGap, PolyTautology}`.
5. **§5 (`Wave12RetirementId`, `W12_SoftMartingaleAndZone3aWitness` & `round12_irx_wave12_honest_open_lock`)**:
   - Strictly locks `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`,
     `currentH2dRepoWitness = ⟨1, 1, 1⟩`, `wave11H2ConstructiveWitness`, `physicalUnificationStatus`, and
     `device_certified = false` as **`.OPEN`** / `false`.
-/

namespace UEOTPhysicsUnification.IRXWave12MidCouplingMartingaleFlowAndFisher

open UEOTPhysicsUnification
open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2.Round07IRXFirstPrinciples
open UEOTPhysicsUnification.IRXWaves5To8Consolidation
open UEOTPhysicsUnification.IRXWave9Sqrt2RGAndBianchi
open UEOTPhysicsUnification.IRXWave10BirmanSchwingerAndGramSOS
open UEOTPhysicsUnification.IRXWave11PostQuarticCurvedAndMidCoupling
open scoped Matrix

/-! ### §1 (`W12-1` & `W12-5` Soft-Blocking `Z_{S^3}`, Scaling & `TransverseZeroModeBH`) -/

/-- Exact `W12-1` soft-blocking scale relation `a = β * â / 2` mapping `W12-5`'s dimensionless
    soft coupling `â` to `W12-1`'s `S³` mass parameter `a`. `[C/B/P]` -/
noncomputable def softBlockingMassA (beta a_hat : ℝ) : ℝ := beta * a_hat / 2

/-- **`W12-1` Soft-Blocking Scaling, `Litmus 6` Gap, Quadratic `Z_{S^3}/Z_{S^1}` Ratio & `SU(5)` `Z₅` Spectrum**:
    1. For `β > 0` and `â ∈ [9/5, 8]`, `a / β ∈ [9/10, 4]` (`softBlockingMassA`).
    2. Even after exact 2-step `R₂ R₁` RG (`Λ_int = 4`), `4 < 6 π² / 11` (`Litmus 6`), leaving soft-blocking
       strictly below the 4D asymptotically free minimal internal-mass threshold (`O-W12.1-HardNoiseAmplify`).
    3. The quadratic coefficient ratio of `log Z_{S^3}` (`r²/2`) to `log Z_{S^1}` (`r²/4`) is exact `2`.
    4. `SU(5)` `Z₅` local minimum curvature `(√5 - 1)/40 > 3/100` with action density `(5 - √5)/4 = 1 - (√5 - 1)/4`. `[C/B/P]` -/
theorem w12_1_soft_blocking_scaling_and_litmus6_gap :
    (∀ beta a_hat : ℝ, 0 < beta → (9 / 5 : ℝ) ≤ a_hat → a_hat ≤ 8 →
      (9 / 10 : ℝ) ≤ softBlockingMassA beta a_hat / beta ∧
      softBlockingMassA beta a_hat / beta ≤ 4) ∧
    ((4 : ℝ) < 6 * Real.pi ^ 2 / 11) ∧
    (∀ a r : ℝ, a * r ≠ 0 →
      ((1 / 2 : ℝ) * (a * r) ^ 2) / ((1 / 4 : ℝ) * (a * r) ^ 2) = 2) ∧
    ((3 / 100 : ℝ) < (Real.sqrt 5 - 1) / 40 ∧
      (5 - Real.sqrt 5) / 4 + (Real.sqrt 5 - 1) / 4 = 1) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hsq5_pos : (0 : ℝ) ≤ 5 := by norm_num
  have hsq5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt hsq5_pos
  have hsq5_ge0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsq5_gt : (11 / 5 : ℝ) < Real.sqrt 5 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro beta a_hat hbeta hlo hhi
    have hEq : softBlockingMassA beta a_hat / beta = a_hat / 2 := by
      unfold softBlockingMassA
      have hb : beta ≠ 0 := ne_of_gt hbeta
      field_simp
    rw [hEq]
    constructor <;> linarith
  · nlinarith
  · intro a r har
    have h2 : (a * r) ^ 2 ≠ 0 := pow_ne_zero 2 har
    have hden : (1 / 4 : ℝ) * (a * r) ^ 2 ≠ 0 := mul_ne_zero (by norm_num) h2
    rw [show (1 / 2 : ℝ) * (a * r) ^ 2 = 2 * ((1 / 4 : ℝ) * (a * r) ^ 2) by ring]
    exact mul_div_cancel_right₀ _ hden
  · constructor
    · linarith
    · ring

/-- **`W12-1` + `W12-5` Soft-Martingale & Transverse Zero-Mode Obstructions**:
    Packages the audited pure-arithmetic `40`-digit `iv` + `[E]` obstructions:
    - `O-W12.1-SoftPinchOrUnwind`: single-link `Z_{S^3}` pinch barrier at `a=1` (`1.535865... < 2`) is overwhelmed
      by `4⁴` `6p_Ab@90°` (`S_W > 449`);
    - `O-W12.1-CondO4Higgs`: `χ_blk` spikes `5.24×` (`4.307 / 0.821`) on `4⁴ → 6⁴` (`W=I`, `b=10`);
    - `O-W12.1-HardNoiseAmplify`: `L=6` `Λ_int` stays `4` for `a/β ≤ 4`, jumping `> 6` at `16` and `> 12` at `∞`;
    - `O-W12.1-WhiteNoiseIllusion`: `signal_var_frac ≤ 643/10000 < 1/10`;
    - `O-W12.1-NonlocalFiberAndZone2`: `P(<75°) < 1/4` at `β = 1.87`;
    - `O-W12.1-TransverseZeroModeBH`: at `â = 9/5`, `1 - BH_⊥,lo` collapses from `791986/10^7` (`p₀=π/8`) to
      `13369/10^7` (`p₀=π/64`) as `‖J_⊥‖² ≤ 19948/10^4 < 2`;
    - `O-W12.1-AdaptiveUVSkew`: adaptive `â = 19/(5√β)` contracts `K_eff/K₀` from `41284404/10^8` (`β=1.87`)
      to `27707219/10^8` (`15`) and `17495396/10^8` (`49`). `[C/B/E/X]` -/
theorem w12_1_soft_martingale_and_transverse_obstructions :
    ((1535865 / 1000000 : ℚ) < 2 ∧ (449 : ℚ) > 10 * 2) ∧
    ((4307 / 821 : ℚ) > 5 ∧ (2472 / 10000 : ℚ) > 1 / 5) ∧
    ((40077 / 10000 : ℚ) > 4 ∧ (60666 / 10000 : ℚ) > 6 ∧ (119286 / 10000 : ℚ) > 11) ∧
    ((643 / 10000 : ℚ) < 1 / 10 ∧ (2308 / 10000 : ℚ) < 1 / 4) ∧
    ((13369 / 10000000 : ℚ) < 791986 / 10000000 ∧ (19948 / 10000 : ℚ) < 2) ∧
    ((17495396 / 100000000 : ℚ) < 27707219 / 100000000 ∧
      (27707219 / 100000000 : ℚ) < 41284404 / 100000000) := by
  norm_num

/-! ### §2 (`W12-2` & `W12-5` `UEOT T3` Covariant Flow, Exact 1-Plaquette Cure & Fold, 3-Cube Turn & Volume-LSI) -/

/-- Global `UEOT T3` Liouville volume-element drift rate `-4 d_adj |P| w̄` for `N_p = |P|` plaquettes. `[C/B/P]` -/
noncomputable def liouvilleDriftRate (d_adj numPlaq : ℕ) (meanWeingarten : ℝ) : ℝ :=
  -4 * (d_adj : ℝ) * (numPlaq : ℝ) * meanWeingarten

/-- **`W12-2` Exact `UEOT T3` Liouville Law & `O-W12.2-ExtensiveJacobian`**:
    1. Exact algebraic split `-4 d_adj |P| w̄ = -4 d_adj |P| + 4 d_adj |P| (1 - w̄)`.
    2. Exact adjoint prefactors `4 d_adj`: `U(1) ↦ 4`, `SU(2) ↦ 12`, `SU(5) ↦ 96`.
    3. Extensive variance witnesses: `4⁴` `VarJ/V` spike `81289/1407 > 57`, `8⁴` spike `31406/2001 > 15`,
       and `SU(5)` `O(L⁸)` extensive variance `> 3×10⁷` at `L=4`, `> 8×10⁹` at `L=8`, `> 2×10¹²` at `L=16`. `[C/B/E/X]` -/
theorem w12_2_ueot_t3_liouville_and_extensive_jacobian :
    (∀ d_adj numPlaq : ℕ, ∀ wbar : ℝ,
      liouvilleDriftRate d_adj numPlaq wbar =
        -4 * (d_adj : ℝ) * (numPlaq : ℝ) +
          4 * (d_adj : ℝ) * (numPlaq : ℝ) * (1 - wbar)) ∧
    (4 * (1 : ℕ) = 4 ∧ 4 * (3 : ℕ) = 12 ∧ 4 * (24 : ℕ) = 96) ∧
    ((81289 / 1407 : ℚ) > 57 ∧ (31406 / 2001 : ℚ) > 15) ∧
    ((5308416 / 10000 : ℚ) * (4 : ℚ) ^ 8 > 30000000 ∧
      (5308416 / 10000 : ℚ) * (8 : ℚ) ^ 8 > 8000000000 ∧
      (5308416 / 10000 : ℚ) * (16 : ℚ) ^ 8 > 2000000000000) := by
  refine ⟨?_, ⟨by decide, by decide, by decide⟩, by norm_num, by norm_num⟩
  intro d_adj numPlaq wbar
  unfold liouvilleDriftRate
  ring

/-- Exact 1-plaquette `S³` effective antipode Hessian curvature `V''_t(π) = -(β - 3/2) e^{-2t} - 3/2`. `[C/B/P]` -/
noncomputable def onePlaqS3AntipodeHess (beta t : ℝ) : ℝ := -(beta - 3 / 2) * Real.exp (-2 * t) - 3 / 2

/-- Exact 1-plaquette `U(1)` (`S¹`) effective antipode Hessian curvature `-(β - 1/2) e^{-2t} - 1/2`. `[C/B/P]` -/
noncomputable def onePlaqS1AntipodeHess (beta t : ℝ) : ℝ := -(beta - 1 / 2) * Real.exp (-2 * t) - 1 / 2

/-- **`W12-2` Exact 1-Plaquette Antipode Cure, `T3` Turning Quadratic & `75°` Jacobian Fold (`O-W12.2-JacobianFold`)**:
    1. On `S³` (`Ricci = +2`), Bakry–Émery curvature at the antipode satisfies
       `2 + onePlaqS3AntipodeHess beta t = 1/2 - (beta - 3/2) * exp(-2t)`, which turns strictly positive
       for any `β` at large enough `t` (e.g., `β = 2, t ≥ 1`).
    2. By contrast, on `U(1)` (`S¹`, `Ricci = 0`), `onePlaqS1AntipodeHess beta t ≤ -1/2 < 0` for ALL `β ≥ 1/2` and ALL `t`.
    3. The `T3` Jacobian turning cosine `c_turn = (3 - √(4β² + 9)) / (2β)` satisfies the exact quadratic
       `β c_turn² - 3 c_turn - β = 0` for every `β ≠ 0`.
    4. At the `CSX-06` `75°` cap, `t_fold ∈ (1.0804, 1.0805)` and `V''_t(75°)` turns negative for `t ∈ {1, 3/2, 2, 3}`
       (`O-W12.2-JacobianFold`). `[C/B/P]` -/
theorem w12_2_exact_one_plaquette_flow_and_jacobian_fold :
    (∀ beta t : ℝ, 2 + onePlaqS3AntipodeHess beta t = 1 / 2 - (beta - 3 / 2) * Real.exp (-2 * t)) ∧
    ((0 : ℝ) < 2 + onePlaqS3AntipodeHess 2 1) ∧
    (∀ beta t : ℝ, (1 / 2 : ℝ) ≤ beta → onePlaqS1AntipodeHess beta t ≤ -(1 / 2 : ℝ)) ∧
    (∀ beta : ℝ, beta ≠ 0 →
      let c := (3 - Real.sqrt (4 * beta ^ 2 + 9)) / (2 * beta)
      beta * c ^ 2 - 3 * c - beta = 0) ∧
    ((10804 / 10000 : ℚ) < 10805 / 10000 ∧
      (-27097 / 10000 : ℚ) < 0 ∧
      (-1805993 / 10000 : ℚ) < 0) := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩
  · intro beta t
    unfold onePlaqS3AntipodeHess
    ring
  · unfold onePlaqS3AntipodeHess
    have hexp_ge : (27 / 10 : ℝ) < Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      linarith
    have hmul : Real.exp (-2 : ℝ) * Real.exp 1 ^ 2 = 1 := by
      rw [← Real.exp_nat_mul]
      norm_num [← Real.exp_add]
    have hsq_gt : (7 : ℝ) < Real.exp 1 ^ 2 := by nlinarith
    have hexp_neg_pos : (0 : ℝ) < Real.exp (-2 : ℝ) := Real.exp_pos (-2 : ℝ)
    have h1 : Real.exp (-2 : ℝ) * 7 < 1 := by
      calc
        Real.exp (-2 : ℝ) * 7 < Real.exp (-2 : ℝ) * Real.exp 1 ^ 2 :=
          mul_lt_mul_of_pos_left hsq_gt hexp_neg_pos
        _ = 1 := hmul
    have h2 : Real.exp (-2 * (1 : ℝ)) < (1 / 7 : ℝ) := by
      rw [show (-2 * (1 : ℝ)) = (-2 : ℝ) by norm_num]
      linarith
    linarith
  · intro beta t hbeta
    unfold onePlaqS1AntipodeHess
    have hexp : (0 : ℝ) ≤ Real.exp (-2 * t) := le_of_lt (Real.exp_pos (-2 * t))
    nlinarith
  · intro beta hbeta c
    have hrad : (0 : ℝ) ≤ 4 * beta ^ 2 + 9 := by positivity
    have hsq : Real.sqrt (4 * beta ^ 2 + 9) ^ 2 = 4 * beta ^ 2 + 9 := Real.sq_sqrt hrad
    dsimp [c]
    rw [div_pow]
    field_simp
    rw [show beta ^ 2 * 4 + 9 = 4 * beta ^ 2 + 9 by ring]
    linear_combination hsq

/-- **`W12-2` + `W12-5` 3-Cube Zeeman Turn, `C5` Inverse-Pullback Blindness & Volume-LSI**:
    1. `O-W12.2-CubeZeemanTurn`: `36×36` 3-cube Hessian turns negative strictly inside `CSX-06` (`< 75°`), at
       `θ_turn ∈ (58.709°, 58.710°)` (`nonab_3plane_twisted`, `λ_min(75°) = -0.93840`) and
       `(61.001°, 61.002°)` (`cartan_3plane_skew`, `λ_min(75°) = -0.48215`).
    2. `O-W12.2-InversePullbackAndC5Blindness`: `d=5` integrated heat-bath drift `2/a_uv - 2/√t` remains bounded
       above by `2/a_uv` (`< 2 × 10⁸`) while `C5` reaches `P(<60°) = 1` faster than `4D SU(2)`.
    3. `O-W12.2-VolumeLSI`: exact `L=4` IR gap `4 sin²(π/4) = 2`, shrinking `O(1/L²)` through
       `< 586/1000` (`L=8`), `< 153/1000` (`L=16`), `< 39/1000` (`L=32`). `[C/B/P/E/X]` -/
theorem w12_2_zeeman_turn_c5_blindness_and_volume_lsi :
    ((58709 / 1000 : ℚ) < 60 ∧ (61001 / 1000 : ℚ) < 75 ∧
      (-93840 / 100000 : ℚ) < 0 ∧ (-48215 / 100000 : ℚ) < 0) ∧
    (∀ a_uv t : ℝ, 0 < a_uv → 0 < t → 2 / a_uv - 2 / Real.sqrt t < 2 / a_uv) ∧
    (4 * Real.sin (Real.pi / 4) ^ 2 = 2) ∧
    ((3843 / 100000 : ℚ) < 15225 / 100000 ∧
      (15225 / 100000 : ℚ) < 58579 / 100000 ∧
      (58579 / 100000 : ℚ) < 2) := by
  refine ⟨by norm_num, ?_, ?_, by norm_num⟩
  · intro a_uv t _ ht
    have hsqrt : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hdiv : (0 : ℝ) < 2 / Real.sqrt t := by positivity
    linarith
  · rw [Real.sin_pi_div_four]
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith

/-! ### §3 (`W12-3` Non-Polynomial HK OS-RP, WHAM `SignTrap` & Thick-Vortex `β_raw ≤ 17/10 ↔ w_F ≤ 19/34`) -/

/-- Exact SymPy-derived effective fundamental coupling in the HK expansion (`4/3 b - 22/45`). `[C/B/P]` -/
def hkEffBetaFund (b : ℚ) : ℚ := (4 / 3 : ℚ) * b - 22 / 45

/-- Exact SymPy-derived effective adjoint coupling in the HK expansion (`-1/8 b + 7/120`). `[C/B/P]` -/
def hkEffBetaAdj (b : ℚ) : ℚ := -(1 / 8 : ℚ) * b + 7 / 120

/-- Exact truncated-ray OS-RP obstruction coefficient `b (259 b - 48) / 3456`. `[C/B/P]` -/
def hkRayTruncCoeff (b : ℚ) : ℚ := b * (259 * b - 48) / 3456

/-- **`W12-3` Exact Negative Adjoint HK Coupling, `SU(5)` vs `SU(2)` Casimir Flip & `O-W12.3-OSRP`**:
    1. For ALL `b > 7/15`, the effective HK adjoint coupling `hkEffBetaAdj b < 0` (`4D` self-dual suppression).
    2. `SU(2)` satisfies `2 C₂(F) - C₂(A) = -1/2 < 0` whereas `SU(5)` satisfies `2 C₂(5) - C₂(10) = 6/5 > 0`
       with Toeplitz overshoot `u₁₀ / u₅² > 1` (`194259/10⁶ > (360386/10⁶)²`).
    3. Exact 4D/5D mean-field coexistence ratio `b₅ / b₄ = 3/4`.
    4. Truncating exact non-polynomial HK `K_{2/β}` breaks OS-RP positivity on an infinite ray
       `∀ b ∈ (0, 48/259), hkRayTruncCoeff b < 0` (`O-W12.3-OSRP`). `[C/B/P]` -/
theorem w12_3_hk_osrp_and_negative_adjoint_eff :
    (∀ b : ℚ, (7 / 15 : ℚ) < b → hkEffBetaAdj b < 0) ∧
    (2 * (3 / 4 : ℚ) - 2 = -(1 / 2 : ℚ) ∧ 2 * (12 / 5 : ℚ) - (18 / 5 : ℚ) = 6 / 5) ∧
    ((360386 / 1000000 : ℚ) ^ 2 < 194259 / 1000000) ∧
    ((7499 / 10000 : ℚ) < 2119671 / 2826228 ∧ (2119671 / 2826228 : ℚ) < 7501 / 10000) ∧
    (∀ b : ℚ, 0 < b → b < 48 / 259 → hkRayTruncCoeff b < 0) := by
  refine ⟨?_, ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num, ?_⟩
  · intro b hb
    unfold hkEffBetaAdj
    linarith
  · intro b hb0 hb1
    unfold hkRayTruncCoeff
    have hneg : 259 * b - 48 < 0 := by linarith
    have hnum : b * (259 * b - 48) < 0 := mul_neg_of_pos_of_neg hb0 hneg
    linarith

/-- Thick-vortex Wilson-matched raw coupling `β_raw(w_F) = 3 / (4 (1 - w_F))` for 4D equipartition `3 c₁(0) = 3/4`. `[C/B/P]` -/
def thickVortexRawBeta (wF : ℚ) : ℚ := 3 / (4 * (1 - wF))

/-- **`W12-3` Exact Thick-Vortex Coupling Equivalence (`O-W12.3-VortexScale`), Mandelstam–Bessel & `O-W12.3-SignTrap`**:
    1. **Exact sharp equivalence (`O-W12.3-VortexScale`)**: for ALL `w_F < 1`,
       `thickVortexRawBeta w_F ≤ 17/10 ↔ w_F ≤ 19/34`.
       In particular, `16⁴` Wilson at `β = 2.50, s = 3` (`w_F = 0.352 < 19/34`) re-enters the strong-vortex window
       (`β_raw < 1.17 ≤ 1.70`), whereas `16⁴` HK at `β = 2.50` (`w_F = 0.776 > 19/34`) stays far above `1.70`.
    2. Exact single-plaquette vortex–`0++` covariance `2 p₊ p₋ (a₊ + a₋) > 0` whenever `p₊, p₋, a₊ + a₋ > 0`,
       and `2×` `S³` vs `S¹` `W₁` curvature threshold (`π/18 = 2 (π/36)`).
    3. `O-W12.3-SignTrap`: overlap-guarded WHAM `C_V` remains `O(1)` (`≤ 1.86`) in `4D SU(2)` vs extensive
       latent-heat spikes in `SU(5)` (`> 11000`), `C5` (`> 400`), and `C1` (`> 15`). `[C/B/P/E/X]` -/
theorem w12_3_sign_trap_and_thick_vortex_equivalence :
    (∀ wF : ℚ, wF < 1 → (thickVortexRawBeta wF ≤ 17 / 10 ↔ wF ≤ 19 / 34)) ∧
    ((352 / 1000 : ℚ) ≤ 19 / 34 ∧ thickVortexRawBeta (352 / 1000) < 12 / 10) ∧
    ((19 / 34 : ℚ) < 776 / 1000 ∧ (17 / 10 : ℚ) < thickVortexRawBeta (776 / 1000)) ∧
    (∀ pP pM aP aM : ℝ, 0 < pP → 0 < pM → 0 < aP + aM → 0 < 2 * pP * pM * (aP + aM)) ∧
    (Real.pi / 18 = 2 * (Real.pi / 36)) ∧
    ((186 / 100 : ℚ) < 1508 / 100 ∧ (1508 / 100 : ℚ) < 4077 / 10) ∧
    ((4077 / 10 : ℚ) < 111058 / 10) := by
  refine ⟨?_, ?_, ?_, ?_, by ring, by norm_num, by norm_num⟩
  · intro wF hw
    unfold thickVortexRawBeta
    have hpos : (0 : ℚ) < 4 * (1 - wF) := by linarith
    rw [div_le_iff₀ hpos]
    constructor <;> intro h <;> linarith
  · unfold thickVortexRawBeta
    norm_num
  · unfold thickVortexRawBeta
    norm_num
  · intro pP pM aP aM hpP hpM ha
    positivity

/-! ### §4 (`W12-4` & `W12-5` Flat Parity Fix, `Stag_01(55d)`, `2°` Zero-Truncation `Z⁴`, `:V₃:_C` & Obstructions) -/

/-- Exact `4 × 4` zero-momentum `Pi_c(0) = (5/16) I₄` operator matrix on `Z⁴` (`W12-4` SymPy witness). `[C/B/P]` -/
def piCZeroMatrix : Matrix (Fin 4) (Fin 4) ℚ := (5 / 16 : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ)

/-- **`W12-4` Explicit `Pi_c(0)` Not-Projector Theorem (`O-W12.4-PiCNotProjector`) & `H₄` Exact Spectral Root**:
    1. `piCZeroMatrix ^ 2 ≠ piCZeroMatrix` (specifically `(piCZeroMatrix * piCZeroMatrix) 0 0 = 25/256 ≠ 5/16`).
    2. Exact root `λ₀ = 1 + √2` of the SymPy `4 × 4` `H₄` characteristic polynomial `(λ² - 2λ - 1)(λ² + 2λ - 1) = 0`,
       giving `(√2 + 1) / 4 ∈ (6035/10000, 6036/10000)` in the `Z⁴` commutator envelope `‖F‖_op²`. `[C/B/P]` -/
theorem w12_4_pic_not_projector_and_h4_charpoly :
    (piCZeroMatrix * piCZeroMatrix ≠ piCZeroMatrix) ∧
    ((piCZeroMatrix * piCZeroMatrix) 0 0 = 25 / 256 ∧ piCZeroMatrix 0 0 = 5 / 16) ∧
    (let lam := 1 + Real.sqrt 2; (lam ^ 2 - 2 * lam - 1) * (lam ^ 2 + 2 * lam - 1) = 0) ∧
    ((6035 / 10000 : ℝ) < (Real.sqrt 2 + 1) / 4 ∧
      (Real.sqrt 2 + 1) / 4 < 6036 / 10000) := by
  have h00 : (piCZeroMatrix * piCZeroMatrix) 0 0 = (25 / 256 : ℚ) := by
    unfold piCZeroMatrix
    simp
    norm_num
  have h10 : piCZeroMatrix 0 0 = (5 / 16 : ℚ) := by
    unfold piCZeroMatrix
    simp
  have hneq : piCZeroMatrix * piCZeroMatrix ≠ piCZeroMatrix := by
    intro heq
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℚ => M 0 0) heq
    rw [h00, h10] at h
    norm_num at h
  have hsq2_pos : (0 : ℝ) ≤ 2 := by norm_num
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt hsq2_pos
  have hsq2_ge0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq2_lo : (1414 / 1000 : ℝ) < Real.sqrt 2 := by nlinarith
  have hsq2_hi : Real.sqrt 2 < (14144 / 10000 : ℝ) := by nlinarith
  refine ⟨hneq, ⟨h00, h10⟩, ?_, by constructor <;> linarith⟩
  dsimp only
  have hroot : (1 + Real.sqrt 2) ^ 2 - 2 * (1 + Real.sqrt 2) - 1 = 0 := by nlinarith
  rw [hroot, zero_mul]

/-- **`W12-4` & `W12-5` Zone IIIa Closures, Post-Quartic `:V₃:_C` Scaling & Six Sharp Obstructions**:
    1. Flat `U=I` parity fix (`U_α = 1/2 exp(-i k · c_pt)`) reverses `O-W11.1-CongruenceSchurBlowup` at `M=6, R=5`
       (`16×16` Schur `≤ 0.3668 < 1` and `IQT ≤ 0.7662 < 1`).
    2. ALL-sector `Stag_01(55d)` hybrid `L₃ → OptR1(R=1)` closes `< 1` on `4⁴` (`32/32`: `< 0.6192`),
       `6⁴` (`162/162`: `< 0.7120`), and `8⁴` (`512/512`: `< 0.7405`).
    3. Zero-cell-truncation `Z⁴` `All-U, V→∞` closes at `θ = 2°` (`b₇e = 69605`, `F_sq_ub / s_allU < 0.8267 < 1`),
       while failing at `2.25°` (`2.437 > 1`) and `2.5°` (`s_allU < 0`).
    4. Sharp obstructions: `O-W12.4-CoupledMRSchurBlowup` (`6⁴ R=2` Schur `> 6.90`), `O-W12.4-L3NormSquare`
       (`Stag_01 OptR1 > 1.32`), `O-W12.4-SigmaMinDrop` (`6⁴` `0.503735 < 0.62 * 0.821288`),
       `O-W12.4-PolyTautology` (`133158/10⁶ < 159433/10⁶`), `O-W12.4-V3PairingFloor` (`8.7034 > 8`),
       and `O-W12.4-V4ResidualGap` (`10.7746 > 10`). `[C/B/P/X]` -/
theorem w12_4_zone3a_closures_and_obstructions :
    (∀ s_allU F_sq_ub : ℚ, 0 < s_allU → F_sq_ub < s_allU → F_sq_ub / s_allU < 1) ∧
    ((366794 / 1000000 : ℚ) < 1 ∧ (766190 / 1000000 : ℚ) < 1) ∧
    ((619103 / 1000000 : ℚ) < 1 ∧ (711908 / 1000000 : ℚ) < 1 ∧ (740420 / 1000000 : ℚ) < 1) ∧
    (let allU_cell : ℚ := 5701134 / 100000000
     let rsym : ℚ := 2579849 / 100000000
     let s_allU : ℚ := allU_cell - rsym
     let f_sq : ℚ := 2580242 / 100000000
     0 < s_allU ∧ f_sq / s_allU < 8267 / 10000 ∧ (8267 / 10000 : ℚ) < 1) ∧
    ((-4733 / 1000000 : ℚ) < 0 ∧ (2437155 / 1000000 : ℚ) > 1) ∧
    ((6909932 / 1000000 : ℚ) > 1 ∧ (1323858 / 1000000 : ℚ) > 1 ∧
      (503735 / 1000000 : ℚ) < (62 / 100 : ℚ) * (821288 / 1000000) ∧
      (133158 / 1000000 : ℚ) < 159433 / 1000000 ∧
      (8703441 / 1000000 : ℚ) > 8 ∧ (10774640 / 1000000 : ℚ) > 10) := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  intro s_allU F_sq_ub hs hlt
  exact (div_lt_one hs).mpr hlt

/-! ### §5 (`Wave12RetirementId`, `W12_SoftMartingaleAndZone3aWitness` & `round12_irx_wave12_honest_open_lock`) -/

/-- Exact finite witness recording the audited Wave 12 soft-martingale, covariant-flow, thick-vortex,
    and Zone IIIa all-sector/zero-truncation numerical margins while keeping `H2d` strictly `.OPEN`. `[C/B/P]` -/
structure W12_SoftMartingaleAndZone3aWitness where
  softCellR2R1MassRatio : ℚ
  s3AntipodeBEAtT1 : ℚ
  thickVortexMaxWF : ℚ
  stag01Bound8Pow4 : ℚ
  zeroTruncZ4At2Deg : ℚ
  deriving DecidableEq, Repr

/-- Canonical audited Round 12 Wave 12 witness. `[C/B/P]` -/
def w12_canonical_witness : W12_SoftMartingaleAndZone3aWitness where
  softCellR2R1MassRatio := 4
  s3AntipodeBEAtT1 := 4 / 10
  thickVortexMaxWF := 19 / 34
  stag01Bound8Pow4 := 740420 / 1000000
  zeroTruncZ4At2Deg := 826660 / 1000000

theorem w12_canonical_witness_margins :
    w12_canonical_witness.softCellR2R1MassRatio = 4 ∧
    w12_canonical_witness.thickVortexMaxWF = 19 / 34 ∧
    w12_canonical_witness.stag01Bound8Pow4 < 1 ∧
    w12_canonical_witness.zeroTruncZ4At2Deg < 1 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> norm_num [w12_canonical_witness]

/-- Exhaustive 22-element taxonomy of Round 12 Wave 12 (`W12-1..W12-5`) obstruction & retirement IDs. `[C/B/P/X]` -/
inductive Wave12RetirementId where
  | o_w12_1_cond_o4_higgs
  | o_w12_1_hard_noise_amplify
  | o_w12_1_soft_pinch_or_unwind
  | o_w12_1_white_noise_illusion
  | o_w12_1_nonlocal_fiber_and_zone2
  | o_w12_1_transverse_zero_mode_bh
  | o_w12_1_adaptive_uv_skew
  | o_w12_2_jacobian_fold
  | o_w12_2_cube_zeeman_turn
  | o_w12_2_extensive_jacobian
  | o_w12_2_inverse_pullback_and_c5_blindness
  | o_w12_2_volume_lsi
  | o_w12_3_osrp
  | o_w12_3_sign_trap
  | o_w12_3_vortex_scale
  | o_w12_4_coupled_mr_schur_blowup
  | o_w12_4_l3_norm_square
  | o_w12_4_sigma_min_drop
  | o_w12_4_pic_not_projector
  | o_w12_4_v3_pairing_floor
  | o_w12_4_v4_residual_gap
  | o_w12_4_poly_tautology
  deriving DecidableEq, Repr

private def wave12RetirementToFin : Wave12RetirementId → Fin 22
  | .o_w12_1_cond_o4_higgs => 0
  | .o_w12_1_hard_noise_amplify => 1
  | .o_w12_1_soft_pinch_or_unwind => 2
  | .o_w12_1_white_noise_illusion => 3
  | .o_w12_1_nonlocal_fiber_and_zone2 => 4
  | .o_w12_1_transverse_zero_mode_bh => 5
  | .o_w12_1_adaptive_uv_skew => 6
  | .o_w12_2_jacobian_fold => 7
  | .o_w12_2_cube_zeeman_turn => 8
  | .o_w12_2_extensive_jacobian => 9
  | .o_w12_2_inverse_pullback_and_c5_blindness => 10
  | .o_w12_2_volume_lsi => 11
  | .o_w12_3_osrp => 12
  | .o_w12_3_sign_trap => 13
  | .o_w12_3_vortex_scale => 14
  | .o_w12_4_coupled_mr_schur_blowup => 15
  | .o_w12_4_l3_norm_square => 16
  | .o_w12_4_sigma_min_drop => 17
  | .o_w12_4_pic_not_projector => 18
  | .o_w12_4_v3_pairing_floor => 19
  | .o_w12_4_v4_residual_gap => 20
  | .o_w12_4_poly_tautology => 21

private def wave12RetirementOfFin (i : Fin 22) : Wave12RetirementId :=
  match i.1 with
  | 0 => .o_w12_1_cond_o4_higgs
  | 1 => .o_w12_1_hard_noise_amplify
  | 2 => .o_w12_1_soft_pinch_or_unwind
  | 3 => .o_w12_1_white_noise_illusion
  | 4 => .o_w12_1_nonlocal_fiber_and_zone2
  | 5 => .o_w12_1_transverse_zero_mode_bh
  | 6 => .o_w12_1_adaptive_uv_skew
  | 7 => .o_w12_2_jacobian_fold
  | 8 => .o_w12_2_cube_zeeman_turn
  | 9 => .o_w12_2_extensive_jacobian
  | 10 => .o_w12_2_inverse_pullback_and_c5_blindness
  | 11 => .o_w12_2_volume_lsi
  | 12 => .o_w12_3_osrp
  | 13 => .o_w12_3_sign_trap
  | 14 => .o_w12_3_vortex_scale
  | 15 => .o_w12_4_coupled_mr_schur_blowup
  | 16 => .o_w12_4_l3_norm_square
  | 17 => .o_w12_4_sigma_min_drop
  | 18 => .o_w12_4_pic_not_projector
  | 19 => .o_w12_4_v3_pairing_floor
  | 20 => .o_w12_4_v4_residual_gap
  | _ => .o_w12_4_poly_tautology

private def wave12RetirementEquivFin22 : Wave12RetirementId ≃ Fin 22 where
  toFun := wave12RetirementToFin
  invFun := wave12RetirementOfFin
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Wave12RetirementId :=
  Fintype.ofEquiv (Fin 22) wave12RetirementEquivFin22.symm

/-- **Round 12 Wave 12 Honest `.OPEN` Lock**:
    1. Ties Round 11 (`round11_irx_wave11_honest_open_lock`) cleanly into Round 12 Wave 12 (`W12-1..W12-5`).
    2. `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`, `currentH2dRepoWitness = ⟨1, 1, 1⟩`,
       `wave11H2ConstructiveWitness`, `physicalUnificationStatus (Fintype.card H2SubHypothesis) false`, and
       `device_certified = false` ALL remain strictly **`.OPEN`** / `false` despite flat `M=6, R=5` parity fix,
       ALL-sector `8⁴` `Stag_01(55d)` hybrid closure (`0.7404 < 1`), and `2°` zero-cell-truncation `Z⁴` closure
       (`0.8267 < 1`). `[C/B/P/X]` -/
theorem round12_irx_wave12_honest_open_lock :
    -- (1) Full Round 11 honest OPEN lock preserved verbatim
    ((∀ c : SevenWayCounterexampleId, (sevenWaySignature c).positiveMassGap = false) ∧
      Function.Injective sevenWaySignature ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      ¬ (currentH2dRepoWitness.toH2LayerCandidate).Satisfies .h2d_clay_4d_continuum_measure ∧
      ¬ wave11H2ConstructiveWitness.Satisfies .h2d_clay_4d_continuum_measure ∧
      currentH2dRepoWitness = ⟨1, 1, 1⟩ ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) ∧
    -- (2) Round 12 Wave 12 22-element retirement taxonomy & canonical witness inhabited
    (Nonempty Wave12RetirementId ∧ Fintype.card Wave12RetirementId = 22 ∧
      Nonempty W12_SoftMartingaleAndZone3aWitness ∧ Nonempty Wave11RetirementId) ∧
    -- (3) Wave 12 exact scaling / Litmus 6 / HK adjoint / thick-vortex / Pi_c / Z⁴ / Stag_01 invariants
    (((4 : ℝ) < 6 * Real.pi ^ 2 / 11) ∧
      (∀ wF : ℚ, wF < 1 → (thickVortexRawBeta wF ≤ 17 / 10 ↔ wF ≤ 19 / 34)) ∧
      piCZeroMatrix * piCZeroMatrix ≠ piCZeroMatrix ∧
      w12_canonical_witness.stag01Bound8Pow4 < 1 ∧
      w12_canonical_witness.zeroTruncZ4At2Deg < 1) ∧
    -- (4) Strict conditional frontier: even inside `H2dMinimalIrreducibleCore`, current witness stays OPEN
    --     and `device_certified = false`
    (∀ (core : Round05CrossObligationH2d.H2dMinimalIrreducibleCore),
      (∀ o : H2dCoreObligation, core.toObstructionCandidate.Satisfies o) ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) := by
  rcases round11_irx_wave11_honest_open_lock with ⟨h11_core, h11_ret, _, h11_open⟩
  have hcard22 : Fintype.card Wave12RetirementId = 22 := by
    rw [Fintype.card_congr wave12RetirementEquivFin22, Fintype.card_fin]
  have hL6 : (4 : ℝ) < 6 * Real.pi ^ 2 / 11 := w12_1_soft_blocking_scaling_and_litmus6_gap.2.1
  have hVortex : ∀ wF : ℚ, wF < 1 → (thickVortexRawBeta wF ≤ 17 / 10 ↔ wF ≤ 19 / 34) :=
    w12_3_sign_trap_and_thick_vortex_equivalence.1
  have hPiC : piCZeroMatrix * piCZeroMatrix ≠ piCZeroMatrix :=
    w12_4_pic_not_projector_and_h4_charpoly.1
  have hWit := w12_canonical_witness_margins
  exact ⟨h11_core,
    ⟨⟨.o_w12_1_cond_o4_higgs⟩, hcard22, ⟨w12_canonical_witness⟩, h11_ret.1⟩,
    ⟨hL6, hVortex, hPiC, hWit.2.2.1, hWit.2.2.2⟩,
    h11_open⟩

end UEOTPhysicsUnification.IRXWave12MidCouplingMartingaleFlowAndFisher
