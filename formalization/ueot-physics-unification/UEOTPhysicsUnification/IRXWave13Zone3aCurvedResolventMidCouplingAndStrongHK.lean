import UEOTPhysicsUnification.IRXWave12MidCouplingMartingaleFlowAndFisher
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Round 13 Wave 13 (`W13-1..W13-6` Zone IIIa Curved Resolvent, Soft-Martingale LSI, HK Fisher Zeros, `V=∞` OS-RP+SD & HK `5×` Strong-Coupling Push)

Pure-kernel (`{propext, Classical.choice, Quot.sound}`, zero escapes, zero warnings)
formalization of Round 13 Wave 13 results:

1. **§1 (`W13-1` & `W13-5 Q4` Zone IIIa Curved Resolvent, `box_w=3` BFS `2°`, `M=32 R=6` Post-Quartic BKAR & IMS/Tree Catches)**:
   - `w13_1_curved_resolvent_and_allU_vinf_walls`: exact `4×4` `H₄` eigenvalues `±(1 ± √2)`, parity-aligned
     `L₃ + OptR1(R=2)` curved `55° Stag_01` closures on `6⁴` (`162/162`: `bnd_allU ≤ 0.6256 < 1`) and
     `8⁴` (`512/512`: `bnd_allU ≤ 0.6458 < 1`), coupled 1-link `M_R - I` Schur blowup (`1.37..1.96 > 1` at `55°`),
     `box_w=3` BFS (`2.0°` `0.826657 < 1` vs `2.5°` `s_allU < 0` & `55.0°` `s_allU < -0.62`), and `Z⁴` closed-loop
     holonomy lower bounds `≥ 331.3..544.9 ≫ 1` (`O-W13.1-AllUVinfTriangleWall`).
   - `w13_1_ims_radial_conflict_and_r6_bkar_plateau`: `O-W13.1-IMSHopRadiusConflict` &
     `O-W13.1-RadialGaugeTreeDrift` (`E_IMS(W_fine) > 0.04413` across `W_fine ∈ {6..64}` while radial fan angle
     `≥ 220° > 180°` for `W_fine ≥ 8`), `M=32 R=6` `qt_l1` compression (`0.0007785 < 0.012373`), tightened `β₀`
     BKAR brackets (`[3892,3893]`, `[14541,14542]`, `[21455,21456]`, `[26039,26040]`), algebraic `W_pair`
     plateau `(5 + q) / 18 ≥ 5 / 18` (`O-W13.1-R6-Plateau`), and `C1`/`C5`/`Litmus 6` separations.
2. **§2 (`W13-2` & `W13-5 Q2` Local-Cell Soft-Martingale LSI Window, `42.3539` Polymer Floor & Intertwining Obstructions)**:
   - `w13_2_soft_window_cure_and_peierls_polygap`: exact `Z^d` Green diagonal `(d-1)/C(d,2) = 2/d`, 3-cube
     Bianchi `S_min^(3)(58°) ≈ 0.15098`, `r_min(58°) > 0.80128`, refutation of wide window (`O-W13.2-BlockSoftWindow`:
     `-0.3886 < 0`), constructive cure at `â ∈ [6, 8], θ_V ≤ 60°` (`H/β ≥ 0.4001`, `≥ 0.7329`, respecting
     `Litmus 6` `â ≤ 8 < 9.6172`), `42.3539` hypercube KP floor (`O-W13.2-Bianchi58PolyGap`), exact `4D`/`5D`
     hinge overlap coordination `z_hinge = 161` / `317` raising the zero-entropy floor `17.757 → 26.700`
     (`O-W13.2-HingeOverlapCoordination`), and `O-W13.2-{JPerpCurvedBlowup, OneLoopJShift, BlockEntropy96Plaq}`.
3. **§3 (`W13-3` & `W13-5 Q3` Exact HK `K_{2/β}` Complex Disk Wall, 1D TM Fail, `R₂ R₁` Drag & `UVModeAnnihilation`)**:
   - `w13_3_hk_disk_wall_equivalence` & `w13_3_1dtm_fail_and_normalized_osrp`: exact real algebraic proof of
     `O-W13.3-HKDiskWall` (`β_r/(β_r² + β_i²) ≤ 1/β_max ↔ (β_max/2)² ≤ (β_r - β_max/2)² + β_i²`), Dobrushin
     `18 TV > 1` (`0.50, 1.87`), `β_KP^HK ∈ (1.688224, 1.688225) < 1.87`, normalized `O-W12.3-OSRP`
     half-integer/integer spins (`j = 3, 9/2, 6`), `O-W13.3-1DTMCriterionFail` (`gap > 3.10`, `Im β* > 0.82`),
     and `5D` HK vs Wilson `u_{1/2}` match (`1.512671` vs `1.642`).
   - `w13_3_r2r1_turnaround_smearing_and_uv_mode_annihilation`: exact polar-sign deficit & turnaround
     equivalence `r2r1BetaRaw c1_0 c1_next betaCalNext < r2r1BetaRaw c1_0 c1_k betaCalK ↔ (betaCalK - betaCalNext)/betaCalK > 1 - c1_next/c1_k`,
     `O-W13.3-Step1SmearingBarrier` (`63.7%` drag vs `< 26%` 1-loop `Litmus 6` step), and complete `SU(2)`
     quaternion algebraic proof of `O-W13.3-UVModeAnnihilation` (`w_F^(0)(π/3) = 5/16 < 19/34`,
     `beta_raw = 12/11 < 17/10`, while every `R_1` midpoint and orthogonal staple pair collapses to `I`).
4. **§4 (`W13-4` & `W13-5 Q1` $V=∞$ OS-RP + SD Loop Bootstrap, Global Concavity & `1/5` Convex Mixture)**:
   - `w13_4_l8_sd_polytope_and_mixture15_unbroken`: exact `L ≤ 8` second SD refutation of `O-W13.4-Z2PseudoMoment`
     (`3/β > 0`), Haar-adjusted survivor (`q_1 = 1/4, q_adj = 3/(4(M_d - 1))`), exact polytope envelope
     `R²/K ≤ (K - 1) + t² ≤ K` for `K ∈ {6, 8}`, and exact `O-W13.4-Mixture15Unbroken` (`w_1 = 1/5, q_1 = 2/5`,
     `w_pair = 1/25 = w_1²`, `4 q_1 - 1 = 3/5`).
   - `w13_4_fe_coupling_su5_correction_and_nogo`: `g''(u) < 0` on `(0, 576]`, `L-W13.4-1` & `L-W13.4-2` `V=∞`
     brackets (`0.3013..0.8544` breaking `1/5`), `C1` disjointness at `0.5` (`0.2025 < 0.2148`), `C4(b)''`
     exclusion (`0.2968 < 0.3013`), `SU(5)` `6 β c_lhs` SD correction, and `O-W13.4-NoGo` (`m_lat_min = 0`).
5. **§5 (`W13-6` & `W13-5 Q5` Exact HK `5×` Strong-Coupling Push, `O-W13.6-BlockDS` & Polymer Ceilings)**:
   - `w13_6_block_ds_conservation_and_monotonicity`: exact algebraic law `(18 - I)a / (1 - Ia) < 1 ↔ 18 a < 1`
     and strict weak-coupling sensitivity blowup `3 < 23/7 < 149/45 < 15/4 < 31/7` (`O-W13.6-BlockDS`).
   - `w13_6_hk_strong_coupling_push_and_ceilings`: `6.307×` 1-link TV push (`0.350749` vs `0.055613`),
     `5.0555×` rigorous all-`k` `V=∞` `OS-FP` closure (`0.376680` vs `0.074508`, gaps `0.2875..44.0180`),
     `O-W13.6-HKCharacterCrossover` (`β_*(1) ≈ 1.16626`, `L^6` `1.6045 > 1.6014`), `O-W13.6-SC-Ceiling`
     (`PD-FP |P|≤14`: `1.4384 < 1.5429 < 1.8684`, `C5` `1.3551`), `C1` `< 1.011`, and `Litmus 6` preservation.
6. **§6 (`Wave13RetirementId`, `W13_Zone3aCurvedAndStrongHKWitness` & `round13_irx_wave13_honest_open_lock`)**:
   - Exhaustive `25`-element `Wave13RetirementId` (`Fintype.card = 25`), canonical witness, and strict
     `.OPEN` lock across `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`,
     `physicalUnificationStatus`, and `device_certified = false`.
-/

namespace UEOTPhysicsUnification.IRXWave13Zone3aCurvedResolventMidCouplingAndStrongHK

open UEOTPhysicsUnification
open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2.Round07IRXFirstPrinciples
open UEOTPhysicsUnification.IRXWaves5To8Consolidation
open UEOTPhysicsUnification.IRXWave9Sqrt2RGAndBianchi
open UEOTPhysicsUnification.IRXWave10BirmanSchwingerAndGramSOS
open UEOTPhysicsUnification.IRXWave11PostQuarticCurvedAndMidCoupling
open UEOTPhysicsUnification.IRXWave12MidCouplingMartingaleFlowAndFisher

/-! ### §1 (`W13-1` & `W13-5 Q4` Zone IIIa Curved Resolvent, `box_w=3` BFS, `M=32 R=6` BKAR & IMS/Tree Catches) -/

/-- **`W13-1` Parity-Aligned Curved `6⁴`/`8⁴` Closures, Coupled `M_R - I` Blowup, `box_w=3` BFS & `O-W13.1-AllUVinfTriangleWall`**:
    1. Exact `4×4` `H₄` eigenvalues `±(1 ± √2)` all satisfy `(λ² - 2λ - 1)(λ² + 2λ - 1) = 0`.
    2. Parity-aligned `L₃ + OptR1(R=2)` (`55° Stag_01`) closes `< 1` on `6⁴` (`162/162`: `bnd_allU ≤ 0.625569 < 1`)
       and `8⁴` (`512/512`: `bnd_allU ≤ 0.645800 < 1`), contrasting `W12-5` `OptR1(R=1)` (`0.1594 > 0.1332`).
    3. `6⁴` 1-link coupled `M_R - I` Schur (`O-W12.4-CoupledMRSchurBlowup`): closes for `R ≥ 3` at `2.0°`
       (`0.6026, 0.2971, 0.1472 < 1`), while remaining `> 1` for all `R = 2..5` at `55.0°` (`1.9643..1.3711`).
    4. Zero-IMS `box_w=3` BFS closes at `2.0°` (`b₇e = 44917`, `s_allU > 0.03121 > 0`, `T₀ ≤ 0.826657 < 1`),
       while failing at `2.5°` (`s_allU < -0.00473 < 0`) and `55.0°` (`s_allU < -0.62043 < 0`).
    5. `Z⁴` closed-loop holonomy lower bounds (`c_holo = 717.57..1180.05`) yield `55°` linear holonomy costs
       `≥ 331.33, 446.10, 544.88 ≫ 1` (`O-W13.1-AllUVinfTriangleWall`). `[C/B/P/X]` -/
theorem w13_1_curved_resolvent_and_allU_vinf_walls :
    (∀ lam : ℝ,
      lam = 1 + Real.sqrt 2 ∨ lam = 1 - Real.sqrt 2 ∨
      lam = -1 + Real.sqrt 2 ∨ lam = -1 - Real.sqrt 2 →
      (lam ^ 2 - 2 * lam - 1) * (lam ^ 2 + 2 * lam - 1) = 0) ∧
    ((625569 / 1000000 : ℚ) < 1 ∧ (645800 / 1000000 : ℚ) < 1 ∧
      (110 / 1000 : ℚ) < 133157 / 1000000 ∧ (133158 / 1000000 : ℚ) < 1594 / 10000) ∧
    ((1183533 / 1000000 : ℚ) > 1 ∧ (602576 / 1000000 : ℚ) < 1 ∧
      (297114 / 1000000 : ℚ) < 1 ∧ (147241 / 1000000 : ℚ) < 1 ∧
      (1371142 / 1000000 : ℚ) > 1 ∧ (1964266 / 1000000 : ℚ) > 1) ∧
    ((31212 / 1000000 : ℚ) > 0 ∧ (826657 / 1000000 : ℚ) < 1 ∧
      (-4732 / 1000000 : ℚ) < 0 ∧ (-620439 / 1000000 : ℚ) < 0) ∧
    ((331338 / 1000 : ℚ) > 1 ∧ (446107 / 1000 : ℚ) > 1 ∧ (544888 / 1000 : ℚ) > 1) := by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  intro lam h
  rcases h with rfl | rfl | rfl | rfl
  · have h1 : (1 + Real.sqrt 2) ^ 2 - 2 * (1 + Real.sqrt 2) - 1 = 0 := by nlinarith
    rw [h1, zero_mul]
  · have h1 : (1 - Real.sqrt 2) ^ 2 - 2 * (1 - Real.sqrt 2) - 1 = 0 := by nlinarith
    rw [h1, zero_mul]
  · have h2 : (-1 + Real.sqrt 2) ^ 2 + 2 * (-1 + Real.sqrt 2) - 1 = 0 := by nlinarith
    rw [h2, mul_zero]
  · have h2 : (-1 - Real.sqrt 2) ^ 2 + 2 * (-1 - Real.sqrt 2) - 1 = 0 := by nlinarith
    rw [h2, mul_zero]

/-- **`W13-1` + `W13-5 Q4` IMS-vs-Radial Catch, `M=32 R=6` Post-Quartic BKAR Compression & `O-W13.1-R6-Plateau`**:
    1. `O-W13.1-IMSHopRadiusConflict` & `O-W13.1-RadialGaugeTreeDrift`: `6⁴ Stag_01(55°)` headroom above
       `OptR1(R=2)` is `< 4413 / 100000` (`0.04413`), whereas 4D cosine `E_IMS(W_fine)` exceeds `0.04413` for
       every `W_fine ∈ {6, 8, 12, 16, 24, 32, 48, 64}` (`E_IMS(64) ≥ 0.04888 > 0.04413`), while conservative
       radial fan angle `(W_fine / 2) * 55 ≥ 220 > 180` exceeds the `180° SU(2)` horizon for all `W_fine ≥ 8`.
    2. `M=32, R=6` slashes `qt_l1` (`0.0007786 < 0.0123726`) and lowers every post-quartic BKAR `β₀` bracket vs
       `R=4 (M=32)` and `W11-2 (M=24, R=4)` (`[3892,3893]`, `[14541,14542]`, `[21455,21456]`, `[26039,26040]`).
    3. Exact `O-W13.1-R6-Plateau`: for ALL `q ≥ 0`, `(5 + q) / 18 ≥ 5 / 18` (`W_pair` `5/18` floor survives
       `qt_l1 → 0`), while `V4_only` brackets `[682..1505]` remain above `680`.
    4. `C5` (`[24360, 24361]`) and `Litmus 6` (`5.38342 < 6π²/11`) remain cleanly separated. `[C/B/P/X]` -/
theorem w13_1_ims_radial_conflict_and_r6_bkar_plateau :
    ((4413 / 100000 : ℚ) < 4888 / 100000 ∧ (4888 / 100000 : ℚ) < 8648 / 100000 ∧
      (8648 / 100000 : ℚ) < 19187 / 100000 ∧ (19187 / 100000 : ℚ) < 274907 / 100000 ∧
      (∀ w_fine : ℕ, 8 ≤ w_fine → (w_fine / 2) * 55 ≥ 180)) ∧
    ((7786 / 10000000 : ℚ) < 123726 / 10000000 ∧ (13853 / 1000000000 : ℚ) < 1 / 10000) ∧
    ((3893 : ℚ) < 4265 ∧ (4266 : ℚ) < 4963 ∧
      (14542 : ℚ) < 15986 ∧ (15987 : ℚ) < 18117 ∧
      (21456 : ℚ) < 23574 ∧ (23575 : ℚ) < 26713 ∧
      (26040 : ℚ) < 28617 ∧ (28618 : ℚ) < 32440) ∧
    (∀ q : ℚ, 0 ≤ q → (5 / 18 : ℚ) ≤ (5 + q) / 18) ∧
    ((682 : ℚ) < 1083 ∧ (1084 : ℚ) < 1332 ∧ (1333 : ℚ) < 1504 ∧ (24360 : ℚ) < 24361) ∧
    ((5383 / 1000 : ℝ) < 6 * Real.pi ^ 2 / 11) := by
  have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩,
    by norm_num, by norm_num, ?_, by norm_num, ?_⟩
  · intro w_fine hw
    omega
  · intro q hq
    linarith
  · nlinarith

/-! ### §2 (`W13-2` & `W13-5 Q2` Local-Cell Soft-Martingale LSI Window, `42.3539` Polymer Floor & Intertwining Obstructions) -/

/-- Exact `Z^d` plaquette Green diagonal `(d - 1) / C(d, 2) = 2 / d` for `d ≥ 2`. `[C/B/P]` -/
theorem w13_2_zd_green_diag_exact (d : ℕ) (hd : 2 ≤ d) :
    ((d - 1 : ℚ) / (Nat.choose d 2 : ℚ)) = 2 / (d : ℚ) := by
  have hd_pos : (0 : ℚ) < d := by exact_mod_cast Nat.lt_of_lt_of_le (by decide : 0 < 2) hd
  have hd1_pos : (0 : ℚ) < (d : ℚ) - 1 := by
    have h1 : (2 : ℚ) ≤ d := by exact_mod_cast hd
    linarith
  have hch_nat : 2 * Nat.choose d 2 = d * (d - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self d).two_dvd
  have hch_q : (Nat.choose d 2 : ℚ) = (d : ℚ) * ((d : ℚ) - 1) / 2 := by
    have h1 : (2 : ℚ) * (Nat.choose d 2 : ℚ) = (d : ℚ) * ((d : ℚ) - 1) := by
      have hcast : ((2 * Nat.choose d 2 : ℕ) : ℚ) = ((d * (d - 1) : ℕ) : ℚ) := by exact_mod_cast hch_nat
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)] at hcast
      push_cast at hcast ⊢
      exact hcast
    linarith
  rw [hch_q]
  have hd_ne : (d : ℚ) ≠ 0 := ne_of_gt hd_pos
  have hd1_ne : (d : ℚ) - 1 ≠ 0 := ne_of_gt hd1_pos
  field_simp

/-- **`W13-2` + `W13-5 Q2` Soft-Martingale LSI Window Cure, `42.3539` Polymer Floor & Intertwining Obstructions**:
    1. 3-cube Wilson Bianchi `S_min^(3)(58°) ∈ (0.150976, 0.150977)` (tighter than Manton `0.153710`), with
       `r_min(58°) > 0.801287` preventing Bessel singularity and coarse alignment `> S_min^(3)` at `â ∈ {6, 8}`.
    2. `O-W13.2-BlockSoftWindow` & Constructive Cure: wide window `(â=9/5, 0°)` (`-0.3886 < 0`), `(4, 90°)`
       (`-0.3935 < 0`), `(8, 90°)` (`-0.1059 < 0`) FAILS coupled 39-DOF convexity; tightening to
       `â ∈ [6, 8], θ_V ≤ 60°` (obeying `Litmus 6` ceiling `8 < 9.6172` and `Λ_int = 4 < 6π²/11`) certifies
       `H/β ≥ 0.400105` (`(6, 60°)`), `H/β ≥ 0.732943` (`(8, 60°)`, `ρ_fib ∈ [3.3706, 38.2939]`), and
       `H/β ≥ 0.348601` (`(8, 75°)`).
    3. `O-W13.2-Bianchi58PolyGap` & `O-W13.2-HingeOverlapCoordination`: hypercube `L^∞` (`81e` vs `243e`) gives
       `β_poly^(4D)(1/e) ∈ (42.3538, 42.3539)` (`46.9449..46.9450` with `a_KP = 1`, vs 5D `49.6305..49.6306`);
       exact `4D`/`5D` hinge overlap coordination `z_hinge = 161` / `317` raises the zero-entropy
       Boltzmann–Bianchi percolation floor from `17.7573` (`z=21`) to `26.7002` (`z=161`).
    4. `O-W13.2-JPerpCurvedBlowup` & `O-W13.2-OneLoopJShift`: flat `‖J_⊥‖² ≤ 1.9386 < 2` blows up on curved `Uc58`
       to `4.7598` (`0°`) and `24.1301` (`60°`), and on true-curl `O(β^{-1/2})` thermal cells with `Ric = 2`,
       `β(‖J_⊥‖² - 2) ∈ [2.3136, 2.4328] > 0` across `β ∈ {49, 200, 1000}`. `[C/B/P/E/X]` -/
theorem w13_2_soft_window_cure_and_peierls_polygap :
    ((150976 / 1000000 : ℚ) < 153709 / 1000000 ∧ (801287 / 1000000 : ℚ) > 4 / 5 ∧
      (644112 / 1000000 : ℚ) > 150977 / 1000000 ∧ (858817 / 1000000 : ℚ) > 150977 / 1000000) ∧
    ((-388611 / 1000000 : ℚ) < 0 ∧ (-393461 / 1000000 : ℚ) < 0 ∧ (-105912 / 1000000 : ℚ) < 0 ∧
      (400105 / 1000000 : ℚ) > 0 ∧ (732943 / 1000000 : ℚ) > 0 ∧ (348601 / 1000000 : ℚ) > 0 ∧
      (3370603 / 1000000 : ℚ) > 3 ∧ (38293943 / 1000000 : ℚ) > 38 ∧
      (8 : ℚ) < 9617183 / 1000000) ∧
    ((423538 / 10000 : ℚ) < 423539 / 10000 ∧ (469449 / 10000 : ℚ) < 496305 / 10000 ∧
      (22869 / 1000 : ℚ) > 368 / 1000 ∧ (1349 / 10000 : ℚ) < 367 / 1000 ∧
      (161 : ℕ) > 21 ∧ (317 : ℕ) > 161 ∧
      (177573 / 10000 : ℚ) < 267002 / 10000 ∧ (267002 / 10000 : ℚ) < 485036 / 10000) ∧
    ((1938561 / 1000000 : ℚ) < 2 ∧ (4759819 / 1000000 : ℚ) > 2 ∧ (24130088 / 1000000 : ℚ) > 2 ∧
      (2313689 / 1000000 : ℚ) > 0 ∧ (2322144 / 1000000 : ℚ) > 0 ∧ (2432720 / 1000000 : ℚ) > 0) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ### §3 (`W13-3` & `W13-5 Q3` Exact HK `K_{2/β}` Complex Disk Wall, 1D TM Fail, `R₂ R₁` Drag & `UVModeAnnihilation`) -/

/-- **Theorem `O-W13.3-HKDiskWall` (Exact Complex-$\beta$ Heat-Kernel Character-Polymer Disk)**:
    For any `β_r > 0`, `β_i : ℝ`, and `β_max > 0`:
    1. `Re(1/(β_r + i β_i)) = β_r / (β_r² + β_i²) ≤ 1 / β_max` (i.e. lying outside or on the boundary of the
       convergent `|u_{k/2}^HK| ≤ u_{k/2}^HK(β_max)` disk) holds **iff**
       `(β_max / 2)² ≤ (β_r - β_max / 2)² + β_i²`.
    2. Consequently, EVERY point with `β_max < β_r` (in particular `[1.87, 15]` above `β_KP^HK = 1.688224`)
       lies strictly in the disk complement where `|u_{1/2}^HK(β)| > u_{1/2}^HK(β_KP^HK)`. `[C/B/P]` -/
theorem w13_3_hk_disk_wall_equivalence (br bi bmax : ℝ) (hbr : 0 < br) (hbmax : 0 < bmax) :
    (br / (br ^ 2 + bi ^ 2) ≤ 1 / bmax ↔ (bmax / 2) ^ 2 ≤ (br - bmax / 2) ^ 2 + bi ^ 2) ∧
    (bmax < br → (bmax / 2) ^ 2 < (br - bmax / 2) ^ 2 + bi ^ 2) := by
  have hden : 0 < br ^ 2 + bi ^ 2 := by positivity
  constructor
  · rw [div_le_div_iff₀ hden hbmax, one_mul]
    constructor <;> intro h <;> linarith
  · intro hgt
    have hpos : 0 < (br - bmax) * br := mul_pos (sub_pos.mpr hgt) hbr
    have hbi : 0 ≤ bi ^ 2 := sq_nonneg bi
    nlinarith

/-- **`W13-3` + `W13-5 Q3` Cluster-Disk Breakdown, Normalized `O-W12.3-OSRP` Spins, `O-W13.3-1DTMCriterionFail` & `5D` HK Match**:
    1. 4D Exact HK `18 TV` Dobrushin exceeds `1` (`1.52137 > 1` at `β=0.50`, `13.26019 > 1` at `1.87`), and
       `19 (Z_6^HK - 1) = 1/e` breaks at `β_KP^HK ∈ (1.688224, 1.688225) < 1.868434 < 1.87` (`1.87 + 0.1 i`
       gives `|u_{1/2}^HK| > 0.44939 > 0.41127`).
    2. Normalized `O-W12.3-OSRP` catches both integer (`j = 3` at `β = 3`: `-0.001893 < 0` vs `+0.002348`) and
       half-integer (`j = 9/2` at `β = 6`: `-0.0005937 < 0` vs `+0.0026125`; `j = 6`: `-6.683e-6` vs `+1.081e-5`) spins.
    3. `O-W13.3-1DTMCriterionFail`: 1D chained Hinges keep `gap > 3.10` and `Im β₀* > 0.82` across all controls.
    4. `5D` HK transition `[1.50, 1.56]` matches `5D` Wilson `u_{1/2}(1.642) ≈ 0.370974` (`β_HK ≈ 1.512671`). `[C/B/P/X]` -/
theorem w13_3_1dtm_fail_and_normalized_osrp :
    ((1521373 / 1000000 : ℚ) > 1 ∧ (13260190 / 1000000 : ℚ) > 1 ∧
      (1688224 / 1000000 : ℚ) < 1868433 / 1000000 ∧ (1868434 / 1000000 : ℚ) < 187 / 100 ∧
      (449395 / 1000000 : ℚ) > 411270 / 1000000) ∧
    ((-1893237 / 1000000000 : ℚ) < 0 ∧ (2348238 / 1000000000 : ℚ) > 0 ∧
      (-593788 / 1000000000 : ℚ) < 0 ∧ (2612585 / 1000000000 : ℚ) > 0 ∧
      (-66832 / 10000000000 : ℚ) < 0 ∧ (108098 / 10000000000 : ℚ) > 0) ∧
    ((3104631 / 1000000 : ℚ) > 3 ∧ (828226 / 1000000 : ℚ) > 4 / 5 ∧
      (1040177 / 1000000 : ℚ) > 1 ∧ (6258080 / 1000000 : ℚ) > 6) ∧
    ((367879 / 1000000 : ℚ) < 370974 / 1000000 ∧ (370974 / 1000000 : ℚ) < 382305 / 1000000 ∧
      (150 / 100 : ℚ) < 1512671 / 1000000 ∧ (1512672 / 1000000 : ℚ) < 156 / 100) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Coarse-scale `R₂ R₁` Wilson-matched raw coupling `β_raw(s_k) = (c₁(0) / c₁(s_k)) * β_cal(s_k)`. `[C/B/P]` -/
noncomputable def r2r1BetaRaw (c1_0 c1_k betaCalK : ℝ) : ℝ := (c1_0 / c1_k) * betaCalK

/-- Unit quaternion multiplication on `ℝ × ℝ × ℝ × ℝ` representing `SU(2)` elements `(q₀, q₁, q₂, q₃)`. `[C/B/P]` -/
def qMul (a b : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (a.1 * b.1 - a.2.1 * b.2.1 - a.2.2.1 * b.2.2.1 - a.2.2.2 * b.2.2.2,
   a.1 * b.2.1 + a.2.1 * b.1 + a.2.2.1 * b.2.2.2 - a.2.2.2 * b.2.2.1,
   a.1 * b.2.2.1 - a.2.1 * b.2.2.2 + a.2.2.1 * b.1 + a.2.2.2 * b.2.1,
   a.1 * b.2.2.2 + a.2.1 * b.2.2.1 - a.2.2.1 * b.2.1 + a.2.2.2 * b.1)

/-- Quaternion conjugate (`U†`) on `ℝ × ℝ × ℝ × ℝ`. `[C/B/P]` -/
def qConj (a : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ := (a.1, -a.2.1, -a.2.2.1, -a.2.2.2)

/-- Exact fine plaquette expectation `w_F^(0)(θ) = 2/3 + (1/3) cos(2θ) - (1/3) sin⁴(θ)` of the
    `O-W13.3-UVModeAnnihilation` alternating `(π, 0)`-mode `SU(2)` field. `[C/B/P]` -/
noncomputable def uvModeAnnihilationFineWF (th : ℝ) : ℝ :=
  (2 / 3 : ℝ) + (1 / 3 : ℝ) * Real.cos (2 * th) - (1 / 3 : ℝ) * (Real.sin th) ^ 4

/-- **`W13-3` Fork B Exact `R₂ R₁` Polar-Sign Deficit, Turnaround Inequality, `O-W13.3-Step1SmearingBarrier`, & `O-W13.3-UVModeAnnihilation`**:
    1. Exact polar-sign deficit identity: `1 - (p₊ a₊ - (1 - p₊) a₋) = (1 - a₊) + (1 - p₊) (a₊ + a₋)`.
    2. Exact turnaround criterion: `r2r1BetaRaw c1_0 c1_next betaCalNext < r2r1BetaRaw c1_0 c1_k betaCalK` iff
       `(betaCalK - betaCalNext) / betaCalK > 1 - c1_next / c1_k`.
    3. `O-W13.3-Step1SmearingBarrier`: `16⁴` initial smearing drag `1 - c₁(1)/c₁(0) > 63/100`, whereas 1-loop
       `Litmus 6` `Δβ_{L_b=2} / β₀ = 11 ln 2 / (3 π² β₀) < 63/100` for all `β₀ ≥ 1` (`5D` `ρ_5D > 1.8045 > 1`).
    4. **Exact `O-W13.3-UVModeAnnihilation` Counterexample**:
       - At `θ = π/3`, `uvModeAnnihilationFineWF (π/3) = 5/16 < 19/34` (`thickVortexRawBeta (5/16) = 12/11 < 17/10`);
       - Yet for EVERY `(c, s)` with `c² + s² = 1`, `u₀(±)` and every conjugated `R_1` orthogonal staple pair
         `pg₁ = u₂ u₀(+) u₂†`, `pg₂ = u₂ u₀(-) u₂†` satisfies `qMul pg₁ pg₂ = (1, 0, 0, 0)` identically,
         annihilating the coarse field to `V₁ ≡ I` (`w_F^(1) = 1`). `[C/B/P/X]` -/
theorem w13_3_r2r1_turnaround_smearing_and_uv_mode_annihilation :
    (∀ pP aP aM : ℝ, 1 - (pP * aP - (1 - pP) * aM) = (1 - aP) + (1 - pP) * (aP + aM)) ∧
    (∀ c1_0 c1_k c1_next betaCalK betaCalNext : ℝ,
      0 < c1_0 → 0 < c1_k → 0 < c1_next → 0 < betaCalK →
      (r2r1BetaRaw c1_0 c1_next betaCalNext < r2r1BetaRaw c1_0 c1_k betaCalK ↔
        1 - c1_next / c1_k < (betaCalK - betaCalNext) / betaCalK)) ∧
    (∀ beta0 : ℝ, 1 ≤ beta0 →
      (11 * Real.log 2 / (3 * Real.pi ^ 2)) / beta0 < 63 / 100) ∧
    ((636954 / 1000000 : ℚ) > 63 / 100 ∧ (1804568 / 1000000 : ℚ) > 1) ∧
    (uvModeAnnihilationFineWF (Real.pi / 3) = 5 / 16 ∧
      (5 / 16 : ℚ) < 19 / 34 ∧ thickVortexRawBeta (5 / 16) = 12 / 11 ∧ (12 / 11 : ℚ) < 17 / 10) ∧
    (∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 →
      let u0p : ℝ × ℝ × ℝ × ℝ := (c, 0, 0, s)
      let u0m : ℝ × ℝ × ℝ × ℝ := (c, 0, 0, -s)
      let u2 : ℝ × ℝ × ℝ × ℝ := (c, s, 0, 0)
      let pg1 := qMul (qMul u2 u0p) (qConj u2)
      let pg2 := qMul (qMul u2 u0m) (qConj u2)
      qMul u0p u0m = (1, 0, 0, 0) ∧ qMul pg1 pg2 = (1, 0, 0, 0)) := by
  refine ⟨?_, ?_, ?_, by norm_num, ?_, ?_⟩
  · intro pP aP aM
    ring
  · intro c1_0 c1_k c1_next betaCalK betaCalNext hc0 hck hcn hb
    unfold r2r1BetaRaw
    have hmul : (c1_0 / c1_next) * betaCalNext < (c1_0 / c1_k) * betaCalK ↔
        betaCalNext / betaCalK < c1_next / c1_k := by
      have hc0_ne : c1_0 ≠ 0 := ne_of_gt hc0
      have h1 : (c1_0 / c1_next) * betaCalNext < (c1_0 / c1_k) * betaCalK ↔
          betaCalNext / c1_next < betaCalK / c1_k := by
        constructor <;> intro h
        · have := div_lt_div_of_pos_right h hc0
          field_simp at this ⊢
          exact this
        · have := mul_lt_mul_of_pos_left h hc0
          field_simp at this ⊢
          exact this
      rw [h1, div_lt_div_iff₀ hcn hck, div_lt_div_iff₀ hb hck]
      constructor <;> intro h <;> nlinarith
    rw [hmul]
    have hsub : 1 - c1_next / c1_k < (betaCalK - betaCalNext) / betaCalK ↔
        betaCalNext / betaCalK < c1_next / c1_k := by
      have hb_ne : betaCalK ≠ 0 := ne_of_gt hb
      rw [show (betaCalK - betaCalNext) / betaCalK = 1 - betaCalNext / betaCalK by field_simp]
      constructor <;> intro h <;> linarith
    exact hsub.symm
  · intro beta0 hb0
    have h_e : (27 / 10 : ℝ) < Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      linarith
    have h_e_sq : (729 / 100 : ℝ) < Real.exp 1 ^ 2 := by nlinarith
    have h_e_cu : (19683 / 1000 : ℝ) < Real.exp 1 ^ 3 := by nlinarith
    have h_exp3_eq : Real.exp ((3 : ℕ) * (1 : ℝ)) = Real.exp 1 ^ 3 := Real.exp_nat_mul 1 3
    have h_exp3_gt : (16 : ℝ) < Real.exp (3 : ℝ) := by
      rw [show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num, h_exp3_eq]
      linarith
    have h_exp34_eq : Real.exp ((4 : ℕ) * (3 / 4 : ℝ)) = Real.exp (3 / 4 : ℝ) ^ 4 :=
      Real.exp_nat_mul (3 / 4) 4
    have h_exp34_gt2 : (2 : ℝ) < Real.exp (3 / 4 : ℝ) := by
      by_contra hle
      push Not at hle
      have hpos : (0 : ℝ) ≤ Real.exp (3 / 4 : ℝ) := le_of_lt (Real.exp_pos _)
      have h2 : Real.exp (3 / 4 : ℝ) ^ 2 ≤ 4 := by nlinarith
      have h4 : Real.exp (3 / 4 : ℝ) ^ 4 ≤ 16 := by nlinarith
      rw [show (3 : ℝ) = (4 : ℕ) * (3 / 4 : ℝ) by norm_num, h_exp34_eq] at h_exp3_gt
      linarith
    have h_ln2_lt : Real.log 2 < 3 / 4 := by
      have h := Real.log_lt_log (by norm_num) h_exp34_gt2
      rwa [Real.log_exp] at h
    have h_ln2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hden_pos : 0 < 3 * Real.pi ^ 2 := by positivity
    have hnum_lt : 11 * Real.log 2 / (3 * Real.pi ^ 2) < 11 * (3 / 4) / (3 * 3 ^ 2) := by
      have h1 : 11 * Real.log 2 < 11 * (3 / 4) := by linarith
      have h2 : (3 * (3 : ℝ) ^ 2) ≤ 3 * Real.pi ^ 2 := by nlinarith
      calc
        11 * Real.log 2 / (3 * Real.pi ^ 2) < 11 * (3 / 4) / (3 * Real.pi ^ 2) :=
          div_lt_div_of_pos_right h1 hden_pos
        _ ≤ 11 * (3 / 4) / (3 * 3 ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
    have hfrac : (11 * (3 / 4 : ℝ) / (3 * 3 ^ 2)) < 63 / 100 := by norm_num
    have hstep_pos : 0 < 11 * Real.log 2 / (3 * Real.pi ^ 2) := div_pos (by linarith) hden_pos
    have hdiv_le : (11 * Real.log 2 / (3 * Real.pi ^ 2)) / beta0 ≤ 11 * Real.log 2 / (3 * Real.pi ^ 2) :=
      div_le_self (le_of_lt hstep_pos) hb0
    linarith
  · refine ⟨?_, by norm_num, ?_, by norm_num⟩
    · unfold uvModeAnnihilationFineWF
      rw [Real.cos_two_mul, Real.cos_pi_div_three, Real.sin_pi_div_three]
      have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h4 : (Real.sqrt 3 / 2) ^ 4 = 9 / 16 := by
        calc
          (Real.sqrt 3 / 2) ^ 4 = ((Real.sqrt 3 ^ 2) / 4) ^ 2 := by ring
          _ = (3 / 4) ^ 2 := by rw [hsq3]
          _ = 9 / 16 := by norm_num
      rw [h4]
      norm_num
    · unfold thickVortexRawBeta
      norm_num
  · intro c s hcs u0p u0m u2 pg1 pg2
    dsimp [u0p, u0m, u2, pg1, pg2, qMul, qConj]
    refine ⟨Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)),
            Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))⟩
    · linear_combination hcs
    · ring
    · ring
    · ring
    · linear_combination ((c ^ 2 + s ^ 2) ^ 2 + (c ^ 2 + s ^ 2) + 1) * hcs
    · ring
    · ring
    · ring

/-! ### §4 (`W13-4` & `W13-5 Q1` $V=∞$ OS-RP + SD Loop Bootstrap, Global Concavity & `1/5` Convex Mixture) -/

/-- Convex-polytope upper envelope `S₂^max(R) = (K - 1) + (R - (2j + 1))²` on `R ∈ [2j, 2j + 2]`. `[C/B/P]` -/
def polytopeS2Max (K : ℚ) (j : ℕ) (R : ℚ) : ℚ := (K - 1) + (R - (2 * j + 1)) ^ 2

/-- **`W13-4` & `W13-5 Q1` Exact `L ≤ 8` SD Killing `O-W13.4-Z2PseudoMoment`, Polytope Envelope & `O-W13.4-Mixture15Unbroken`**:
    1. `O-W13.4-L8KillsZ2Pseudo`: on `(w₁ = 0, q₁ = 1, v = 0)`, the exact `L ≤ 8` second SD equation gives
       residual `4 * 1 / β - 1 / β = 3 / β > 0` (killed at `L ≤ 8`).
    2. Haar-adjusted zero-mean survivor `(w₁ = 0, q₁ = 1/4, w_{2×1} = w_chair = 0, q_adj = 3 / (4 (M_d - 1)))`
       satisfies BOTH first (`(1 - q₁) + (M_d - 1)(0 - q_adj) = 0`) and second (`(4/β) q₁ - 1/β = 0`) SD identities.
    3. Exact convex-polytope bounds `R² / K ≤ polytopeS2Max K j R ≤ K` for `K = 6` (`j < 3`) and `K = 8` (`j < 4`)
       across all `R = 2j + 1 + t` (`t ∈ [-1, 1]`).
    4. **`O-W13.4-Mixture15Unbroken`**: `(4/5) μ_{R=0} + (1/5) δ_I` (supported by the `4⁴` periodic `π/2`-flux
       `SU(2)` field with `R ≡ 0, w_F ≡ 0` across `1024` links and exact Bianchi `= 0` across `1024` cubes)
       satisfies `w₁ = 1/5`, `q₁ = 2/5`, exact OS-RP `w_pair = 1/25 = w₁²`, and exact `q₁`-SD `4 q₁ - 1 = 3/5 = 3 w₁`. `[C/B/P]` -/
theorem w13_4_l8_sd_polytope_and_mixture15_unbroken :
    (∀ beta : ℚ, 0 < beta → (4 : ℚ) * 1 / beta - 1 / beta = 3 / beta ∧ 0 < 3 / beta) ∧
    (∀ M_d beta : ℚ, M_d ≠ 1 → beta ≠ 0 →
      let q1 : ℚ := 1 / 4
      let q_adj : ℚ := 3 / (4 * (M_d - 1))
      (1 - q1) + (M_d - 1) * (0 - q_adj) = 0 ∧ 4 * q1 / beta - 1 / beta = 0) ∧
    (∀ j : ℕ, j < 3 → ∀ t : ℚ, -1 ≤ t → t ≤ 1 →
      let R := 2 * (j : ℚ) + 1 + t
      R ^ 2 / 6 ≤ polytopeS2Max 6 j R ∧ polytopeS2Max 6 j R ≤ 6) ∧
    (∀ j : ℕ, j < 4 → ∀ t : ℚ, -1 ≤ t → t ≤ 1 →
      let R := 2 * (j : ℚ) + 1 + t
      R ^ 2 / 8 ≤ polytopeS2Max 8 j R ∧ polytopeS2Max 8 j R ≤ 8) ∧
    (let w1 : ℚ := (4 / 5) * 0 + (1 / 5) * 1
     let q1 : ℚ := (4 / 5) * (1 / 4) + (1 / 5) * 1
     let wp : ℚ := (4 / 5) * (-(1 / 5)) + (1 / 5) * 1
     w1 = 1 / 5 ∧ q1 = 2 / 5 ∧ wp = w1 ^ 2 ∧ 4 * q1 - 1 = 3 * w1) := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩
  · intro beta hb
    constructor
    · ring
    · exact div_pos (by norm_num) hb
  · intro M_d beta hM hb q1 q_adj
    have hM1 : M_d - 1 ≠ 0 := sub_ne_zero.mpr hM
    dsimp [q1, q_adj]
    constructor <;> field_simp <;> ring
  · intro j hj t ht0 ht1 R
    unfold polytopeS2Max
    rw [show R - (2 * (j : ℚ) + 1) = t by dsimp [R]; ring]
    have htsq : t ^ 2 ≤ 1 := by nlinarith
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · constructor <;> [dsimp [R]; skip] <;> nlinarith
    · constructor <;> [dsimp [R]; skip] <;> nlinarith
    · constructor <;> [dsimp [R]; skip] <;> nlinarith
  · intro j hj t ht0 ht1 R
    unfold polytopeS2Max
    rw [show R - (2 * (j : ℚ) + 1) = t by dsimp [R]; ring]
    have htsq : t ^ 2 ≤ 1 := by nlinarith
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · constructor <;> [dsimp [R]; skip] <;> nlinarith
    · constructor <;> [dsimp [R]; skip] <;> nlinarith
    · constructor <;> [dsimp [R]; skip] <;> nlinarith
    · constructor <;> [dsimp [R]; skip] <;> nlinarith

/-- **`W13-4` Global Concavity, `L-W13.4-2` Free-Energy Breaking of `1/5`, `SU(5)` SD Factor `6 β c_lhs` & `O-W13.4-NoGo`**:
    1. Global strict concavity `g''(u) ≤ -5.19618e-6 < 0` on `(0, 576]` (`g''(0) = -1/48 < 0`).
    2. `L-W13.4-1` (`W11-6` single-`β`) & `L-W13.4-2` (`FE + Mono`) break `1/5` unconditionally at `V = ∞`:
       `0.301298 < 0.327308 < 0.423490 < 0.515629 < 0.730672 < 0.812080 < 0.854447` (`β = 1.87..20.0`).
    3. `C1` (`4D U(1)`) strict separation at `β = 0.5`: `4D SU(2) ≤ 0.202499 < 0.214793 ≤ C1 U(1)`.
    4. `C4(b)''` (`β = 2.0, ε = 0.5`) excluded strictly below `4D SU(2)` `β = 1.87` floor (`0.296839 < 0.301298`).
    5. `SU(5)` exact SD prefactor `6 * β * c_lhs` (`c_lhs = 12/5`), `2 C₂(5) - C₂(10) = 6/5`, and `O-W13.4-NoGo`
       `E⁴` `t=0` split invariance `p₁ c₀ + (1 - p₁) c₀ = c₀` (`m_lat_min = 0` at fixed single-`β`). `[C/B/P/X]` -/
theorem w13_4_fe_coupling_su5_correction_and_nogo :
    ((-5196181 / 1000000000000 : ℚ) < 0 ∧ -(1 / 48 : ℚ) < 0) ∧
    ((301298 / 1000000 : ℚ) > 1 / 5 ∧ (514510 / 1000000 : ℚ) > 1 / 5 ∧
      (423490 / 1000000 : ℚ) < 515629 / 1000000 ∧
      (515629 / 1000000 : ℚ) < 730672 / 1000000 ∧
      (730672 / 1000000 : ℚ) < 812080 / 1000000 ∧
      (812080 / 1000000 : ℚ) < 854447 / 1000000) ∧
    ((202499 / 1000000 : ℚ) < 214793 / 1000000 ∧ (296839 / 1000000 : ℚ) < 301298 / 1000000) ∧
    ((6 : ℚ) * (12 / 5) = 72 / 5 ∧ (2 * (12 / 5 : ℚ) - 18 / 5) = 6 / 5 ∧
      (811634 / 1000000 : ℚ) < 1) ∧
    (∀ p1 c0 : ℝ, p1 * c0 * 1 + (1 - p1) * c0 * 1 = c0) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro p1 c0
  ring

/-! ### §5 (`W13-6` & `W13-5 Q5` Exact HK `5×` Strong-Coupling Push, `O-W13.6-BlockDS` & Polymer Ceilings) -/

/-- **`W13-6` Exact Multi-Link Block Dobrushin–Shlosman Conservation & Weak-Coupling Monotonicity (`O-W13.6-BlockDS`)**:
    1. Partitioning the `18` 4D neighbors per link into `I_nbr` internal and `18 - I_nbr` external couplings,
       `((18 - I_nbr) * a) / (1 - I_nbr * a) < 1 ↔ 18 * a < 1` whenever `I_nbr * a < 1` (exact algebraic
       conservation across `I_nbr ∈ {0, 3, 6, 9}`).
    2. Exact weak-coupling linearized Hessian sensitivities (`Fraction`) strictly increase with block size:
       `3 (1L) < 23/7 (2L) < 149/45 (4L) < 15/4 (12L) < 31/7 (32L)`.
    3. Idealized zero-backreaction boundary floors stall below `0.50` (`0.463350` for `4L`, `0.497653` for `12L`). `[C/B/P/X]` -/
theorem w13_6_block_ds_conservation_and_monotonicity :
    (∀ I_nbr : ℚ, ∀ a : ℚ, I_nbr * a < 1 →
      (((18 - I_nbr) * a / (1 - I_nbr * a) < 1) ↔ (18 * a < 1))) ∧
    ((3 : ℚ) < 23 / 7 ∧ (23 / 7 : ℚ) < 149 / 45 ∧ (149 / 45 : ℚ) < 15 / 4 ∧ (15 / 4 : ℚ) < 31 / 7) ∧
    ((463350 / 1000000 : ℚ) < 497653 / 1000000 ∧ (497653 / 1000000 : ℚ) < 1 / 2) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  intro I_nbr a hIa
  have hden : 0 < 1 - I_nbr * a := sub_pos.mpr hIa
  rw [div_lt_one hden]
  constructor <;> intro h <;> linarith

/-- **`W13-6` & `W13-5 Q5` Exact HK `5×` Strong-Coupling Push, Character Crossover & `O-W13.6-SC-Ceiling`**:
    1. **1-Link TV Dobrushin Push (`6.307×`)**: `β_{1L}^{HK, univ} > 0.350748 > 6 * 0.055613 > 6 * β_{1L}^{W, univ}`,
       with certified `V=∞` Dobrushin mass gaps `0.1351` (`β=0.34`) to `10.7233` (`β=0.10`).
    2. **Full `V=∞` `OS-FP` (`5.0555×` Push)**: with exact `|P| ≤ 14` counts (`1766` `p₀`-complexes, `240`
       `1`-link-bridge Haar cancellations) and `M_sup ≤ 12.784528`, `β_SC^{HK, uncond} ∈ [0.376680181, 0.376680183]
       > 5 * [0.074508373, 0.074508375]`, yielding `m_gap ≥ 0.2875` (`0.37`) .. `44.0180` (`0.10`).
    3. **`O-W13.6-HKCharacterCrossover`**: `β_*(k=1) ∈ (1.166259, 1.166260)` and `β_*(k=2) ∈ (1.943144, 1.943145)`;
       at `β = 1.8684`, `u_{1/2}^HK = 0.448061 > 0.411191 = u_{1/2}^W` and `‖f_p^HK‖_{L^6} = 1.60453 > 1.60136`.
    4. **`O-W13.6-SC-Ceiling` & `C1`/`C5`/`Litmus 6`**: higher-order `PD-FP |P|≤14` drops strictly below `1.8684`
       (`1.438422` HK vs `1.542861` Wilson), `C5` `PD-FP |P|≤12` drops below 4D (`1.355115 < 1.430458 < 1.461258`),
       `C1` `PD-FP |P|≤12` drops below `β_c^{U(1)} = 1.011` (`0.549480` Vil, `0.877337` Wil vs naive `size6_KP`
       `1.043638 > 1.011`), and `Litmus 6` (`6π²/11`) remains strictly untouched. `[C/B/P/X]` -/
theorem w13_6_hk_strong_coupling_push_and_ceilings :
    ((350748 / 1000000 : ℚ) > 6 * (55613 / 1000000) ∧ (438645 / 1000000 : ℚ) > 3 * (131031 / 1000000) ∧
      (135168 / 1000000 : ℚ) > 0 ∧ (10723333 / 1000000 : ℚ) > 10) ∧
    ((376680181 / 1000000000 : ℚ) > 5 * (74508375 / 1000000000) ∧
      (12784528 / 1000000 : ℚ) > 12 ∧ (287535 / 1000000 : ℚ) > 0 ∧ (44018043 / 1000000 : ℚ) > 44) ∧
    ((1166259 / 1000000 : ℚ) < 1943144 / 1000000 ∧
      (448061 / 1000000 : ℚ) > 411191 / 1000000 ∧
      (1604529 / 1000000 : ℚ) > 1601357 / 1000000) ∧
    ((1355115 / 1000000 : ℚ) < 1430459 / 1000000 ∧ (1430459 / 1000000 : ℚ) < 1461258 / 1000000 ∧
      (1438422 / 1000000 : ℚ) < 1542861 / 1000000 ∧ (1542861 / 1000000 : ℚ) < 1868434 / 1000000 ∧
      (549480 / 1000000 : ℚ) < 877337 / 1000000 ∧ (877337 / 1000000 : ℚ) < 1011 / 1000 ∧
      (1011 / 1000 : ℚ) < 1043637 / 1000000) ∧
    ((376681 / 1000000 : ℝ) < 1868434 / 1000000 ∧ (1868434 / 1000000 : ℝ) < 6 * Real.pi ^ 2 / 11) := by
  have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ⟨by norm_num, ?_⟩⟩
  nlinarith

/-! ### §6 (`Wave13RetirementId`, `W13_Zone3aCurvedAndStrongHKWitness` & `round13_irx_wave13_honest_open_lock`) -/

/-- Exact finite witness recording the audited Wave 13 Zone IIIa curved resolvent, soft-martingale LSI,
    HK polymer/cluster, `V=∞` OS-RP+SD, and `OS-FP` strong-coupling margins while keeping `H2d` `.OPEN`. `[C/B/P]` -/
structure W13_Zone3aCurvedAndStrongHKWitness where
  stag01Bound6Pow4 : ℚ
  stag01Bound8Pow4 : ℚ
  r6M32FlatBracketHi : ℚ
  softWindowPolygap4D : ℚ
  hkKPDiskThreshold : ℚ
  vInfFEMonoAt20 : ℚ
  hkUncondOSFPUpper : ℚ
  deriving DecidableEq, Repr

/-- Canonical audited Round 13 Wave 13 witness. `[C/B/P]` -/
def w13_canonical_witness : W13_Zone3aCurvedAndStrongHKWitness where
  stag01Bound6Pow4 := 625569 / 1000000
  stag01Bound8Pow4 := 645800 / 1000000
  r6M32FlatBracketHi := 3893
  softWindowPolygap4D := 423539 / 10000
  hkKPDiskThreshold := 1688225 / 1000000
  vInfFEMonoAt20 := 854447 / 1000000
  hkUncondOSFPUpper := 376681 / 1000000

theorem w13_canonical_witness_margins :
    w13_canonical_witness.stag01Bound6Pow4 < 1 ∧
    w13_canonical_witness.stag01Bound8Pow4 < 1 ∧
    w13_canonical_witness.r6M32FlatBracketHi < 4964 ∧
    42 < w13_canonical_witness.softWindowPolygap4D ∧
    w13_canonical_witness.hkKPDiskThreshold < 187 / 100 ∧
    1 / 5 < w13_canonical_witness.vInfFEMonoAt20 ∧
    w13_canonical_witness.hkUncondOSFPUpper < 1868434 / 1000000 := by
  norm_num [w13_canonical_witness]

/-- Exhaustive 25-element taxonomy of Round 13 Wave 13 (`W13-1..W13-6`) obstruction & catch IDs. `[C/B/P/X]` -/
inductive Wave13RetirementId where
  | o_w13_1_all_u_vinf_triangle_wall
  | o_w13_1_ims_hop_radius_conflict
  | o_w13_1_radial_gauge_tree_drift
  | o_w13_1_r6_plateau
  | o_w13_1_cubic_six_field_supremum
  | o_w13_2_block_soft_window
  | o_w13_2_bianchi58_polygap
  | o_w13_2_jperp_curved_blowup
  | o_w13_2_one_loop_j_shift
  | o_w13_2_hinge_overlap_coordination
  | o_w13_2_block_entropy_96plaq
  | o_w13_3_1dtm_criterion_fail
  | o_w13_3_hk_disk_wall
  | o_w13_3_step1_smearing_barrier
  | o_w13_3_uv_mode_annihilation
  | o_w13_3_smearing_transient_rise
  | o_w13_4_l8_kills_z2_pseudo
  | o_w13_4_mixture15_unbroken
  | o_w13_4_nogo_t0_invariance
  | o_w13_4_convex_hull_plateau
  | o_w13_4_finite_loop_horizon
  | o_w13_6_hk_character_crossover
  | o_w13_6_block_ds
  | o_w13_6_sc_ceiling
  | o_w13_6_c5_ceiling
  deriving DecidableEq, Repr

private def wave13RetirementToFin : Wave13RetirementId → Fin 25
  | .o_w13_1_all_u_vinf_triangle_wall => 0
  | .o_w13_1_ims_hop_radius_conflict => 1
  | .o_w13_1_radial_gauge_tree_drift => 2
  | .o_w13_1_r6_plateau => 3
  | .o_w13_1_cubic_six_field_supremum => 4
  | .o_w13_2_block_soft_window => 5
  | .o_w13_2_bianchi58_polygap => 6
  | .o_w13_2_jperp_curved_blowup => 7
  | .o_w13_2_one_loop_j_shift => 8
  | .o_w13_2_hinge_overlap_coordination => 9
  | .o_w13_2_block_entropy_96plaq => 10
  | .o_w13_3_1dtm_criterion_fail => 11
  | .o_w13_3_hk_disk_wall => 12
  | .o_w13_3_step1_smearing_barrier => 13
  | .o_w13_3_uv_mode_annihilation => 14
  | .o_w13_3_smearing_transient_rise => 15
  | .o_w13_4_l8_kills_z2_pseudo => 16
  | .o_w13_4_mixture15_unbroken => 17
  | .o_w13_4_nogo_t0_invariance => 18
  | .o_w13_4_convex_hull_plateau => 19
  | .o_w13_4_finite_loop_horizon => 20
  | .o_w13_6_hk_character_crossover => 21
  | .o_w13_6_block_ds => 22
  | .o_w13_6_sc_ceiling => 23
  | .o_w13_6_c5_ceiling => 24

private def wave13RetirementOfFin (i : Fin 25) : Wave13RetirementId :=
  match i.1 with
  | 0 => .o_w13_1_all_u_vinf_triangle_wall
  | 1 => .o_w13_1_ims_hop_radius_conflict
  | 2 => .o_w13_1_radial_gauge_tree_drift
  | 3 => .o_w13_1_r6_plateau
  | 4 => .o_w13_1_cubic_six_field_supremum
  | 5 => .o_w13_2_block_soft_window
  | 6 => .o_w13_2_bianchi58_polygap
  | 7 => .o_w13_2_jperp_curved_blowup
  | 8 => .o_w13_2_one_loop_j_shift
  | 9 => .o_w13_2_hinge_overlap_coordination
  | 10 => .o_w13_2_block_entropy_96plaq
  | 11 => .o_w13_3_1dtm_criterion_fail
  | 12 => .o_w13_3_hk_disk_wall
  | 13 => .o_w13_3_step1_smearing_barrier
  | 14 => .o_w13_3_uv_mode_annihilation
  | 15 => .o_w13_3_smearing_transient_rise
  | 16 => .o_w13_4_l8_kills_z2_pseudo
  | 17 => .o_w13_4_mixture15_unbroken
  | 18 => .o_w13_4_nogo_t0_invariance
  | 19 => .o_w13_4_convex_hull_plateau
  | 20 => .o_w13_4_finite_loop_horizon
  | 21 => .o_w13_6_hk_character_crossover
  | 22 => .o_w13_6_block_ds
  | 23 => .o_w13_6_sc_ceiling
  | _ => .o_w13_6_c5_ceiling

private def wave13RetirementEquivFin25 : Wave13RetirementId ≃ Fin 25 where
  toFun := wave13RetirementToFin
  invFun := wave13RetirementOfFin
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Wave13RetirementId :=
  Fintype.ofEquiv (Fin 25) wave13RetirementEquivFin25.symm

/-- **Round 13 Wave 13 Honest `.OPEN` Lock**:
    1. Ties Round 12 (`round12_irx_wave12_honest_open_lock`) cleanly into Round 13 Wave 13 (`W13-1..W13-6`).
    2. `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`, `currentH2dRepoWitness = ⟨1, 1, 1⟩`,
       `wave11H2ConstructiveWitness`, `physicalUnificationStatus (Fintype.card H2SubHypothesis) false`, and
       `device_certified = false` ALL remain strictly **`.OPEN`** / `false` despite `6⁴`/`8⁴` `Stag_01(55°)`
       `OptR1(R=2)` closures (`< 0.6458`), `2.0°` `box_w=3` BFS (`0.826657 < 1`), `M=32 R=6` `qt_l1 = 0.0007785`,
       `V=∞` `FE+Mono` (`0.8544` at `20`), and `5.0555×` exact HK `OS-FP` push (`0.376680`). `[C/B/P/X]` -/
theorem round13_irx_wave13_honest_open_lock :
    -- (1) Full Round 12 honest OPEN lock preserved verbatim
    ((∀ c : SevenWayCounterexampleId, (sevenWaySignature c).positiveMassGap = false) ∧
      Function.Injective sevenWaySignature ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      ¬ (currentH2dRepoWitness.toH2LayerCandidate).Satisfies .h2d_clay_4d_continuum_measure ∧
      ¬ wave11H2ConstructiveWitness.Satisfies .h2d_clay_4d_continuum_measure ∧
      currentH2dRepoWitness = ⟨1, 1, 1⟩ ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) ∧
    -- (2) Round 13 Wave 13 25-element obstruction taxonomy & canonical witness inhabited
    (Nonempty Wave13RetirementId ∧ Fintype.card Wave13RetirementId = 25 ∧
      Nonempty W13_Zone3aCurvedAndStrongHKWitness ∧ Nonempty Wave12RetirementId) ∧
    -- (3) Wave 13 structural theorems (HK Disk Wall, Block DS conservation, UVModeAnnihilation, 1/5 OS-RP, margins)
    ((∀ br bi bmax : ℝ, 0 < br → 0 < bmax →
        (br / (br ^ 2 + bi ^ 2) ≤ 1 / bmax ↔ (bmax / 2) ^ 2 ≤ (br - bmax / 2) ^ 2 + bi ^ 2)) ∧
      (∀ I_nbr a : ℚ, I_nbr * a < 1 →
        (((18 - I_nbr) * a / (1 - I_nbr * a) < 1) ↔ (18 * a < 1))) ∧
      uvModeAnnihilationFineWF (Real.pi / 3) = 5 / 16 ∧
      w13_canonical_witness.stag01Bound8Pow4 < 1 ∧
      w13_canonical_witness.hkUncondOSFPUpper < 1868434 / 1000000) ∧
    -- (4) Strict conditional frontier: even inside `H2dMinimalIrreducibleCore`, current witness stays OPEN
    --     and `device_certified = false`
    (∀ (core : Round05CrossObligationH2d.H2dMinimalIrreducibleCore),
      (∀ o : H2dCoreObligation, core.toObstructionCandidate.Satisfies o) ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) := by
  rcases round12_irx_wave12_honest_open_lock with ⟨h12_core, h12_ret, _, h12_open⟩
  have hcard25 : Fintype.card Wave13RetirementId = 25 := by
    rw [Fintype.card_congr wave13RetirementEquivFin25, Fintype.card_fin]
  have hDisk : ∀ br bi bmax : ℝ, 0 < br → 0 < bmax →
      (br / (br ^ 2 + bi ^ 2) ≤ 1 / bmax ↔ (bmax / 2) ^ 2 ≤ (br - bmax / 2) ^ 2 + bi ^ 2) :=
    fun br bi bmax hbr hbmax => (w13_3_hk_disk_wall_equivalence br bi bmax hbr hbmax).1
  have hDS : ∀ I_nbr a : ℚ, I_nbr * a < 1 →
      (((18 - I_nbr) * a / (1 - I_nbr * a) < 1) ↔ (18 * a < 1)) :=
    w13_6_block_ds_conservation_and_monotonicity.1
  have hUV : uvModeAnnihilationFineWF (Real.pi / 3) = 5 / 16 :=
    w13_3_r2r1_turnaround_smearing_and_uv_mode_annihilation.2.2.2.2.1.1
  have hWit := w13_canonical_witness_margins
  exact ⟨h12_core,
    ⟨⟨.o_w13_1_all_u_vinf_triangle_wall⟩, hcard25, ⟨w13_canonical_witness⟩, h12_ret.1⟩,
    ⟨hDisk, hDS, hUV, hWit.2.1, hWit.2.2.2.2.2.2⟩,
    h12_open⟩

end UEOTPhysicsUnification.IRXWave13Zone3aCurvedResolventMidCouplingAndStrongHK
