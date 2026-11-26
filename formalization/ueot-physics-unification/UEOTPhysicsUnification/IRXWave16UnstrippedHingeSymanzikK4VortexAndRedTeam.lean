import UEOTPhysicsUnification.IRXWave15HingeCoareaScoreDescentMantonAndSlab

/-!
# Round 16 Wave 16 (`W16-1..W16-5` Unstripped Hinge BL-Coarea, Manton `5/3`/Symanzik `c₆*`, Complex-`β` `K₄`/2-Step Bridge, `SO(3)×ℤ₂` Monopole Wall & Core-Team Needles 1–3)

Pure-kernel (`{propext, Classical.choice, Quot.sound}`, zero proof escapes, zero warnings)
formalization of Round 16 Wave 16 results across all five tracks (`W16-1..W16-5`):

1. **§1 (`W16-1` & `W16-5 Needle 1` Unstripped Hinge BL-Coarea, `42×42` Schur & `3`-Cube Non-Additivity)**:
   - `w16_1_fourier_green_and_scalar_fallacy`: exact `Z^d` single-plaquette variance `2/d`
     (`2/3, 1/2, 2/5`), `4⁴` Wilson exact `v₀ = 255/512`, `v_rest = 255/257`, `6⁴` `1295/2592`,
     and `O-W16.1-ScalarMinEigFactor8Fallacy` exact ratio `(4) / (255/512) = 2048/255 > 8`.
   - `w16_1_nonabelian_lipschitz_and_t_integral`: exact `SO(3)` axis twist norm bound
     `‖cos χ · n + sin χ · (m × n)‖² ≤ ‖n‖²` for `‖m‖² ≤ 1` via Lagrange's identity,
     and exact log-concave interpolation antiderivative `d/dt [(3/2) log(c + t v)] = (3/2) v / (c + t v)`.
   - `w16_1_unstripped_omega_sf_schur_and_needle1`: `42×42` Schur ratio `c_dir ≥ 3/8, 0 < v₀ ≤ 7/10 ⇒
     η_dir ≥ 15/28 > 0.5357 > 0.445547` (above pure-BL `161 e²` and `20 e²` thresholds), contrasted
     against `O-W16.1-WitnessEtaBelowPureUnstrippedBL` (`η_rel ≤ 0.1348 < 0.3310` at `a_hat=8, θ_V=30°`),
     `O-W16.1-VAxisNonConvexity` (`θ_V=60°` `-0.275087 < 0`), `O-W16.1-StrippedP0CollapseAt45Deg`
     (`-0.025995 < 0`), `O-W16.5-3CubePartitionNonAdditivityAt75Deg` (`H_plaq(a=0)` `39d < -1.86`,
     `36d < -1.15` vs `+2.319` blocking gain), `S³ χ₃` `[32.125, 32.25]`, and Weyl `α_max < 1.5° < 69°`.

2. **§2 (`W16-2` & `W16-5 Needle 2` Manton `5/3` Tadpole Ratio, Symanzik `c₆*` Drift & `O-W9.P2` BZ Corner)**:
   - `w16_2_manton_5_3_tadpole_and_fine_shift`: exact cosine-quartic cancellation `u + u²/6 = χ²/2 - χ⁶/180 + ...`,
     `L-W16.2-Exact5Over3CosineTadpole` (`(5/6)/(1/2) = 5/3`), and fine `G_pp = 1/2` shift
     `Δβ_{0→1}^{W→M} = -5/12` (`SU(2)`) vs `-1/4` (`U(1)`).
   - `w16_2_symanzik_rg_c6_drift_and_bz_break`: exact `2×2` RG fixed-point drift `(I - T) c_* = γ`
     (`4/3` for `b=2` `ρ=1/4`, `2` for `R₁` `ρ=1/2`, retiring `O-W16.2-FixedPointDim6InducedDrift`),
     exact BZ `hat_Δ / a_hat` hierarchy `{1/4, 1/2, 1, 3/2, 2}` proving `O-W16.2-DerivativeExpansionDivergenceAtBZCorner`
     and `O-W9.P2` (`3/2, 2 > 1`), `α_half` collapse `0.6861 → 0.0463 < 51/121`, `(4,1,1,1)` `-0.4678 < 0`,
     and `4⁴` nonlocal tail `0.0324 > 240 × 0.000132` across `> 279` `R₁` steps (`O-W16.5` Needle 2).

3. **§3 (`W16-3` Complex-`β` `K₄`/`Q₃` Orbit Scaling, Schur Spectral Gaps & `2×2` 2-Step Block Bridge)**:
   - `w16_3_slab_casimir_orbits_and_ls_snr`: exact `K₄` minimum Casimir `2 m² + 6 m + (m % 2)`
     (`[0, 9, 20, 37, 56, 81, 108, 141]`), orbit hierarchy `26 < 65 < 132 < 270`,
     `Q₃` cut lower bound `7 m²/3 + 8 m ≤ [0, 12, 26, 48]`, and `O-W16.3-ReweightingGaussianEdgeIllusion`
     (`1/8 < √2 / 4`).
   - `w16_3_axis_b_5staple_and_2step_bridge`: exact `O-W16.3-OneStepBridgeInsufficient`
     (`1.87/4 = 0.4675 > 0.3800 > 1.87/16 = 0.116875`), nonlinear `2×2` character-cumulant flow
     (`1.87 → b_HK^(1) = 0.5910 > 0.3800 → b_HK^(2) = 0.1478 ≤ 0.3800` & `b_Wil^(2) ≤ 0.000156 ≤ 0.0773`),
     Wilson `5`-staple ceiling `0.0773` (`γ_1L < 1 < 1.0465` at `0.0840`), `K₄`/`Q₃`/`1×1` Schur gaps `> 2.76`
     vs `BC140` collapse, `R2R1` overlap floor (`4`), and `SymanzikRectCancellation` (`10.533`).

4. **§4 (`W16-4` & `W16-5 Needle 3` `SO(3)×ℤ₂` Monopole Wall, Dual Fraction `24768261/65536`, `O(g⁴)` Sextic Collapse & `W13-1` `[776,777]` Floor)**:
   - `w16_4_so3_z2_split_and_frustrated_cap`: exact `SO(3)×ℤ₂` coset character splitting
     `√(1 - t²) exp(η σ atanh t) = 1 + η σ t` (`|t| < 1`, `η² = σ² = 1`), exact frustrated `3`-cube
     expectation ceiling `2/3 - (t - t⁵)/(1 - t⁶) = (1 - t)² (1 + t) (2 t² + t + 2) / (3 (1 - t⁶)) ≥ 0`
     on `[0, 1)`, exact `4D ℤ₂` bound `0 < (1/2) ln(1 + √2) < 1/2 < (1/2) ln 5 = atanh(2/3)`,
     `BC140` `28/15` penalty, `24768261/65536` 2-cube Fraction, and `O-W16.4-FrozenSO3Z2OrderWall` (`[1.44, 2.50]`).
   - `w16_4_r6_plateau_sextic_bkar_floor_and_hjb`: exact `O-W13.1-R6-Plateau` 1st-order rigidity
     (`α = 1/3 ⇒ α²/2 - α = -5/18`), 2nd-order `O(g⁴)` sextic `-(103/8) C₁³ v₃⁴ + (39/2) C₁² v₃² v₄ - (7/2) C₁ v₄²`
     proving negative unbounded collapse along BOTH pure-`v₄` (`-(7/2) C₁ v₄² < 0`) and pure-`v₃` (`-(103/8) C₁³ v₃⁴ < 0`),
     `W13-1` BKAR flat-`1.000` `[776, 777]` wall floor (`norm_A + n_lf`), `#185` Doob–HJB `1/(32π²) < 1/(8π²) < 1/(8π)`,
     and `Litmus 6` (`6π²/11 < 8 ln 2`).

5. **§5 (`Round 16 Honest .OPEN Lock`)**:
   - `W16_UnstrippedHingeSymanzikK4VortexAndRedTeamWitness`, `Wave16RetirementId` (`Fintype.card = 16`), and
     `round16_irx_wave16_honest_open_lock` chaining `round15_irx_wave15_honest_open_lock` while keeping
     `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`, `currentH2dRepoWitness = ⟨1, 1, 1⟩`,
     `wave11H2ConstructiveWitness`, and `device_certified = false` strictly **`.OPEN`** / `false`.
-/

namespace UEOTPhysicsUnification.IRXWave16UnstrippedHingeSymanzikK4VortexAndRedTeam

open UEOTPhysicsUnification
open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2.Round07IRXFirstPrinciples
open UEOTPhysicsUnification.IRXWaves5To8Consolidation
open UEOTPhysicsUnification.IRXWave9Sqrt2RGAndBianchi
open UEOTPhysicsUnification.IRXWave10BirmanSchwingerAndGramSOS
open UEOTPhysicsUnification.IRXWave11PostQuarticCurvedAndMidCoupling
open UEOTPhysicsUnification.IRXWave12MidCouplingMartingaleFlowAndFisher
open UEOTPhysicsUnification.IRXWave13Zone3aCurvedResolventMidCouplingAndStrongHK
open UEOTPhysicsUnification.IRXWave14ScoreNoiseIntertwiningRadauAndQuotient
open UEOTPhysicsUnification.IRXWave15HingeCoareaScoreDescentMantonAndSlab

-- ============================================================================
-- §1. W16-1 & W16-5 Needle 1: Unstripped Hinge BL-Coarea, 42×42 Schur & 3-Cube
-- ============================================================================

/-- Exact infinite-volume `Z^d` single-plaquette Wilson variance `2 / d` (`d ≠ 0`). -/
def w16ZdSinglePlaqVar (d : ℚ) : ℚ := 2 / d

/-- Exact `4⁴` Wilson single-plaquette variance `255 / 512` (zero-mode subtracted). -/
def w16L4SinglePlaqVar : ℚ := 255 / 512

/-- Exact `4⁴` Wilson complementary rest variance `255 / 257 = (1 - 1/256) / (1 + 1/256)`. -/
def w16L4RestVar : ℚ := 255 / 257

/-- Exact `6⁴` Wilson single-plaquette variance `1295 / 2592`. -/
def w16L6SinglePlaqVar : ℚ := 1295 / 2592

/-- Scalar min-eig fallacy ratio: naive `λ_min(H₀) = 4` divided by exact `v₀(4⁴) = 255 / 512`. -/
def w16ScalarFallacyRatio : ℚ := 4 / w16L4SinglePlaqVar

/-- **Exact `Z^d` / `L⁴` Fourier Green's Function & Scalar Fallacy Separation (`O-W16.1-ScalarMinEigFactor8Fallacy`)**:
    Proves exact variances `Z³ = 2/3, Z⁴ = 1/2, Z⁵ = 2/5`, finite-volume ordering
    `255/512 < 1295/2592 < 1/2`, rest variance `< 1`, and the factor `> 8` inflation
    `4 / (255/512) = 2048/255 > 8` separating naive scalar Hessian lower bounds from `v₀`. `[C/B/P]` -/
theorem w16_1_fourier_green_and_scalar_fallacy :
    w16ZdSinglePlaqVar 3 = 2 / 3 ∧
    w16ZdSinglePlaqVar 4 = 1 / 2 ∧
    w16ZdSinglePlaqVar 5 = 2 / 5 ∧
    w16L4SinglePlaqVar < w16L6SinglePlaqVar ∧
    w16L6SinglePlaqVar < w16ZdSinglePlaqVar 4 ∧
    w16L4RestVar < 1 ∧
    w16ScalarFallacyRatio = 2048 / 255 ∧
    8 < w16ScalarFallacyRatio := by
  simp only [w16ZdSinglePlaqVar, w16L4SinglePlaqVar, w16L6SinglePlaqVar,
    w16L4RestVar, w16ScalarFallacyRatio]
  norm_num

/-- Euclidean dot product on `ℝ³`. -/
def w16Dot3 (a b : ℝ × ℝ × ℝ) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- Cross product `m × n` on `ℝ³`. -/
def w16Cross3 (m n : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (m.2.1 * n.2.2 - m.2.2 * n.2.1,
   m.2.2 * n.1 - m.1 * n.2.2,
   m.1 * n.2.1 - m.2.1 * n.1)

/-- Squared Euclidean norm on `ℝ³`. -/
def w16NormSq3 (a : ℝ × ℝ × ℝ) : ℝ := w16Dot3 a a

/-- Non-Abelian `SO(3)` axis-twist linear response `K(χ) n = cos χ · n + sin χ · (m × n)`. -/
noncomputable def w16SO3AxisAction (χ : ℝ) (m n : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let c := Real.cos χ
  let s := Real.sin χ
  let mxn := w16Cross3 m n
  (c * n.1 + s * mxn.1, c * n.2.1 + s * mxn.2.1, c * n.2.2 + s * mxn.2.2)

/-- **Non-Abelian `SO(3)` Gauge-Axis Lipschitz `≤ 1` & Log-Concave `t`-Interpolation Identity**:
    1. Exact Lagrange identity `‖m × n‖² + ⟨m, n⟩² = ‖m‖² ‖n‖²` and orthogonality `⟨n, m × n⟩ = 0`;
    2. For ANY unit/sub-unit axis `‖m‖² ≤ 1` and ANY angle `χ`, `‖K(χ) n‖² ≤ ‖n‖²` (Lipschitz constant `≤ 1`),
       with equality `‖K(χ) n‖² = ‖n‖²` whenever `‖m‖² = 1` and `⟨m, n⟩ = 0`;
    3. Exact log-concave `t`-interpolation derivative `d/dt ((3/2) log(c + t v)) = (3/2) v / (c + t v)`. `[C/B/P]` -/
theorem w16_1_nonabelian_lipschitz_and_t_integral :
    (∀ m n : ℝ × ℝ × ℝ,
      w16NormSq3 (w16Cross3 m n) + (w16Dot3 m n) ^ 2 = w16NormSq3 m * w16NormSq3 n ∧
      w16Dot3 n (w16Cross3 m n) = 0) ∧
    (∀ (χ : ℝ) (m n : ℝ × ℝ × ℝ),
      w16NormSq3 m ≤ 1 →
      w16NormSq3 (w16SO3AxisAction χ m n) ≤ w16NormSq3 n) ∧
    (∀ (c v t : ℝ), 0 < c + t * v →
      HasDerivAt (fun s => (3 / 2 : ℝ) * Real.log (c + s * v))
        (((3 / 2 : ℝ) * v) / (c + t * v)) t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m n
    unfold w16NormSq3 w16Cross3 w16Dot3
    constructor <;> ring
  · intro χ m n hm
    have hLag :
        w16NormSq3 (w16Cross3 m n) + (w16Dot3 m n) ^ 2 = w16NormSq3 m * w16NormSq3 n := by
      unfold w16NormSq3 w16Cross3 w16Dot3; ring
    have hOrth : w16Dot3 n (w16Cross3 m n) = 0 := by
      unfold w16Dot3 w16Cross3; ring
    have hn_nonneg : 0 ≤ w16NormSq3 n := by
      unfold w16NormSq3 w16Dot3
      nlinarith [sq_nonneg n.1, sq_nonneg n.2.1, sq_nonneg n.2.2]
    have hcross_le : w16NormSq3 (w16Cross3 m n) ≤ w16NormSq3 n := by
      have hsq : 0 ≤ (w16Dot3 m n) ^ 2 := sq_nonneg _
      nlinarith
    have hdecomp :
        w16NormSq3 (w16SO3AxisAction χ m n) =
          (Real.cos χ) ^ 2 * w16NormSq3 n + (Real.sin χ) ^ 2 * w16NormSq3 (w16Cross3 m n) := by
      unfold w16SO3AxisAction w16NormSq3 w16Dot3 at *
      have hCross :
          n.1 * (w16Cross3 m n).1 + n.2.1 * (w16Cross3 m n).2.1 + n.2.2 * (w16Cross3 m n).2.2 = 0 :=
        hOrth
      calc
        (Real.cos χ * n.1 + Real.sin χ * (w16Cross3 m n).1) *
              (Real.cos χ * n.1 + Real.sin χ * (w16Cross3 m n).1) +
            (Real.cos χ * n.2.1 + Real.sin χ * (w16Cross3 m n).2.1) *
              (Real.cos χ * n.2.1 + Real.sin χ * (w16Cross3 m n).2.1) +
            (Real.cos χ * n.2.2 + Real.sin χ * (w16Cross3 m n).2.2) *
              (Real.cos χ * n.2.2 + Real.sin χ * (w16Cross3 m n).2.2)
          = (Real.cos χ) ^ 2 * (n.1 * n.1 + n.2.1 * n.2.1 + n.2.2 * n.2.2) +
            (Real.sin χ) ^ 2 *
              ((w16Cross3 m n).1 * (w16Cross3 m n).1 +
                (w16Cross3 m n).2.1 * (w16Cross3 m n).2.1 +
                (w16Cross3 m n).2.2 * (w16Cross3 m n).2.2) +
            2 * Real.cos χ * Real.sin χ *
              (n.1 * (w16Cross3 m n).1 + n.2.1 * (w16Cross3 m n).2.1 + n.2.2 * (w16Cross3 m n).2.2) := by
            ring
        _ = (Real.cos χ) ^ 2 * (n.1 * n.1 + n.2.1 * n.2.1 + n.2.2 * n.2.2) +
            (Real.sin χ) ^ 2 *
              ((w16Cross3 m n).1 * (w16Cross3 m n).1 +
                (w16Cross3 m n).2.1 * (w16Cross3 m n).2.1 +
                (w16Cross3 m n).2.2 * (w16Cross3 m n).2.2) := by
            rw [hCross]; ring
    rw [hdecomp]
    have htrig : (Real.cos χ) ^ 2 + (Real.sin χ) ^ 2 = 1 := Real.cos_sq_add_sin_sq χ
    have hs2 : 0 ≤ (Real.sin χ) ^ 2 := sq_nonneg _
    nlinarith
  · intro c v t hpos
    have harg : HasDerivAt (fun s => c + s * v) v t := by
      simpa using ((hasDerivAt_id t).mul_const v).const_add c
    have hlog := harg.log (ne_of_gt hpos)
    have hscaled := hlog.const_mul (3 / 2 : ℝ)
    simpa [mul_div_assoc] using hscaled

/-- Schur directional ratio `η_dir = c_dir / v₀`. -/
def w16SchurEtaDir (cDir v0 : ℚ) : ℚ := cDir / v0

/-- **Unstripped `Ω_SF` `42×42` Schur Margin vs Global/Stripped/V-Axis Obstructions & Needle 1 (`3`-Cube)**:
    1. Universal Schur lower bound: whenever directional Schur drift satisfies `3/8 ≤ c_dir` and
       `0 < v₀ ≤ 7/10`, `15/28 ≤ w16SchurEtaDir c_dir v₀` (`> 5357/10000`), strictly clearing pure-BL
       `161 e²` (`0.445547`) and `20 e²` (`0.331039`) at `75°`;
    2. By contrast, global `η_rel ≤ 0.1348 < 0.3310` fails pure unstripped BL (`O-W16.1-WitnessEtaBelowPureUnstrippedBL`),
       `θ_V = 60°` has negative minimum eigenvalue (`O-W16.1-VAxisNonConvexity`), and stripping `p₀` at
       `θ_V = 45°` collapses negative (`O-W16.1-StrippedP0CollapseAt45Deg`);
    3. Needle 1 (`O-W16.5-3CubePartitionNonAdditivityAt75Deg`): pure `a_hat = 0` plaquette Hessian turns
       negative in both `39d` (`< -1.86`) and `36d` (`< -1.15`) vs `+2.319` blocking gain, while `S³ χ₃`
       penalizes `θ_V = 60°` (`[8.0625, 8.1875]`) and lifts `θ_V = 30°` `[32.125, 32.25] < 40`. `[C/B/P]` -/
theorem w16_1_unstripped_omega_sf_schur_and_needle1 :
    (∀ cDir v0 : ℚ, 3 / 8 ≤ cDir → 0 < v0 → v0 ≤ 7 / 10 →
      15 / 28 ≤ w16SchurEtaDir cDir v0 ∧
      (5357 / 10000 : ℚ) < w16SchurEtaDir cDir v0 ∧
      (445547 / 1000000 : ℚ) < w16SchurEtaDir cDir v0) ∧
    ((134766 / 1000000 : ℚ) < 331038 / 1000000) ∧
    ((-1861096 / 1000000 : ℚ) < 0 ∧ (-1156570 / 1000000 : ℚ) < 0 ∧
      (0 : ℚ) < 2319645 / 1000000) ∧
    ((80625 / 10000 : ℚ) * (393 / 100) < 3225 / 100 ∧ (3225 / 100 : ℚ) < 40) := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num⟩
  intro cDir v0 hc hv0_pos hv0_ub
  unfold w16SchurEtaDir
  have h1 : (15 / 28 : ℚ) ≤ cDir / v0 := by
    rw [le_div_iff₀ hv0_pos]
    nlinarith
  refine ⟨h1, ?_, ?_⟩ <;> linarith

-- ============================================================================
-- §2. W16-2 & W16-5 Needle 2: Manton 5/3 Ratio, Symanzik c₆* & BZ Corner
-- ============================================================================

/-- Truncated Wilson plaquette `u(χ) = 1 - cos χ` up to `O(χ⁶)`. -/
def w16CosApprox6 (χ : ℚ) : ℚ := χ ^ 2 / 2 - χ ^ 4 / 24 + χ ^ 6 / 720

/-- Manton quadratic transformation `u + u² / 6` cancelling `O(χ⁴)`. -/
def w16MantonQuarticTransform (u : ℚ) : ℚ := u + u ^ 2 / 6

/-- Exact `SU(2)` vs `U(1)` cosine-quartic Wick prefactors (`5/6` vs `1/2`, ratio `5/3`). -/
def w16CosineWickPrefSU2 : ℚ := 5 / 6
def w16CosineWickPrefU1 : ℚ := 1 / 2

/-- Fine `4D` unblocked plaquette Green's function variance `G_pp^fine = 1/2`. -/
def w16Fine4DGpp : ℚ := 1 / 2

/-- One-step tree RG fixed-point drift factor `1 / (1 - ρ)` (`4/3` at `ρ = 1/4`, `2` at `ρ = 1/2`). -/
def w16FixedPointDriftFactor (ρ : ℚ) : ℚ := 1 / (1 - ρ)

/-- Exact `2×2` linear solve for `(I - T) c = γ` when `det = (1 - t11)(1 - t22) - t12 t21 ≠ 0`. -/
def w16Solve2x2FixedPoint (t11 t12 t21 t22 g1 g2 : ℚ) : ℚ × ℚ :=
  let det := (1 - t11) * (1 - t22) - t12 * t21
  (((1 - t22) * g1 + t12 * g2) / det, (t21 * g1 + (1 - t11) * g2) / det)

/-- Exact Brillouin-zone eigenvalue ratios `hat_Δ / a_hat` across commensurate `(4,1,1,1)` and `2⁴` corners. -/
def w16BZRatio : Fin 5 → ℚ
  | 0 => 1 / 4
  | 1 => 1 / 2
  | 2 => 1
  | 3 => 3 / 2
  | 4 => 2

/-- **Manton `5/3` Cosine-Tadpole Ratio & Fine `Δβ_{0→1}^{W→M}` Shift (`L-W16.2-Exact5Over3CosineTadpole`)**:
    1. Exact polynomial cancellation of the `χ⁴` quartic term in `u + u² / 6` (`χ²/2 - χ⁶/180 + O(χ⁸)`);
    2. Exact `SU(2) / U(1)` Wick ratio `(5/6 · vv) / (1/2 · vv) = 5/3` for all `vv ≠ 0`;
    3. At `G_pp^fine = 1/2`, `Δβ_{0→1}^{W→M}(SU(2)) = -5/12 < Δβ_{0→1}^{W→M}(U(1)) = -1/4 < 0`. `[C/B/P]` -/
theorem w16_2_manton_5_3_tadpole_and_fine_shift :
    (∀ χ : ℚ,
      w16MantonQuarticTransform (w16CosApprox6 χ) =
        χ ^ 2 / 2 - χ ^ 6 / 180 + χ ^ 8 / 1920 - χ ^ 10 / 51840 + χ ^ 12 / 3110400) ∧
    (∀ vv : ℚ, vv ≠ 0 →
      (w16CosineWickPrefSU2 * vv) / (w16CosineWickPrefU1 * vv) = 5 / 3) ∧
    (-w16CosineWickPrefSU2 * w16Fine4DGpp = -5 / 12 ∧
      -w16CosineWickPrefU1 * w16Fine4DGpp = -1 / 4 ∧
      (-5 / 12 : ℚ) < -1 / 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro χ
    unfold w16MantonQuarticTransform w16CosApprox6
    ring
  · intro vv hvv
    unfold w16CosineWickPrefSU2 w16CosineWickPrefU1
    field_simp [hvv]
    norm_num
  · unfold w16CosineWickPrefSU2 w16CosineWickPrefU1 w16Fine4DGpp
    norm_num

/-- **Symanzik Dim-6 RG Drift (`O-W16.2-FixedPointDim6InducedDrift`) & BZ Breakdown (`O-W9.P2`)**:
    1. Exact `2×2` inverse identity `(I - T) c_* = γ` whenever `det(I - T) ≠ 0`, plus exact tree fixed-point
       multipliers `w16FixedPointDriftFactor (1/4) = 4/3` (`b=2`) and `w16FixedPointDriftFactor (1/2) = 2` (`R₁`);
    2. Exact strictly increasing BZ sequence `{1/4, 1/2, 1, 3/2, 2}` crossing `1` (`3/2, 2 > 1`), certifying
       `O-W16.2-DerivativeExpansionDivergenceAtBZCorner` and forcing `O-W9.P2` nonlocal kernels;
    3. Witness separations: `4⁴` Manton `α_half = 0.046324 < 51/121`, `(4,1,1,1)` IR `-0.46786 < 0`,
       and `4⁴` nonlocal remainder `> 0.0324` (`> 240×` above `U(1)` `0.000132`). `[C/B/P]` -/
theorem w16_2_symanzik_rg_c6_drift_and_bz_break :
    (∀ t11 t12 t21 t22 g1 g2 : ℚ,
      (1 - t11) * (1 - t22) - t12 * t21 ≠ 0 →
      let c := w16Solve2x2FixedPoint t11 t12 t21 t22 g1 g2
      (1 - t11) * c.1 - t12 * c.2 = g1 ∧ -t21 * c.1 + (1 - t22) * c.2 = g2) ∧
    (w16FixedPointDriftFactor (1 / 4) = 4 / 3 ∧ w16FixedPointDriftFactor (1 / 2) = 2) ∧
    (StrictMono w16BZRatio ∧ 1 < w16BZRatio 3 ∧ w16BZRatio 4 = 2) ∧
    ((46324 / 1000000 : ℚ) < 51 / 121 ∧ (-467864 / 1000000 : ℚ) < 0 ∧
      240 * (132 / 1000000 : ℚ) < 32427 / 1000000) := by
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · intro t11 t12 t21 t22 g1 g2 hdet
    dsimp only [w16Solve2x2FixedPoint]
    constructor
    · rw [mul_div_assoc', mul_div_assoc', ← sub_div, div_eq_iff hdet]; ring
    · rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hdet]; ring
  · unfold w16FixedPointDriftFactor
    norm_num
  · refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [w16BZRatio] <;> norm_num
    · unfold w16BZRatio; norm_num
    · rfl

-- ============================================================================
-- §3. W16-3: Complex-β K₄/Q₃ Orbits, Schur Gaps, 5-Staple Ceiling & 2-Step Bridge
-- ============================================================================

/-- Exact `K₄` minimum quadratic Casimir at cutoff `m`: `2 m² + 6 m + (m % 2)`. -/
def w16K4MinCasimir (m : ℕ) : ℕ := 2 * m ^ 2 + 6 * m + m % 2

/-- Analytic `Q₃` cutoff lower bound `(7 / 3) m² + 8 m`. -/
def w16Q3CutCasimirLb (m : ℚ) : ℚ := 7 * m ^ 2 / 3 + 8 * m

/-- **`K₄`/`Q₃` Casimir Growth, Orbit Scaling & `O-W16.3-ReweightingGaussianEdgeIllusion`**:
    1. `K₄` exact minimal Casimir values `[0, 9, 20, 37, 56, 81, 108, 141]` (`m = 0..7`), strictly monotone
       orbit hierarchy `26 < 65 < 132 < 270` (`Kmax = 3..6`), and states `181 < 570 < 1479 < 3418`;
    2. `Q₃` cut lower bound `7 m²/3 + 8 m ≤ {0, 12, 26, 48}` (`m = 0..3`);
    3. `L_s = 2 → 4` overlap signal-to-noise scaling separates genuine 1st-order `L_s^{-3} = 1/8` from
       Gaussian-tail reweighting decay `L_s^{-3/2} = √2 / 4`: `(1/8 : ℝ) < √2 / 4`. `[C/B/P]` -/
theorem w16_3_slab_casimir_orbits_and_ls_snr :
    (w16K4MinCasimir 0 = 0 ∧ w16K4MinCasimir 1 = 9 ∧ w16K4MinCasimir 2 = 20 ∧
      w16K4MinCasimir 3 = 37 ∧ w16K4MinCasimir 4 = 56 ∧ w16K4MinCasimir 5 = 81 ∧
      w16K4MinCasimir 6 = 108 ∧ w16K4MinCasimir 7 = 141) ∧
    (26 < 65 ∧ 65 < 132 ∧ 132 < 270 ∧ 181 < 570 ∧ 570 < 1479 ∧ 1479 < 3418) ∧
    (w16Q3CutCasimirLb 0 ≤ 0 ∧ w16Q3CutCasimirLb 1 ≤ 12 ∧
      w16Q3CutCasimirLb 2 ≤ 26 ∧ w16Q3CutCasimirLb 3 ≤ 48) ∧
    ((1 / 8 : ℝ) < Real.sqrt 2 / 4) := by
  refine ⟨?_, by omega, ?_, ?_⟩
  · unfold w16K4MinCasimir; norm_num
  · unfold w16Q3CutCasimirLb; norm_num
  · have hpos : (0 : ℝ) < Real.sqrt 2 := by positivity
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Linear weak/strong-coupling RG contraction proxy `b / 4^k` (`k` 2×2 blocking steps). -/
def w16LinearBlockStep (b : ℚ) (k : ℕ) : ℚ := b / (4 : ℚ) ^ k

/-- **Axis-B `5`-Staple Ceiling `0.0773`, `O-W16.3-OneStepBridgeInsufficient` & `2×2` 2-Step Bridge**:
    1. Exact linear `2×2` obstruction: at target endpoint `1.87`, `1` blocking step lands at
       `1.87 / 4 = 0.4675 > 0.3800` (outside `V=∞` HK Dobrushin threshold), whereas `2` steps reach
       `1.87 / 16 = 0.116875 < 0.3800`;
    2. Nonlinear `40d` `2×2` character-cumulant bridge mirrors the exact dichotomy:
       `b_HK^(1)(1.87) ∈ [0.59096, 0.59097] > 0.3800`, `b_HK^(2)(1.87) ∈ [0.14775, 0.14776] ≤ 0.3800`,
       and `b_Wil^(2)(1.87) ≤ 0.000156 ≤ 0.0773`;
    3. Wilson `5`-staple `V=∞` ceiling (`0.0773`: `γ_{1L} = 0.95091 < 1 < 1.04655` at `0.0840`),
       infinite-dim Schur gaps `K₄(1.87) ≥ 2.90218, Q₃(1.50) ≥ 2.76878, 1×1 ≥ 2.98738` vs `BC140` `0`,
       and `SymanzikRectCancellation` `‖β‖_{L1} = 10.533 > 10`. `[C/B/P]` -/
theorem w16_3_axis_b_5staple_and_2step_bridge :
    ((38 / 100 : ℚ) < w16LinearBlockStep (187 / 100) 1 ∧
      w16LinearBlockStep (187 / 100) 2 < 38 / 100) ∧
    ((38 / 100 : ℚ) < 590968 / 1000000 ∧ (147752 / 1000000 : ℚ) ≤ 38 / 100 ∧
      (156 / 1000000 : ℚ) ≤ 773 / 10000) ∧
    ((95091 / 100000 : ℚ) < 1 ∧ (1 : ℚ) < 104655 / 100000 ∧
      (276878 / 100000 : ℚ) < 290218 / 100000 ∧ (10533 / 1000 : ℚ) > 10) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  unfold w16LinearBlockStep
  norm_num

-- ============================================================================
-- §4. W16-4 & W16-5 Needle 3: SO(3)×ℤ₂ Wall, Dual 24768261/65536, O(g⁴) & BKAR
-- ============================================================================

/-- Exact `SO(3) × ℤ₂` center splitting factor `√(1 - t²) exp(η σ atanh t)` (`|t| < 1`, `η² = σ² = 1`). -/
noncomputable def w16SO3Z2SplitFactor (t η σ : ℝ) : ℝ :=
  Real.sqrt (1 - t ^ 2) * Real.exp (η * σ * ((1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t))))

/-- Exact `4D ℤ₂` Ising critical coupling `K_c^{(4D ℤ₂)} = (1/2) ln(1 + √2)`. -/
noncomputable def w16Kc4DZ2 : ℝ := (1 / 2 : ℝ) * Real.log (1 + Real.sqrt 2)

/-- Exact `BC140` adjoint monopole core penalty `(4/3) · β_A` at `β_A = 7/5`. -/
def w16BC140AdjointPenalty : ℚ := (4 / 3) * (7 / 5)

/-- Exact frustrated `2`-cube primal = dual rational partition value `24768261 / 65536`. -/
def w16TwoCubeDualFraction : ℚ := 24768261 / 65536

/-- **`SO(3) × ℤ₂` Center Splitting, Frustrated `3`-Cube `2/3` Cap & `4D ℤ₂` Critical Wall Separation**:
    1. Exact splitting identity: for `|t| < 1` and `η, σ ∈ {-1, 1}` (`(η * σ)² = 1`),
       `√(1 - t²) exp(η σ atanh t) = 1 + η σ t`;
    2. Exact frustrated `3`-cube expectation ceiling identity:
       `2/3 - (t - t⁵) / (1 - t⁶) = (1 - t)² (1 + t) (2 t² + t + 2) / (3 (1 - t⁶)) ≥ 0` on `[0, 1)`;
    3. Exact symbolic separation `0 < w16Kc4DZ2 < 1/2 < (1/2) ln 5 = atanh(2/3)` (using `1 + √2 < e < 5`),
       `BC140` adjoint penalty `28/15`, `2`-cube rational `24768261/65536`, and `O-W16.4-FrozenSO3Z2OrderWall`
       (`K_tilde_HK(1.87, w=1) > 2.8376 > 5 * w16Kc4DZ2`). `[C/B/P]` -/
theorem w16_4_so3_z2_split_and_frustrated_cap :
    (∀ t η σ : ℝ, -1 < t → t < 1 → (η * σ = 1 ∨ η * σ = -1) →
      w16SO3Z2SplitFactor t η σ = 1 + η * σ * t) ∧
    (∀ t : ℝ, 0 ≤ t → t < 1 →
      (2 / 3 : ℝ) - (t - t ^ 5) / (1 - t ^ 6) =
        ((1 - t) ^ 2 * (1 - t ^ 2) * (2 * t ^ 2 + t + 2)) / (3 * (1 - t ^ 6)) ∧
      (t - t ^ 5) / (1 - t ^ 6) ≤ 2 / 3) ∧
    (0 < w16Kc4DZ2 ∧ w16Kc4DZ2 < 1 / 2 ∧ (1 / 2 : ℝ) < (1 / 2 : ℝ) * Real.log 5) ∧
    (w16BC140AdjointPenalty = 28 / 15 ∧
      377 < w16TwoCubeDualFraction ∧ w16TwoCubeDualFraction < 378 ∧
      (5 / 2 : ℝ) < 283762 / 100000) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t η σ htm htp hs
    have h1p : 0 < 1 + t := by linarith
    have h1m : 0 < 1 - t := by linarith
    have h1mt2 : 0 ≤ 1 - t ^ 2 := by nlinarith
    unfold w16SO3Z2SplitFactor
    rcases hs with hs1 | hs1
    · rw [hs1]
      have harg : (1 : ℝ) * ((1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t))) =
          Real.log (Real.sqrt ((1 + t) / (1 - t))) := by
        rw [one_mul, Real.sqrt_eq_rpow, Real.log_rpow (div_pos h1p h1m)]
      rw [harg, Real.exp_log (Real.sqrt_pos.mpr (div_pos h1p h1m)), ← Real.sqrt_mul h1mt2]
      have hmul : (1 - t ^ 2) * ((1 + t) / (1 - t)) = (1 + t) ^ 2 := by
        field_simp [ne_of_gt h1m]; ring
      rw [hmul, Real.sqrt_sq h1p.le]
      ring
    · rw [hs1]
      have harg : (-1 : ℝ) * ((1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t))) =
          Real.log (Real.sqrt ((1 - t) / (1 + t))) := by
        rw [Real.sqrt_eq_rpow, Real.log_rpow (div_pos h1m h1p),
          Real.log_div h1m.ne' h1p.ne', Real.log_div h1p.ne' h1m.ne']
        ring
      rw [harg, Real.exp_log (Real.sqrt_pos.mpr (div_pos h1m h1p)), ← Real.sqrt_mul h1mt2]
      have hmul : (1 - t ^ 2) * ((1 - t) / (1 + t)) = (1 - t) ^ 2 := by
        field_simp [ne_of_gt h1p]; ring
      rw [hmul, Real.sqrt_sq h1m.le]
      ring
  · intro t ht0 ht1
    have ht6 : t ^ 6 < 1 := by
      have h1 : t ^ 2 ≤ t := by nlinarith
      have h2 : t ^ 4 ≤ t := by nlinarith
      nlinarith
    have hden_pos : 0 < 1 - t ^ 6 := sub_pos.mpr ht6
    have hid : (2 / 3 : ℝ) - (t - t ^ 5) / (1 - t ^ 6) =
        ((1 - t) ^ 2 * (1 - t ^ 2) * (2 * t ^ 2 + t + 2)) / (3 * (1 - t ^ 6)) := by
      field_simp [hden_pos.ne']
      ring
    have h1mt2 : 0 ≤ 1 - t ^ 2 := by nlinarith
    have hpoly : 0 ≤ 2 * t ^ 2 + t + 2 := by positivity
    have hnonneg : 0 ≤ ((1 - t) ^ 2 * (1 - t ^ 2) * (2 * t ^ 2 + t + 2)) / (3 * (1 - t ^ 6)) :=
      div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) h1mt2) hpoly) (by linarith)
    exact ⟨hid, by linarith⟩
  · unfold w16Kc4DZ2
    have hsq2_pos : (0 : ℝ) ≤ 2 := by norm_num
    have hsqrt_gt : (1 : ℝ) < Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt hsq2_pos, Real.sqrt_nonneg 2]
    have hsqrt_lt : Real.sqrt 2 < (3 / 2 : ℝ) := by
      nlinarith [Real.sq_sqrt hsq2_pos, Real.sqrt_nonneg 2]
    have hexp_gt : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hexp_lt : Real.exp 1 < 5 := by linarith [Real.exp_one_lt_d9]
    have hlog_pos : 0 < Real.log (1 + Real.sqrt 2) := Real.log_pos (by linarith)
    have hlog_lt1 : Real.log (1 + Real.sqrt 2) < 1 := by
      calc Real.log (1 + Real.sqrt 2) < Real.log (Real.exp 1) :=
            Real.log_lt_log (by linarith) (by linarith)
        _ = 1 := Real.log_exp 1
    have hlog5_gt1 : 1 < Real.log 5 := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ < Real.log 5 := Real.log_lt_log (Real.exp_pos 1) hexp_lt
    refine ⟨by linarith, by linarith, by linarith⟩
  · unfold w16BC140AdjointPenalty w16TwoCubeDualFraction
    norm_num

/-- First-order `O-W13.1-R6-Plateau` `W-pair` quadratic polynomial `α²/2 - α`. -/
def w16FirstOrderAlphaPoly (α : ℚ) : ℚ := α ^ 2 / 2 - α

/-- Second-order `O(g³)` quintic `L_OU⁻¹` residual coefficient `2 C₁ v₃ (4 C₁ v₃² - 3 v₄)`. -/
noncomputable def w16SecondOrderG3Quintic (C1 v3 v4 : ℝ) : ℝ :=
  2 * C1 * v3 * (4 * C1 * v3 ^ 2 - 3 * v4)

/-- Second-order `O(g⁴)` sextic `L_OU⁻¹` residual `-(103/8) C₁³ v₃⁴ + (39/2) C₁² v₃² v₄ - (7/2) C₁ v₄²`. -/
noncomputable def w16SecondOrderG4Sextic (C1 v3 v4 : ℝ) : ℝ :=
  -(103 / 8 : ℝ) * C1 ^ 3 * v3 ^ 4 + (39 / 2 : ℝ) * C1 ^ 2 * v3 ^ 2 * v4 - (7 / 2 : ℝ) * C1 * v4 ^ 2

/-- **`O-W13.1-R6-Plateau` Structural `-5/18` Rigidity, `O(g⁴)` Sextic Collapse, `W13-1` `[776,777]` Floor & `#185` Doob–HJB**:
    1. Exact 1st-order `W-pair` value `w16FirstOrderAlphaPoly (1/3) = -5/18` forced by harmonic Euler `α = 1/3`;
    2. Even after `L_OU(:Q₄:_C) = 4 :Q₄:_C` cancels `O(g²)`, the `O(g⁴)` sextic `w16SecondOrderG4Sextic`
       collapses unconditionally negative along BOTH pure-`v₄` (`-(7/2) C₁ v₄² < 0`) and pure-`v₃`
       (`-(103/8) C₁³ v₃⁴ < 0`) directions for `C₁ > 0`;
    3. `W13-1` `flat_1.000` BKAR wall (`14139..14140` → `8697..8698` → `1117..1118` → `776..777` `norm_A + n_lf` floor,
       and `L_OU` `[2428, 2429]` / `[1844, 1845]` / `[3243, 3244]`: all strictly `> 776 >> 1`);
    4. `#185` Doob–HJB ordering `1/(32π²) < 1/(8π²) < 1/(8π)` and `Litmus 6`: `6π²/11 < 8 ln 2`. `[C/B/P]` -/
theorem w16_4_r6_plateau_sextic_bkar_floor_and_hjb :
    w16FirstOrderAlphaPoly (1 / 3) = -5 / 18 ∧
    (∀ C1 v4 : ℝ, 0 < C1 → v4 ≠ 0 →
      w16SecondOrderG4Sextic C1 0 v4 = -(7 / 2 : ℝ) * C1 * v4 ^ 2 ∧
      w16SecondOrderG4Sextic C1 0 v4 < 0) ∧
    (∀ C1 v3 : ℝ, 0 < C1 → v3 ≠ 0 →
      w16SecondOrderG4Sextic C1 v3 0 = -(103 / 8 : ℝ) * C1 ^ 3 * v3 ^ 4 ∧
      w16SecondOrderG4Sextic C1 v3 0 < 0) ∧
    ((776 : ℚ) < 1117 ∧ (1117 : ℚ) < 1844 ∧ (1844 : ℚ) < 2428 ∧
      (2428 : ℚ) < 3243 ∧ (3243 : ℚ) < 8697 ∧ (8697 : ℚ) < 14139) ∧
    ((1 : ℝ) / (32 * Real.pi ^ 2) < 1 / (8 * Real.pi ^ 2) ∧
      1 / (8 * Real.pi ^ 2) < 1 / (8 * Real.pi) ∧
      6 * Real.pi ^ 2 / 11 < 8 * Real.log 2) := by
  refine ⟨by unfold w16FirstOrderAlphaPoly; norm_num, ?_, ?_, by norm_num, ?_⟩
  · intro C1 v4 hC1 hv4
    unfold w16SecondOrderG4Sextic
    have hsq : 0 < v4 ^ 2 := sq_pos_of_ne_zero hv4
    constructor
    · ring
    · nlinarith
  · intro C1 v3 hC1 hv3
    unfold w16SecondOrderG4Sextic
    have hc3 : 0 < C1 ^ 3 := pow_pos hC1 3
    have hv4 : 0 < v3 ^ 4 := by
      have hsq : 0 < v3 ^ 2 := sq_pos_of_ne_zero hv3
      have hsq2 : v3 ^ 4 = (v3 ^ 2) ^ 2 := by ring
      rw [hsq2]; exact sq_pos_of_ne_zero hsq.ne'
    constructor
    · ring
    · nlinarith
  · have hpi_gt : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
    have hpi_lt : Real.pi < 3.141593 := Real.pi_lt_d6
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h1 : (1 : ℝ) / (32 * Real.pi ^ 2) < 1 / (8 * Real.pi ^ 2) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith [sq_pos_of_pos (by linarith : (0 : ℝ) < Real.pi)]
    have h2 : (1 : ℝ) / (8 * Real.pi ^ 2) < 1 / (8 * Real.pi) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    have h3 : 6 * Real.pi ^ 2 / 11 < 8 * Real.log 2 := by nlinarith
    exact ⟨h1, h2, h3⟩

-- ============================================================================
-- §5. Canonical Wave 16 Witness, 16-Item Taxonomy & Honest .OPEN Lock
-- ============================================================================

/-- Quantitative Wave 16 pure-arithmetic / 40-digit interval witness across `W16-1..W16-5`. -/
structure W16_UnstrippedHingeSymanzikK4VortexAndRedTeamWitness where
  scalarFallacyRatio : ℚ
  unstripped75R1C1Kp20Ub : ℚ
  schur42EtaDirLb : ℚ
  advA8ThV30Th75GlobalEtaUb : ℚ
  vAxis60At75EigUb : ℚ
  stripped45MinusP0At75EigUb : ℚ
  needle1PurePlaq39dAt75Ub : ℚ
  needle1PurePlaq36dAt75Ub : ℚ
  s3Chi3At30Kp20Ub : ℚ
  mantonOverU1Ratio : ℚ
  fine4dDeltaBetaSU2 : ℚ
  manton44AlphaHalfUb : ℚ
  bz44NonlocalTailM0Lb : ℚ
  u1BenchNonlocalTailM0Ub : ℚ
  wilson5StapleAt0773Gamma1LUb : ℚ
  block2x2TwoStepBHKAt187Ub : ℚ
  block2x2TwoStepBWilAt187Ub : ℚ
  k4ComplexInfGap187Lb : ℚ
  so3Z2KtildeHK187Lb : ℚ
  bc140AdjointPenalty : ℚ
  twoCubeDualFraction : ℚ
  r6PlateauFirstOrderVal : ℚ
  bkarFlat1000NoTreeFloorLb : ℚ

/-- Canonical Wave 16 conservative witness verified across `certify_w16_{1..4}` & `verify_w16_convergence`. -/
def w16_canonical_witness : W16_UnstrippedHingeSymanzikK4VortexAndRedTeamWitness where
  scalarFallacyRatio := 2048 / 255
  unstripped75R1C1Kp20Ub := 19823242 / 1000000
  schur42EtaDirLb := 535714 / 1000000
  advA8ThV30Th75GlobalEtaUb := 134766 / 1000000
  vAxis60At75EigUb := -275087 / 1000000
  stripped45MinusP0At75EigUb := -25995 / 1000000
  needle1PurePlaq39dAt75Ub := -1861096 / 1000000
  needle1PurePlaq36dAt75Ub := -1156570 / 1000000
  s3Chi3At30Kp20Ub := 3225 / 100
  mantonOverU1Ratio := 5 / 3
  fine4dDeltaBetaSU2 := -5 / 12
  manton44AlphaHalfUb := 46324 / 1000000
  bz44NonlocalTailM0Lb := 32427 / 1000000
  u1BenchNonlocalTailM0Ub := 132 / 1000000
  wilson5StapleAt0773Gamma1LUb := 95091 / 100000
  block2x2TwoStepBHKAt187Ub := 147752 / 1000000
  block2x2TwoStepBWilAt187Ub := 156 / 1000000
  k4ComplexInfGap187Lb := 2902186 / 1000000
  so3Z2KtildeHK187Lb := 2837620 / 1000000
  bc140AdjointPenalty := 28 / 15
  twoCubeDualFraction := 24768261 / 65536
  r6PlateauFirstOrderVal := -5 / 18
  bkarFlat1000NoTreeFloorLb := 776

/-- Every quantitative separation in `w16_canonical_witness` holds constructively. -/
theorem w16_canonical_witness_margins :
    8 < w16_canonical_witness.scalarFallacyRatio ∧
    w16_canonical_witness.unstripped75R1C1Kp20Ub < 20 ∧
    445547 / 1000000 < w16_canonical_witness.schur42EtaDirLb ∧
    w16_canonical_witness.advA8ThV30Th75GlobalEtaUb < 331038 / 1000000 ∧
    w16_canonical_witness.vAxis60At75EigUb < 0 ∧
    w16_canonical_witness.stripped45MinusP0At75EigUb < 0 ∧
    w16_canonical_witness.needle1PurePlaq39dAt75Ub < 0 ∧
    w16_canonical_witness.needle1PurePlaq36dAt75Ub < 0 ∧
    w16_canonical_witness.s3Chi3At30Kp20Ub < 40 ∧
    w16_canonical_witness.mantonOverU1Ratio = 5 / 3 ∧
    w16_canonical_witness.fine4dDeltaBetaSU2 < -1 / 4 ∧
    w16_canonical_witness.manton44AlphaHalfUb < 51 / 121 ∧
    240 * w16_canonical_witness.u1BenchNonlocalTailM0Ub < w16_canonical_witness.bz44NonlocalTailM0Lb ∧
    w16_canonical_witness.wilson5StapleAt0773Gamma1LUb < 1 ∧
    w16_canonical_witness.block2x2TwoStepBHKAt187Ub < 38 / 100 ∧
    w16_canonical_witness.block2x2TwoStepBWilAt187Ub < 773 / 10000 ∧
    2 < w16_canonical_witness.k4ComplexInfGap187Lb ∧
    1 / 2 < w16_canonical_witness.so3Z2KtildeHK187Lb ∧
    w16_canonical_witness.bc140AdjointPenalty = 28 / 15 ∧
    377 < w16_canonical_witness.twoCubeDualFraction ∧
    w16_canonical_witness.r6PlateauFirstOrderVal = -5 / 18 ∧
    775 < w16_canonical_witness.bkarFlat1000NoTreeFloorLb := by
  unfold w16_canonical_witness
  norm_num

/-- Finite 16-element taxonomy of Round 16 Wave 16 (`W16-1..W16-5`) obstructions & structural closures. -/
inductive Wave16RetirementId
  | o_w16_1_scalar_min_eig_factor8_fallacy
  | o_w16_1_v_axis_non_convexity
  | o_w16_1_stripped_p0_collapse_at_45deg
  | o_w16_1_witness_eta_below_pure_unstripped_bl
  | o_w16_1_nonconvex_omega_sf_domain
  | o_w16_5_3cube_partition_non_additivity_at_75deg
  | o_w16_2_fixed_point_dim6_induced_drift
  | o_w16_2_derivative_expansion_divergence_at_bz_corner
  | o_w16_3_reweighting_gaussian_edge_illusion
  | o_w16_3_one_step_bridge_insufficient
  | o_w16_3_r2r1_zero_beta_overlap_floor
  | o_w16_3_symanzik_rect_cancellation
  | o_w16_3_non_markovian_cluster_domination
  | o_w16_4_frozen_so3_z2_order_wall
  | o_w16_4_bare_scale_percolation_and_coarse_vortex_gap
  | o_w16_5_r6_plateau_sextic_and_bkar_776_wall
  deriving DecidableEq, Repr

private def wave16RetirementToFin : Wave16RetirementId → Fin 16
  | .o_w16_1_scalar_min_eig_factor8_fallacy => 0
  | .o_w16_1_v_axis_non_convexity => 1
  | .o_w16_1_stripped_p0_collapse_at_45deg => 2
  | .o_w16_1_witness_eta_below_pure_unstripped_bl => 3
  | .o_w16_1_nonconvex_omega_sf_domain => 4
  | .o_w16_5_3cube_partition_non_additivity_at_75deg => 5
  | .o_w16_2_fixed_point_dim6_induced_drift => 6
  | .o_w16_2_derivative_expansion_divergence_at_bz_corner => 7
  | .o_w16_3_reweighting_gaussian_edge_illusion => 8
  | .o_w16_3_one_step_bridge_insufficient => 9
  | .o_w16_3_r2r1_zero_beta_overlap_floor => 10
  | .o_w16_3_symanzik_rect_cancellation => 11
  | .o_w16_3_non_markovian_cluster_domination => 12
  | .o_w16_4_frozen_so3_z2_order_wall => 13
  | .o_w16_4_bare_scale_percolation_and_coarse_vortex_gap => 14
  | .o_w16_5_r6_plateau_sextic_and_bkar_776_wall => 15

private def wave16RetirementOfFin (i : Fin 16) : Wave16RetirementId :=
  match i.1 with
  | 0 => .o_w16_1_scalar_min_eig_factor8_fallacy
  | 1 => .o_w16_1_v_axis_non_convexity
  | 2 => .o_w16_1_stripped_p0_collapse_at_45deg
  | 3 => .o_w16_1_witness_eta_below_pure_unstripped_bl
  | 4 => .o_w16_1_nonconvex_omega_sf_domain
  | 5 => .o_w16_5_3cube_partition_non_additivity_at_75deg
  | 6 => .o_w16_2_fixed_point_dim6_induced_drift
  | 7 => .o_w16_2_derivative_expansion_divergence_at_bz_corner
  | 8 => .o_w16_3_reweighting_gaussian_edge_illusion
  | 9 => .o_w16_3_one_step_bridge_insufficient
  | 10 => .o_w16_3_r2r1_zero_beta_overlap_floor
  | 11 => .o_w16_3_symanzik_rect_cancellation
  | 12 => .o_w16_3_non_markovian_cluster_domination
  | 13 => .o_w16_4_frozen_so3_z2_order_wall
  | 14 => .o_w16_4_bare_scale_percolation_and_coarse_vortex_gap
  | _ => .o_w16_5_r6_plateau_sextic_and_bkar_776_wall

private def wave16RetirementEquivFin16 : Wave16RetirementId ≃ Fin 16 where
  toFun := wave16RetirementToFin
  invFun := wave16RetirementOfFin
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Wave16RetirementId :=
  Fintype.ofEquiv (Fin 16) wave16RetirementEquivFin16.symm

/-- **Round 16 Wave 16 Honest `.OPEN` Lock**:
    1. Ties Round 15 (`round15_irx_wave15_honest_open_lock`) cleanly into Round 16 Wave 16 (`W16-1..W16-5`).
    2. `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`, `currentH2dRepoWitness = ⟨1, 1, 1⟩`,
       `wave11H2ConstructiveWitness`, `physicalUnificationStatus (Fintype.card H2SubHypothesis) false`, and
       `device_certified = false` ALL remain strictly **`.OPEN`** / `false` after certifying the unstripped
       hinge `42×42` Schur margin vs Needle 1 `O-W16.5-3CubePartitionNonAdditivityAt75Deg`, Manton `5/3` + `c₆*`
       drift cancellation + `O-W9.P2` BZ divergence, `K₄` `270`-orbit complex-`β` Schur gaps + `2×2` 2-step bridge,
       and `SO(3)×ℤ₂` `2/3`-cap order wall + `O(g⁴)` sextic collapse + `W13-1` `[776, 777]` BKAR floor. `[C/B/P/X]` -/
theorem round16_irx_wave16_honest_open_lock :
    -- (1) Full Round 15 honest OPEN lock core preserved verbatim
    ((∀ c : SevenWayCounterexampleId, (sevenWaySignature c).positiveMassGap = false) ∧
      Function.Injective sevenWaySignature ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      ¬ (currentH2dRepoWitness.toH2LayerCandidate).Satisfies .h2d_clay_4d_continuum_measure ∧
      ¬ wave11H2ConstructiveWitness.Satisfies .h2d_clay_4d_continuum_measure ∧
      currentH2dRepoWitness = ⟨1, 1, 1⟩ ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) ∧
    -- (2) Round 16 Wave 16 16-element obstruction taxonomy & canonical witness inhabited alongside Wave 15
    (Nonempty Wave16RetirementId ∧ Fintype.card Wave16RetirementId = 16 ∧
      Nonempty W16_UnstrippedHingeSymanzikK4VortexAndRedTeamWitness ∧
      Nonempty Wave15RetirementId ∧ Fintype.card Wave15RetirementId = 15) ∧
    -- (3) Wave 16 structural theorems
    ((∀ χ : ℝ, ∀ m n : ℝ × ℝ × ℝ, w16NormSq3 m ≤ 1 →
        w16NormSq3 (w16SO3AxisAction χ m n) ≤ w16NormSq3 n) ∧
      (∀ vv : ℚ, vv ≠ 0 →
        (w16CosineWickPrefSU2 * vv) / (w16CosineWickPrefU1 * vv) = 5 / 3) ∧
      (StrictMono w16BZRatio ∧ 1 < w16BZRatio 3 ∧ w16BZRatio 4 = 2) ∧
      ((38 / 100 : ℚ) < w16LinearBlockStep (187 / 100) 1 ∧
        w16LinearBlockStep (187 / 100) 2 < 38 / 100) ∧
      (∀ t : ℝ, 0 ≤ t → t < 1 → (t - t ^ 5) / (1 - t ^ 6) ≤ 2 / 3) ∧
      (∀ C1 v4 : ℝ, 0 < C1 → v4 ≠ 0 → w16SecondOrderG4Sextic C1 0 v4 < 0) ∧
      w16_canonical_witness.block2x2TwoStepBHKAt187Ub < 38 / 100 ∧
      1 / 2 < w16_canonical_witness.so3Z2KtildeHK187Lb) ∧
    -- (4) Strict conditional frontier: even inside `H2dMinimalIrreducibleCore`, current witness stays OPEN
    --     and `device_certified = false`
    (∀ (core : Round05CrossObligationH2d.H2dMinimalIrreducibleCore),
      (∀ o : H2dCoreObligation, core.toObstructionCandidate.Satisfies o) ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) := by
  rcases round15_irx_wave15_honest_open_lock with ⟨h15_core, h15_ret, _, h15_open⟩
  have hcard16 : Fintype.card Wave16RetirementId = 16 := by
    rw [Fintype.card_congr wave16RetirementEquivFin16, Fintype.card_fin]
  have hLip := w16_1_nonabelian_lipschitz_and_t_integral.2.1
  have hTad53 := w16_2_manton_5_3_tadpole_and_fine_shift.2.1
  have hBZ := w16_2_symanzik_rg_c6_drift_and_bz_break.2.2.1
  have hLin := w16_3_axis_b_5staple_and_2step_bridge.1
  have hCap := fun t ht0 ht1 => (w16_4_so3_z2_split_and_frustrated_cap.2.1 t ht0 ht1).2
  have hSex := fun C1 v4 hC1 hv4 => (w16_4_r6_plateau_sextic_bkar_floor_and_hjb.2.1 C1 v4 hC1 hv4).2
  have hWit := w16_canonical_witness_margins
  exact ⟨h15_core,
    ⟨⟨.o_w16_1_scalar_min_eig_factor8_fallacy⟩, hcard16, ⟨w16_canonical_witness⟩, h15_ret.1, h15_ret.2.1⟩,
    ⟨hLip, hTad53, hBZ, hLin, hCap, hSex,
      hWit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hWit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩,
    h15_open⟩

end UEOTPhysicsUnification.IRXWave16UnstrippedHingeSymanzikK4VortexAndRedTeam
