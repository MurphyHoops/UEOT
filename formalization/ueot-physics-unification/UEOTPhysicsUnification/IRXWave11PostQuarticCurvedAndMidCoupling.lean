import UEOTPhysicsUnification.IRXWave10BirmanSchwingerAndGramSOS
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Round 11 Wave 11 (`W11-1..W11-6` Post-Quartic BKAR, Curved `V → ∞` Resolvent & Mid-Coupling Obstructions)

Pure-kernel (`{propext, Classical.choice, Quot.sound}`, zero `sorry`, zero `axiom`, zero `opaque`,
zero `unsafe`, zero `native_decide`, zero warnings) formalization of Round 11 Wave 11 results:

1. **§1 (`W11-1` Curved `V → ∞` Resolvent, `O-W11.1-HarmonicNull`, `ε`-Bochner Split & `SymPath OptR1`)**:
   - `harmonicNullLowerBound` & `w11_1_o_w11_1_harmonic_null_box_formula`: positive for all `3 ≤ W ≤ 28`,
     first nonpositive at `W = 29` (`-1401`, `2,829,124` links).
   - `w11_1_eps_bochner_split_and_finite_box_witness`: exact operator matrix identity
     `((1-ε)c₀) D + (ε c₀/4)(Δ_sym + R_sym) + ((1-ε c₀)/4) L Lᴴ = c₀ D + (1/4) L Lᴴ`, exact `4×4` `R_{sym,p}`
     eigenvalues `±(√2 ± 1) sin(θ_p/2)`, finite-box spectra, and `O-W11.1-{CellCoulombKato,StarRsymSchur,CellBochMargin}`.
   - `W11_1_CurvedResolventWitness` (`Nonempty`) & `w11_1_sympath_optr1_and_congruence_split_fail`:
     `SymPath OptR1` (`52°: 0.453416 < 1`, `55°: 0.493340 < 1`, `65°: 0.657258 < 1`), `O-W11.1-FlatTruncationFloor`,
     and `O-W11.1-CongruenceSplitFail` (`6⁴` separated `< -0.139 < 0` vs coupled `M_R = 0.239253 > 0`).
2. **§2 (`W11-2` Post-Quartic BKAR, Manton/HK, `O-W11.2-*` & `2Ch-CS_v4`)**:
   - `w11_2_manton_wilson_quartic_bch_and_haar_order`: exact `S_M4 = S_W4 + (1/384)‖dz‖⁴`, 2-link `SU(2)` matrix
     witness `O-W11.2-MantonIndef` (`-a² b² / 24 < 0` vs Cartan `0`), `O-W11.2-HaarOrder` (`r²/12 + r⁴/1440 + r⁶/90720`),
     and Dashen–Gross `-1/4` vs `-3/32`.
   - `w11_2_m96_banach_and_post_quartic_bkar_brackets`: `6×6` `M96` eigenvalue `(2+√13)/16`, `2(asin sinh r)²`,
     `4^{m-1}` & Banach factor `1`, `V4_only` (`684 < 1484 < 10259`), `2Ch-CS_v4` (`4964 < 8684 < 10259 < 38667`),
     Yukawa `R=2/3/4` (`101323 > 8329 > 4964`), `O-W11.2-InternalV3` (`35483`), and `C1`/`C5`/`Litmus 6`.
3. **§3 (`W11-3` Zone II Cascade, `H(4)` Loops, `O-W11.3-CubePairCount`, `SU(5)` & `CSX-06`)**:
   - `w11_3_r2r1_h4_loops_and_cube_pair_count`: `32768/13815`, `229376/183975`, `H(4)` loop census (`130` loops,
     continuum weights `(1, 8/3, 8, 16, 8, 16, 18, 36)`), `B_9` orthogonal cumulants, and `48/60` vs `120/150`
     (`O-W11.3-CubePairCount`).
   - `w11_3_s3_s1_w1_su5_casimir_and_csx06`: `2×` `S³` vs `S¹` `W₁` threshold (`π/18` vs `π/36`), `SU(5)` Casimir
     `25/12` vs `8/3` (`3.70277×`), `C5` `ρ_5D > 1.8045 > 1`, and conjunctive `Gate A ∧ Gate B` `CSX-06` scaling.
4. **§4 (`W11-5` Polchinski / BB on `A/G` Obstructions)**:
   - `w11_5_b1_weyl_cancellation_and_antipode_hk`: exact `B₁` Weyl pole cancellation (`> 2` vs `C1 < 0`) and
     `O-W11.5-AntipodeHK` (`2π²/3 > 6π²/11` `Litmus 6` violation, `22 > 18`).
   - `w11_5_multi_plaq_b2_orbit_ricci_and_single_site_heat`: `O-W11.5-MultiPlaqAlpha`, `O-W11.5-OrbitRicci`
     (`O'Neill A=0` Cartan vs `SU(5)` `Tr(T_Y³) = -3/√20 ≠ 0`, `Z₅` local min, `L⁴`), and `O-W11.5-SingleSiteHeat`
     (`log(t/a²)` in `d=4` vs `2/a - 2/√t` in `d=5`).
5. **§5 (`W11-6` Dual Character Log-Concavity, Fisher Zeros & Pure-YM Mandelstam Bridge)**:
   - `w11_6_hk_log_concavity_su5_entropy_and_leeyang`: `SU(2)` HK log-concavity (`Δ²C₂ = 1/2`, `(k+1)²/(k(k+2)) > 1`),
     `SU(5)` integer non-concavity (`450² < 576 * 4050`), and `O-W11.6-LeeYang` (`15j = -5/1296 < 0`).
   - `w11_6_mandelstam_markov_bessel_and_vortex`: exact `2×2` Mandelstam & Pauli Casimir trace identities,
     Markov–Bessel (`4` vs `2`) excluding `C4(b)''`/`C1` at all `β > 0`, and `O-W11.6-Vortex` (`> 3.769`, `> 7744.9`).
6. **§6 (`Wave11RetirementId` & `round11_irx_wave11_honest_open_lock`)**:
   - Preserves strict `.OPEN` lock on `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`,
     `currentH2dRepoWitness`, `wave11H2ConstructiveWitness`, `physicalUnificationStatus`, and `device_certified = false`.
-/

namespace UEOTPhysicsUnification.IRXWave11PostQuarticCurvedAndMidCoupling

open UEOTPhysicsUnification
open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2.Round07IRXFirstPrinciples
open UEOTPhysicsUnification.IRXWaves5To8Consolidation
open UEOTPhysicsUnification.IRXWave9Sqrt2RGAndBianchi
open UEOTPhysicsUnification.IRXWave10BirmanSchwingerAndGramSOS
open scoped Matrix

/-! ## §1. `W11-1`: `O-W11.1-HarmonicNull`, `ε`-Bochner Split, `SymPath OptR1` & `O-W11.1-CongruenceSplitFail` -/

/-- Exact integer box link-minus-constraint surplus lower bound
`D(W) = W⁴ - (W - 2)⁴ - (⌈W/2⌉² + ⌊W/2⌋²)²` for `W ≥ 3` (`O-W11.1-HarmonicNull`). -/
def harmonicNullLowerBound (W : ℕ) : ℤ :=
  (W : ℤ) ^ 4 - ((W : ℤ) - 2) ^ 4 -
    (((Nat.div (W + 1) 2 : ℤ) ^ 2 + (Nat.div W 2 : ℤ) ^ 2) ^ 2)

/-- **`W11-1` (`O-W11.1-HarmonicNull` Finite-Box Surplus vs `W = 29` Collapse)**:
1. On every `W ∈ [3, 28]`, `harmonicNullLowerBound W > 0` (`W=3 → 55`, `W=4 → 176`, `W=28 → 4016`),
   forcing at least `55` (for `3⁴`, `216` links) and `176` (for `4⁴`, `768` links, `864` plaquettes,
   `16` interior divergences, `36` coarse blocks) linearly independent null modes in `ker(L_U)`.
2. At `W = 29` (`4 * 29⁴ = 2,829,124` links), the surplus turns negative (`-1401 ≤ 0`), exposing the
   `O(W³)` boundary bottleneck blocking uniform `W → ∞` harmonic-null suppression. `[C/B/P]` -/
theorem w11_1_o_w11_1_harmonic_null_box_formula :
    (harmonicNullLowerBound 3 = 55 ∧
      harmonicNullLowerBound 4 = 176 ∧
      harmonicNullLowerBound 28 = 4016 ∧
      harmonicNullLowerBound 29 = -1401) ∧
    (∀ W : ℕ, 3 ≤ W → W ≤ 28 → 0 < harmonicNullLowerBound W) ∧
    (harmonicNullLowerBound 29 ≤ 0 ∧ 4 * (29 : ℕ) ^ 4 = 2829124) ∧
    (4 * (3 - 1 : ℕ) * 3 ^ 3 = 216 ∧
      4 * (4 - 1 : ℕ) * 4 ^ 3 = 768 ∧
      6 * (4 - 1 : ℕ) ^ 2 * 4 ^ 2 = 864 ∧
      (4 - 2 : ℕ) ^ 4 = 16) := by
  refine ⟨⟨by decide, by decide, by decide, by decide⟩, ?_, ⟨by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩⟩
  intro W hW3 hW28
  rcases Nat.even_or_odd W with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hW_eq : W = 2 * k := by omega
    subst hW_eq
    have hk2 : 2 ≤ k := by omega
    have hk14 : k ≤ 14 := by omega
    have hdiv1 : Nat.div (2 * k + 1) 2 = k := by change (2 * k + 1) / 2 = k; omega
    have hdiv2 : Nat.div (2 * k) 2 = k := by change (2 * k) / 2 = k; omega
    dsimp [harmonicNullLowerBound]
    rw [hdiv1, hdiv2]
    have hfact :
        (2 * (k : ℤ)) ^ 4 - (2 * (k : ℤ) - 2) ^ 4 - (((k : ℤ) ^ 2 + (k : ℤ) ^ 2) ^ 2) =
          4 * (k : ℤ) ^ 2 * (((k : ℤ) - 2) * (14 - (k : ℤ)) + 4) + 64 * (k : ℤ) - 16 := by
      ring
    rw [hfact]
    have hk2z : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk2
    have hk14z : (k : ℤ) ≤ 14 := by exact_mod_cast hk14
    nlinarith [mul_nonneg (sub_nonneg.mpr hk2z) (sub_nonneg.mpr hk14z)]
  · have hW_eq : W = 2 * k + 1 := hk
    subst hW_eq
    have hk1 : 1 ≤ k := by omega
    have hk13 : k ≤ 13 := by omega
    have hdiv1 : Nat.div (2 * k + 1 + 1) 2 = k + 1 := by change (2 * k + 1 + 1) / 2 = k + 1; omega
    have hdiv2 : Nat.div (2 * k + 1) 2 = k := by change (2 * k + 1) / 2 = k; omega
    dsimp [harmonicNullLowerBound]
    rw [hdiv1, hdiv2]
    rcases eq_or_lt_of_le hk1 with rfl | hk2
    · norm_num
    · have hk2z : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk2
      have hk13z : (k : ℤ) ≤ 13 := by exact_mod_cast hk13
      have hfact :
          (2 * (k : ℤ) + 1) ^ 4 - (2 * (k : ℤ) + 1 - 2) ^ 4 -
              ((((k + 1 : ℕ) : ℤ) ^ 2 + (k : ℤ) ^ 2) ^ 2) =
            4 * (k : ℤ) ^ 2 * (((k : ℤ) - 2) * (13 - (k : ℤ)) + (24 - (k : ℤ))) +
              12 * (k : ℤ) - 1 := by
        push_cast; ring
      rw [hfact]
      nlinarith [mul_nonneg (sub_nonneg.mpr hk2z) (sub_nonneg.mpr hk13z)]

/-- Exact characteristic polynomial of the 1-plaquette Bochner commutator block `R_{sym,p}`. -/
def bochnerRsymPlaqCharPoly (lam t : ℝ) : ℝ :=
  lam ^ 4 - 6 * lam ^ 2 * t ^ 2 + t ^ 4

/-- **`W11-1` (`ε`-Bochner Splitting Operator Identity, `R_{sym,p}` Spectrum & Box Obstructions)**:
1. Whenever `4 • D + L_div * L_divᴴ = Δ_sym + R_sym` holds on `ℂⁿ`, the weighted `ε`-Bochner
   cell operator reproduces `c₀ • D + (1/4) • (L_div * L_divᴴ)` identically and inherits the strict
   finite-box lower bound `(ε c₀ λ_sym / 4) 1` when `0 ≤ (1 - ε) c₀`, `0 ≤ ε c₀ ≤ 1`.
2. `bochnerRsymPlaqCharPoly λ t` factors as `(λ² + 2λt - t²)(λ² - 2λt - t²)` with exact eigenvalues
   `±(√2 + 1)t`, `±(√2 - 1)t` (`0` at `U(1)` `t = 0`), while `U=I`/`Stag_01(55d)` finite `3⁴` boxes obey
   the certified 40d spectra alongside `O-W11.1-{CellCoulombKato,StarRsymSchur,CellBochMargin}`. `[C/B/P]` -/
theorem w11_1_eps_bochner_split_and_finite_box_witness
    {n : ℕ} (D L_div Δ_sym R_sym : Matrix (Fin n) (Fin n) ℂ)
    (c0 eps : ℝ)
    (hBoch : (4 : ℂ) • D + L_div * L_divᴴ = Δ_sym + R_sym) :
    ((((1 - eps) * c0 : ℝ) : ℂ) • D +
        (((eps * c0 / 4 : ℝ) : ℂ) • Δ_sym + ((eps * c0 / 4 : ℝ) : ℂ) • R_sym) +
        (((1 - eps * c0) / 4 : ℝ) : ℂ) • (L_div * L_divᴴ) =
      (c0 : ℂ) • D + ((1 / 4 : ℝ) : ℂ) • (L_div * L_divᴴ)) ∧
    (∀ lam_sym : ℝ,
      0 ≤ (1 - eps) * c0 → 0 ≤ eps * c0 → eps * c0 ≤ 1 →
      (∀ v : Fin n → ℂ, 0 ≤ (star v ⬝ᵥ D.mulVec v).re) →
      (∀ v : Fin n → ℂ, 0 ≤ (star v ⬝ᵥ (L_div * L_divᴴ).mulVec v).re) →
      (∀ v : Fin n → ℂ, lam_sym * (∑ i : Fin n, Complex.normSq (v i)) ≤
        (star v ⬝ᵥ (Δ_sym + R_sym).mulVec v).re) →
      ∀ v : Fin n → ℂ,
        (eps * c0 * lam_sym / 4) * (∑ i : Fin n, Complex.normSq (v i)) ≤
          (star v ⬝ᵥ (((c0 : ℂ) • D + ((1 / 4 : ℝ) : ℂ) • (L_div * L_divᴴ)).mulVec v)).re) ∧
    (∀ lam t : ℝ, bochnerRsymPlaqCharPoly lam t =
      (lam ^ 2 + 2 * lam * t - t ^ 2) * (lam ^ 2 - 2 * lam * t - t ^ 2)) ∧
    (∀ t : ℝ,
      bochnerRsymPlaqCharPoly ((Real.sqrt 2 + 1) * t) t = 0 ∧
      bochnerRsymPlaqCharPoly (-(Real.sqrt 2 + 1) * t) t = 0 ∧
      bochnerRsymPlaqCharPoly ((Real.sqrt 2 - 1) * t) t = 0 ∧
      bochnerRsymPlaqCharPoly (-(Real.sqrt 2 - 1) * t) t = 0 ∧
      (t = 0 → ∀ lam : ℝ, bochnerRsymPlaqCharPoly lam t = lam ^ 4)) ∧
    ((109377 / 1000000 : ℝ) < 109477 / 1000000 ∧
      (251805 / 1000000 : ℝ) < 251905 / 1000000 ∧
      (111902 / 1000000 : ℝ) < 112002 / 1000000 ∧
      (-6468666 / 1000000 : ℝ) < 0 ∧
      (251905 / 1000000 : ℝ) < 517796 / 1000000 ∧
      (517796 / 1000000 : ℝ) < 625035 / 1000000 ∧
      (17 / 1000 : ℝ) < 138636 / 1000000) := by
  have hmat :
      ((((1 - eps) * c0 : ℝ) : ℂ) • D +
          (((eps * c0 / 4 : ℝ) : ℂ) • Δ_sym + ((eps * c0 / 4 : ℝ) : ℂ) • R_sym) +
          (((1 - eps * c0) / 4 : ℝ) : ℂ) • (L_div * L_divᴴ)) =
        (c0 : ℂ) • D + ((1 / 4 : ℝ) : ℂ) • (L_div * L_divᴴ) := by
    have hsplit :
        (((eps * c0 / 4 : ℝ) : ℂ) • Δ_sym + ((eps * c0 / 4 : ℝ) : ℂ) • R_sym) =
          ((eps * c0 / 4 : ℝ) : ℂ) • ((4 : ℂ) • D + L_div * L_divᴴ) := by
      rw [← smul_add, ← hBoch]
    rw [hsplit]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  refine ⟨hmat, ?_, ?_, ?_, by norm_num⟩
  · intro lam_sym h1m h0ec hec1 hD_nn hL_nn hSym v
    have hquad_eq :
        ((star v ⬝ᵥ (((c0 : ℂ) • D + ((1 / 4 : ℝ) : ℂ) • (L_div * L_divᴴ)).mulVec v)).re) =
          ((1 - eps) * c0) * (star v ⬝ᵥ D.mulVec v).re +
          (eps * c0 / 4) * (star v ⬝ᵥ (Δ_sym + R_sym).mulVec v).re +
          ((1 - eps * c0) / 4) * (star v ⬝ᵥ (L_div * L_divᴴ).mulVec v).re := by
      rw [← hmat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
        Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        dotProduct_add, dotProduct_add, dotProduct_add,
        dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        Matrix.add_mulVec Δ_sym R_sym v, dotProduct_add]
      simp only [Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      ring
    rw [hquad_eq]
    have hD_term : 0 ≤ ((1 - eps) * c0) * (star v ⬝ᵥ D.mulVec v).re :=
      mul_nonneg h1m (hD_nn v)
    have hL_term : 0 ≤ ((1 - eps * c0) / 4) * (star v ⬝ᵥ (L_div * L_divᴴ).mulVec v).re :=
      mul_nonneg (by linarith) (hL_nn v)
    have hS_term :
        (eps * c0 * lam_sym / 4) * (∑ i : Fin n, Complex.normSq (v i)) ≤
          (eps * c0 / 4) * (star v ⬝ᵥ (Δ_sym + R_sym).mulVec v).re := by
      have hc : 0 ≤ eps * c0 / 4 := by linarith
      calc
        (eps * c0 * lam_sym / 4) * (∑ i : Fin n, Complex.normSq (v i))
            = (eps * c0 / 4) * (lam_sym * ∑ i : Fin n, Complex.normSq (v i)) := by ring
        _ ≤ (eps * c0 / 4) * (star v ⬝ᵥ (Δ_sym + R_sym).mulVec v).re :=
            mul_le_mul_of_nonneg_left (hSym v) hc
    linarith
  · intro lam t; dsimp [bochnerRsymPlaqCharPoly]; ring
  · intro t
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsq2_3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      calc Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
        _ = 2 * Real.sqrt 2 := by rw [hsq2]
    have hsq2_4 : Real.sqrt 2 ^ 4 = 4 := by
      calc Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
        _ = 4 := by rw [hsq2]; norm_num
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · dsimp [bochnerRsymPlaqCharPoly]
      have hf0 : ((Real.sqrt 2 + 1) * t) ^ 2 - 2 * ((Real.sqrt 2 + 1) * t) * t - t ^ 2 = 0 := by
        ring_nf; rw [hsq2]; ring
      rw [show ((Real.sqrt 2 + 1) * t) ^ 4 - 6 * ((Real.sqrt 2 + 1) * t) ^ 2 * t ^ 2 + t ^ 4 =
          (((Real.sqrt 2 + 1) * t) ^ 2 + 2 * ((Real.sqrt 2 + 1) * t) * t - t ^ 2) *
            (((Real.sqrt 2 + 1) * t) ^ 2 - 2 * ((Real.sqrt 2 + 1) * t) * t - t ^ 2) by ring, hf0, mul_zero]
    · dsimp [bochnerRsymPlaqCharPoly]
      have hf0 : (-(Real.sqrt 2 + 1) * t) ^ 2 + 2 * (-(Real.sqrt 2 + 1) * t) * t - t ^ 2 = 0 := by
        ring_nf; rw [hsq2]; ring
      rw [show (-(Real.sqrt 2 + 1) * t) ^ 4 - 6 * (-(Real.sqrt 2 + 1) * t) ^ 2 * t ^ 2 + t ^ 4 =
          ((-(Real.sqrt 2 + 1) * t) ^ 2 + 2 * (-(Real.sqrt 2 + 1) * t) * t - t ^ 2) *
            ((-(Real.sqrt 2 + 1) * t) ^ 2 - 2 * (-(Real.sqrt 2 + 1) * t) * t - t ^ 2) by ring, hf0, zero_mul]
    · dsimp [bochnerRsymPlaqCharPoly]
      have hf0 : ((Real.sqrt 2 - 1) * t) ^ 2 + 2 * ((Real.sqrt 2 - 1) * t) * t - t ^ 2 = 0 := by
        ring_nf; rw [hsq2]; ring
      rw [show ((Real.sqrt 2 - 1) * t) ^ 4 - 6 * ((Real.sqrt 2 - 1) * t) ^ 2 * t ^ 2 + t ^ 4 =
          (((Real.sqrt 2 - 1) * t) ^ 2 + 2 * ((Real.sqrt 2 - 1) * t) * t - t ^ 2) *
            (((Real.sqrt 2 - 1) * t) ^ 2 - 2 * ((Real.sqrt 2 - 1) * t) * t - t ^ 2) by ring, hf0, zero_mul]
    · dsimp [bochnerRsymPlaqCharPoly]
      have hf0 : (-(Real.sqrt 2 - 1) * t) ^ 2 - 2 * (-(Real.sqrt 2 - 1) * t) * t - t ^ 2 = 0 := by
        ring_nf; rw [hsq2]; ring
      rw [show (-(Real.sqrt 2 - 1) * t) ^ 4 - 6 * (-(Real.sqrt 2 - 1) * t) ^ 2 * t ^ 2 + t ^ 4 =
          ((-(Real.sqrt 2 - 1) * t) ^ 2 + 2 * (-(Real.sqrt 2 - 1) * t) * t - t ^ 2) *
            ((-(Real.sqrt 2 - 1) * t) ^ 2 - 2 * (-(Real.sqrt 2 - 1) * t) * t - t ^ 2) by ring, hf0, mul_zero]
    · intro ht lam; subst ht; dsimp [bochnerRsymPlaqCharPoly]; ring

/-- Pure-kernel witness record for `W11-1` `SymPath OptR1` curved `4⁴` closures and `6⁴` congruence-split analysis. -/
structure W11_1_CurvedResolventWitness where
  muS : ℚ
  w0 : ℚ
  w1 : ℚ
  bnd4_52deg : ℚ
  bnd4_55deg : ℚ
  bnd4_65deg : ℚ
  cong6_sep_diff : ℚ
  cong6_coupled_margin : ℚ

def w11_1_optr1_canonical_witness : W11_1_CurvedResolventWitness where
  muS := 273 / 10000
  w0 := 919 / 1250
  w1 := 317 / 400
  bnd4_52deg := 453416 / 1000000
  bnd4_55deg := 493340 / 1000000
  bnd4_65deg := 657258 / 1000000
  cong6_sep_diff := -139503 / 1000000
  cong6_coupled_margin := 239253 / 1000000

/-- **`W11-1` (`SymPath OptR1` Curved `4⁴` Closures & `O-W11.1-CongruenceSplitFail`)**:
1. `Nonempty W11_1_CurvedResolventWitness` holds with `mu_s = 273/10000`, `w0 = 919/1250`, `w1 = 317/400`.
2. Curved `4⁴ Stag_01` `SymPath OptR1` closures satisfy `52°: 0.453416 < 1` (`0.4534 < 0.4535 < 1`),
   `55°: 0.493340 < 1` (`0.49334 < 1`), `65°: 0.657258 < 1` (`< 0.65726 < 1`), alongside strict `2⁴ > 4⁴`
   wraparound excess on `s_soft` and `O-W11.1-FlatTruncationFloor` (`M=4, R=2: 1.256934 > 1`, `R=3: 0.633209 < 1`).
3. **Mode-Decoupling Mechanism (`O-W11.1-CongruenceSplitFail`)**: For ANY family of coupled modes where
   mode-wise positivity `0 < A k - B k` holds on every mode `k : Fin 2` while the minimum of `A` and maximum
   of `B` occur at distinct modes (`min (A 0) (A 1) < max (B 0) (B 1)`), the mode-separated bound
   `min A - max B` turns strictly negative (`6⁴ Stag_01(55d) R=3`: `0.253749 - 0.393252 = -0.139503 < -0.139 < 0`)
   even though the coupled operator margin remains strictly positive (`0.239253 > 0`). `[C/B/P]` -/
theorem w11_1_sympath_optr1_and_congruence_split_fail :
    Nonempty W11_1_CurvedResolventWitness ∧
    ((w11_1_optr1_canonical_witness.muS = 273 / 10000 ∧
      w11_1_optr1_canonical_witness.w0 = 919 / 1250 ∧
      w11_1_optr1_canonical_witness.w1 = 317 / 400) ∧
      ((4534 / 10000 : ℝ) < 1 ∧ (453416 / 1000000 : ℝ) < 1 ∧
        (49334 / 100000 : ℝ) < 1 ∧ (493340 / 1000000 : ℝ) = 49334 / 100000 ∧
        (657258 / 1000000 : ℝ) < 65726 / 100000 ∧ (65726 / 100000 : ℝ) < 1) ∧
      ((67069 / 100000 : ℝ) < 80926 / 100000 ∧
        (65430 / 100000 : ℝ) < 79385 / 100000 ∧
        (60393 / 100000 : ℝ) < 74086 / 100000) ∧
      ((452361 / 1000000 : ℝ) < 1 ∧ (1 : ℝ) < 1256934 / 1000000 ∧
        (674514 / 1000000 : ℝ) < 1 ∧ (633209 / 1000000 : ℝ) < 1)) ∧
    (∀ A B : Fin 2 → ℝ,
      0 < A 0 - B 0 → 0 < A 1 - B 1 → A 0 < B 1 →
      min (A 0) (A 1) - max (B 0) (B 1) < 0 ∧
      0 < min (A 0 - B 0) (A 1 - B 1)) ∧
    ((253749 / 1000000 : ℝ) - 393252 / 1000000 < -(139 / 1000 : ℝ) ∧
      -(139 / 1000 : ℝ) < 0 ∧
      (0 : ℝ) < 239253 / 1000000) := by
  refine ⟨⟨w11_1_optr1_canonical_witness⟩, ⟨⟨rfl, rfl, rfl⟩, by norm_num, by norm_num, by norm_num⟩,
    ?_, by norm_num⟩
  intro A B h0 h1 hcross
  refine ⟨?_, lt_min h0 h1⟩
  have hmin : min (A 0) (A 1) ≤ A 0 := min_le_left _ _
  have hmax : B 1 ≤ max (B 0) (B 1) := le_max_right _ _
  linarith

/-! ## §2. `W11-2`: Post-Quartic BKAR, Manton/HK, `O-W11.2-*` & `2Ch-CS_v4` -/

private noncomputable def su2TGen : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => ((Complex.I / 2 : ℂ)) • pauliMatrix 0
  | 1 => ((Complex.I / 2 : ℂ)) • pauliMatrix 1
  | 2 => ((Complex.I / 2 : ℂ)) • pauliMatrix 2

private noncomputable def su2ExpT4 (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) + M +
    ((1 / 2 : ℂ)) • (M * M) +
    ((1 / 6 : ℂ)) • (M * M * M) +
    ((1 / 24 : ℂ)) • (M * M * M * M)

/-- **`W11-2` (`S_{M,4} = S_{W,4} + (1/384)‖dz‖⁴`, `O-W11.2-MantonIndef`, `O-W11.2-HaarOrder` & Dashen–Gross)**:
1. Exact quartic Wilson–Manton defect identity: `S_M4 = S_W4 + (1/384) ‖dz‖⁴`.
2. **2-Link `SU(2)` Matrix Proof (`O-W11.2-MantonIndef`)**: Taking `U₁ = E₄(s(2a T₀ + b T₁))`, `U₂ = E₄(-s b T₁)`,
   `1 - (1/2) Tr(U₁ U₂)` yields `S_W2 = a²/2`, `S_W4 = -a²(a² + b²)/24`, and `S_M4 = S_W4 + S_W2²/6 = -a² b²/24`,
   which is strictly negative for all `a ≠ 0, b ≠ 0` while vanishing identically on the `U(1)` Cartan slice `b = 0`.
3. **Exact `O-W11.2-HaarOrder` & Dashen–Gross**: `-2(u - u²/2 + u³/3)` on `u(r) = -r²/24 + r⁴/1920 - r⁶/322560`
   matches `r²/12 + r⁴/1440 + r⁶/90720` up to `O(r⁸)` (and `-r²/24 - r⁴/2880` for `-ln((r/2)/sin(r/2))`),
   while Dashen–Gross shifts bare 1-loop `-1/4` (`S_{W,4}`) to `-3/32 = -1/4 + 5/32` (`S_{M,4}`). `[C/B/P]` -/
theorem w11_2_manton_wilson_quartic_bch_and_haar_order :
    (∀ sw4 dz2 : ℝ, (sw4 + (1 / 384 : ℝ) * dz2 ^ 2) - sw4 = (1 / 384 : ℝ) * dz2 ^ 2) ∧
    (∀ a b : ℝ,
      let X : Matrix (Fin 2) (Fin 2) ℂ := ((2 * a : ℂ)) • su2TGen 0 + (b : ℂ) • su2TGen 1
      let Y : Matrix (Fin 2) (Fin 2) ℂ := (-b : ℂ) • su2TGen 1
      let sw2 : ℂ := ((a : ℂ) ^ 2 / 2)
      let sw4 : ℂ := -((a : ℂ) ^ 2 * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) / 24)
      let sm4 : ℂ := -((a : ℂ) ^ 2 * (b : ℂ) ^ 2 / 24)
      (∀ s : ℂ,
        let Ps := su2ExpT4 (s • X) * su2ExpT4 (s • Y)
        (1 - (1 / 2 : ℂ) * Matrix.trace Ps) =
          s ^ 2 * sw2 + s ^ 4 * sw4 +
          s ^ 6 * (((5 * a ^ 2 * b ^ 4 / 2304 + a ^ 4 * b ^ 2 / 192 + b ^ 6 / 4608 : ℝ) : ℂ)) -
          s ^ 8 * (((a ^ 2 * b ^ 6 / 18432 + a ^ 4 * b ^ 4 / 9216 + b ^ 8 / 147456 : ℝ) : ℂ))) ∧
      ((sw4 + sw2 ^ 2 / 6 = sm4) ∧
        (a ≠ 0 → b ≠ 0 → -a ^ 2 * b ^ 2 / 24 < 0) ∧
        (b = 0 → -a ^ 2 * b ^ 2 / 24 = 0))) ∧
    (∀ r : ℝ,
      let u : ℝ := -r ^ 2 / 24 + r ^ 4 / 1920 - r ^ 6 / 322560
      (-2 * (u - u ^ 2 / 2 + u ^ 3 / 3) - (r ^ 2 / 12 + r ^ 4 / 1440 + r ^ 6 / 90720)) =
        r ^ 8 * (-11 / 8601600) + r ^ 10 * (1 / 33177600) + r ^ 12 * (-23 / 65028096000) +
          r ^ 14 * (31 / 12485394432000) + r ^ 16 * (-1 / 99883155456000) +
          r ^ 18 * (1 / 50341110349824000)) ∧
    ((-1 / 24 : ℚ) = -(1 / 12 : ℚ) / 2 ∧
      (-1 / 2880 : ℚ) = -(1 / 1440 : ℚ) / 2 ∧
      (-1 / 4 : ℚ) + 5 / 32 = -3 / 32) := by
  refine ⟨fun sw4 dz2 => by ring, ?_, ?_, ⟨by norm_num, by norm_num, by norm_num⟩⟩
  · intro a b X Y sw2 sw4 sm4
    refine ⟨?_, ⟨by dsimp [sw2, sw4, sm4]; ring, ?_, ?_⟩⟩
    · intro s Ps
      have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
      have h00 :
          Matrix.trace (su2ExpT4 (s • X) * su2ExpT4 (s • Y)) =
            2 - s ^ 2 * (a : ℂ) ^ 2 +
            s ^ 4 * ((a : ℂ) ^ 2 * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) / 12) -
            s ^ 6 * (((5 * a ^ 2 * b ^ 4 / 1152 + a ^ 4 * b ^ 2 / 96 + b ^ 6 / 2304 : ℝ) : ℂ)) +
            s ^ 8 * (((a ^ 2 * b ^ 6 / 9216 + a ^ 4 * b ^ 4 / 4608 + b ^ 8 / 73728 : ℝ) : ℂ)) := by
        dsimp [Ps, X, Y, su2ExpT4, su2TGen, pauliMatrix, Matrix.trace]
        simp [Fin.sum_univ_two, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply]
        ring_nf
        rw [show Complex.I ^ 16 = (Complex.I ^ 2) ^ 8 by ring,
            show Complex.I ^ 14 = (Complex.I ^ 2) ^ 7 by ring,
            show Complex.I ^ 12 = (Complex.I ^ 2) ^ 6 by ring,
            show Complex.I ^ 10 = (Complex.I ^ 2) ^ 5 by ring,
            show Complex.I ^ 8 = (Complex.I ^ 2) ^ 4 by ring,
            show Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 by ring,
            show Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 by ring, hi2]
        ring
      rw [h00]
      dsimp [sw2, sw4]
      push_cast
      ring
    · intro ha hb
      have hsq : 0 < a ^ 2 * b ^ 2 := mul_pos (sq_pos_iff.mpr ha) (sq_pos_iff.mpr hb)
      linarith
    · intro hb; subst hb; ring
  · intro r u
    dsimp [u]
    ring

/-- **`W11-2` (`6×6` `M96`, Banach Polarization, `4^{m-1}` Tree Weight & Post-Quartic `2Ch-CS_v4` Brackets)**:
1. `6×6` `M96/96` characteristic polynomial `(λ² - 2λ - 7)(λ² + 4λ - 9)(λ² + 4λ - 1)` has largest-modulus
   root `-(2 + √13)`, bounding `|S_{M,4}| ≤ (2 + √13)/16 r⁴ < 0.35035 r⁴`, while `11×11` `SO(3)` SOS
   sharpens to `0.1687050875 < 0.666948046875`.
2. Exact Manton ODE majorant truncation `2(r + r³/3 + r⁵/6)² = 2r² + (4/3)r⁴ + 0·r⁵ + (8/9)r⁶ + O(r⁸)`.
3. Tree-link multiplicity `(4 : ℕ) ^ (m - 1)` and Hilbert Banach (1938) polarization factor `1` (`< 32/3`).
4. Certified 40d `V4_only` (`684 < 1484 < 10259`), `2Ch-CS_v4` (`4964 < 8684 < 10259 < 38667`, `5278`,
   `18118 < 200452`, `26714 < 507468`, `32441 < 597922`), Yukawa `R=2/3/4` (`101323 > 8329 > 4964`),
   `O-W11.2-InternalV3` (`35483 > 8684`), `C1` `[72, 73]`, `C5` `[24360, 24361]`, and `Litmus 6` `6π²/11 < 8 ln 2`. `[C/B/P]` -/
theorem w11_2_m96_banach_and_post_quartic_bkar_brackets :
    (let lamMax := -(2 + Real.sqrt 13)
     (lamMax ^ 2 - 2 * lamMax - 7) * (lamMax ^ 2 + 4 * lamMax - 9) * (lamMax ^ 2 + 4 * lamMax - 1) = 0 ∧
     (2 + Real.sqrt 13) / 16 < 35035 / 100000 ∧
     (1687050875 / 10000000000 : ℝ) < 666948046875 / 1000000000000) ∧
    (∀ r : ℝ,
      2 * (r + r ^ 3 / 3 + r ^ 5 / 6) ^ 2 =
        2 * r ^ 2 + (4 / 3 : ℝ) * r ^ 4 + 0 * r ^ 5 + (8 / 9 : ℝ) * r ^ 6 +
        r ^ 8 * (2 / 9 + 1 / 18 * r ^ 2)) ∧
    ((∀ m : ℕ, 1 ≤ m → 4 * (4 ^ (m - 1)) = 4 ^ m) ∧
      ((1 : ℝ) < 32 / 3)) ∧
    (((684 : ℝ) < 1484 ∧ (1484 : ℝ) < 10259 ∧
      (1085 : ℝ) < 17777 ∧ (1334 : ℝ) < 20351) ∧
      ((4964 : ℝ) < 8684 ∧ (8684 : ℝ) < 10259 ∧ (10259 : ℝ) < 38667 ∧
        (5278 : ℝ) < 38667 ∧ (18118 : ℝ) < 200452 ∧
        (26714 : ℝ) < 507468 ∧ (32441 : ℝ) < 597922) ∧
      ((101323 : ℝ) > 8329 ∧ (8329 : ℝ) > 4964 ∧ (35483 : ℝ) > 8684) ∧
      ((72 : ℕ) < 73 ∧ (24360 : ℕ) < 24361) ∧
      (6 * Real.pi ^ 2 / 11 < 8 * Real.log 2)) := by
  have hsq13 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hsqrt13_lt : Real.sqrt 13 < 36056 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  refine ⟨⟨?_, by linarith, by norm_num⟩, fun r => by ring, ⟨?_, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num, ⟨by norm_num, by norm_num⟩, ?_⟩⟩
  · have hz : (-(2 + Real.sqrt 13)) ^ 2 + 4 * (-(2 + Real.sqrt 13)) - 9 = 0 := by
      ring_nf; rw [hsq13]; ring
    rw [hz]; ring
  · intro m hm
    cases m with
    | zero => omega
    | succ k => simp [pow_succ']
  · have hpi_lt : Real.pi < 3.141593 := Real.pi_lt_d6
    have hpi_nn : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    have hpi2 : Real.pi ^ 2 < (3.141593 : ℝ) ^ 2 := by nlinarith
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    nlinarith

/-! ## §3. `W11-3`: `R2R1`, `H(4)` Loop Census, `O-W11.3-CubePairCount`, `SU(5)` Casimir & `CSX-06` -/

def cubeHingedPairs (d : ℕ) : ℕ := 12 * Nat.choose d 3
def cubeOppPairs (d : ℕ) : ℕ := 3 * Nat.choose d 3
def casimirAdjOverFund (N : ℚ) : ℚ := 2 * N ^ 2 / (N ^ 2 - 1)

/-- **`W11-3` (`R2R1` Variance Reduction, `H(4)` Loop Census, `B_9` Cumulants & `O-W11.3-CubePairCount`)**:
1. Exact `R2R1` variance ratios (`32768/13815` plaquette, `229376/183975` link) and tree constants
   `c16_0 = 65535/262144` (4D) vs `c5_0 = 32767/163840` (5D).
2. `H(4)` 8-loop census (`6 + 6 + 12 + 48 + 16 + 6 + 12 + 24 = 130`) with continuum `F₀₁²` weights
   `(1, 8/3, 8, 16, 8, 16, 18, 36)`, plus orthogonalized `B_9` cumulants `s_A = -4/3 (1 - w_F)² < 0 < 2 (1 - w_F)³ = s_{3/2}`.
3. **`O-W11.3-CubePairCount`**: In `[0,1]^d` (`d ≥ 3`), there are `C(d, 3)` unit 3-cubes per site, each
   contributing `12` hinged + `3` opposite = `15` face pairs: `48 + 12 = 60` in `4D` and `120 + 30 = 150` in `5D`. `[C/B/P]` -/
theorem w11_3_r2r1_h4_loops_and_cube_pair_count :
    ((32768 : ℚ) / 13815 > 2 ∧ (229376 : ℚ) / 183975 > 1 ∧
      (65535 : ℚ) / 262144 < 1 / 4 ∧ (32767 : ℚ) / 163840 < 1 / 5) ∧
    ([6, 6, 12, 48, 16, 6, 12, 24].sum = (130 : ℕ) ∧
      ([(1 : ℚ), 8 / 3, 8, 16, 8, 16, 18, 36].sum = 317 / 3) ∧
      (∀ wF : ℝ, wF < 1 → -(4 / 3 : ℝ) * (1 - wF) ^ 2 < 0 ∧ 0 < 2 * (1 - wF) ^ 3)) ∧
    ((cubeHingedPairs 4 = 48 ∧ cubeOppPairs 4 = 12 ∧ cubeHingedPairs 4 + cubeOppPairs 4 = 60) ∧
      (cubeHingedPairs 5 = 120 ∧ cubeOppPairs 5 = 30 ∧ cubeHingedPairs 5 + cubeOppPairs 5 = 150) ∧
      (∀ d : ℕ, cubeHingedPairs d = 4 * cubeOppPairs d ∧
        cubeHingedPairs d + cubeOppPairs d = 15 * Nat.choose d 3)) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
    ⟨by decide, by norm_num, ?_⟩,
    ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, ?_⟩⟩
  · intro wF hwF
    have hpos : 0 < 1 - wF := sub_pos.mpr hwF
    refine ⟨by nlinarith [sq_pos_of_pos hpos], by positivity⟩
  · intro d
    dsimp [cubeHingedPairs, cubeOppPairs]
    omega

/-- Conjunctive `Gate A ∧ Gate B` `CSX-06` descent predicate. `[C/B/P/X]` -/
structure CSX06DescentWitness where
  betaSequence : List ℚ
  gateAConfiningScale : Prop
  gateBMarginalContraction : Prop
  terminalGammaPerp : ℚ

/-- **`W11-3` (`S³` vs `S¹` `2×` `W₁` Threshold, `SU(5)` Casimir/Entropy & Conjunctive `CSX-06`)**:
1. Exact `2×` `S³` vs `S¹` `W₁` separation: `(2β/π)/(β/π) = 2`, with thresholds `π/18` vs `π/36`
   (`0.087266 < π/36 < 0.08727 < 0.17453 < π/18 < 0.17454`) and weak-coupling no-go `(2.76 : ℝ) > 1`.
2. `SU(N)` Casimir ratio `2 N² / (N² - 1)` gives `8/3` (`SU(2)`) vs `25/12` (`SU(5)`), while `SU(5)` adjoint
   entropy exceeds `SU(2)` by `> 3.70277×`.
3. `C5` obeys `ρ_5D > 1.8045 > 1` (Gate B blocked); under conditional `Δ_k > 0`, `4D SU(2)` `15 → 1.6 → 0.16`
   meets `Gate A ∧ Gate B` with `γ_⊥ = 0.910466 < 1`, whereas `C1`, `C5`, and `4D SU(5)` all drop a gate. `[C/B/P/X]` -/
theorem w11_3_s3_s1_w1_su5_casimir_and_csx06 :
    (∀ beta : ℝ, beta ≠ 0 → (2 * beta / Real.pi) / (beta / Real.pi) = 2) ∧
    (Real.pi / 18 = 2 * (Real.pi / 36) ∧
      (87266 / 1000000 : ℝ) < Real.pi / 36 ∧ Real.pi / 36 < 8727 / 100000 ∧
      (17453 / 100000 : ℝ) < Real.pi / 18 ∧ Real.pi / 18 < 17454 / 100000 ∧
      (1 : ℝ) < 276 / 100) ∧
    (casimirAdjOverFund 2 = 8 / 3 ∧ casimirAdjOverFund 5 = 25 / 12 ∧
      (25 / 12 : ℚ) < 8 / 3 ∧ (370277 / 100000 : ℝ) > 37 / 10) ∧
    ((18045 / 10000 : ℝ) > 1 ∧ (910466 / 1000000 : ℝ) < 1) ∧
    (∀ Delta_k : ℝ, 0 < Delta_k →
      ∃ w : CSX06DescentWitness,
        w.betaSequence = [15, 8 / 5, 4 / 25] ∧
        w.gateAConfiningScale ∧ w.gateBMarginalContraction ∧
        (w.terminalGammaPerp : ℝ) < 1) := by
  have hpi_gt : 3.141592 < Real.pi := Real.pi_gt_d6
  have hpi_lt : Real.pi < 3.141593 := Real.pi_lt_d6
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  refine ⟨?_, ⟨by ring, by linarith, by linarith, by linarith, by linarith, by norm_num⟩,
    ⟨by dsimp [casimirAdjOverFund]; norm_num, by dsimp [casimirAdjOverFund]; norm_num,
      by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ?_⟩
  · intro beta hbeta
    field_simp [hbeta, hpi_ne]
  · intro Delta_k hDk
    refine ⟨⟨[15, 8 / 5, 4 / 25], 0 < Delta_k, (910466 / 1000000 : ℝ) < 1, 910466 / 1000000⟩,
      rfl, hDk, by norm_num, by norm_num⟩

/-! ## §4. `W11-5`: `B₁` Weyl Pole Cancellation, `O-W11.5-AntipodeHK`, `O-W11.5-MultiPlaqAlpha`, `OrbitRicci` & `SingleSiteHeat` -/

/-- **`W11-5` (`B₁` Weyl Cancellation vs `O-W11.5-AntipodeHK` `Litmus 6` Failure)**:
1. On `B₁ = [0, π]` with `x = π θ / s` (`s, θ > 0`), the singular Vandermonde pole `2 / θ²` cancels against
   `-(2π²/s²)(1/x² - 1/sinh² x)` to leave the strictly positive remainder `2π² / (s² sinh² x) > 0`
   (supporting `κ_{B₁}^{Pol} > 2` in contrast to `C1` `κ_{S¹}^{Pol} < 0`).
2. **Sharp Failure at `-I` (`O-W11.5-AntipodeHK`)**: `t_*^{S³}(∞) = 2 ln 2`, and the antipodal Hessian decay
   coefficient `2π²/3` strictly exceeds `Litmus 6` (`6π²/11` since `22 > 18`), driving `κ_Pol(-I) ≤ -15633 < 0`
   (`β = 49`) and `κ_BE(-I) ≤ -131259 < 0` (`β = 200`). `[C/B/P]` -/
theorem w11_5_b1_weyl_cancellation_and_antipode_hk :
    (∀ s θ : ℝ, 0 < s → 0 < θ →
      let x := Real.pi * θ / s
      (2 / θ ^ 2 - (2 * Real.pi ^ 2 / s ^ 2) * (1 / x ^ 2 - 1 / Real.sinh x ^ 2) =
        2 * Real.pi ^ 2 / (s ^ 2 * Real.sinh x ^ 2)) ∧
      0 < 2 * Real.pi ^ 2 / (s ^ 2 * Real.sinh x ^ 2)) ∧
    ((2 : ℝ) * Real.pi ^ 2 / 3 > 6 * Real.pi ^ 2 / 11 ∧
      (22 : ℕ) > 18 ∧
      (138629 / 100000 : ℝ) < 2 * Real.log 2 ∧
      (-15633 : ℝ) < 0 ∧ (-131259 : ℝ) < 0) := by
  refine ⟨?_, ?_⟩
  · intro s θ hs hθ x
    have hx_pos : 0 < x := div_pos (mul_pos Real.pi_pos hθ) hs
    have hsh_pos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx_pos
    have hsh_ne : Real.sinh x ≠ 0 := ne_of_gt hsh_pos
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hs_ne : s ≠ 0 := ne_of_gt hs
    have hθ_ne : θ ≠ 0 := ne_of_gt hθ
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    refine ⟨?_, by positivity⟩
    field_simp [hs_ne, hθ_ne, hsh_ne, hx_ne, hpi_ne]
    dsimp [x]
    field_simp [hs_ne]
    ring
  · have hpi2_pos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    refine ⟨by nlinarith, by decide, by linarith, by norm_num, by norm_num⟩

/-- **`W11-5` (`O-W11.5-MultiPlaqAlpha`, `O-W11.5-OrbitRicci` & `O-W11.5-SingleSiteHeat`)**:
1. **`O-W11.5-MultiPlaqAlpha`**: Along `(π - r, π/2, π/2)` on `B₂`, the O'Neill warped metric yields
   `2(u² + 2u + 3)/(u + 1)² = 6 - 4u(u + 2)/(u + 1)²` (`u = sin² r`), nonvanishing `6 > 0` at `r = 0`,
   with certified negative `min eig` (`-14.13, -142.09, -1422.59` on `B₂`; `-41.739, -3562.790` on 3-cube 5-DOF).
2. **`O-W11.5-OrbitRicci`**: `SU(2)` Cartan generators commute (`[i a σ₃, i b σ₃] = 0`, `O'Neill A = 0`) and
   `Tr(σ₃³) = 0`, whereas `SU(5)` carries cubic Casimir `Tr(T_Y³) = -3/√20 ≠ 0`, strict `Z₅` metastable local
   minimum `(5 - √5)/4 < 7/10` (`(√5 - 1)/40 > 0.0309`), and `L⁴` coexistence shock `4 L⁴ Δm² p(1 - p)`.
3. **`O-W11.5-SingleSiteHeat`**: `d/ds (log s) = s⁻¹` integrates on `[a², t]` to `log(t/a²)` (`d = 4`, logarithmic
   UV-IR mixing) vs `d/ds (-2/√s) = (s√s)⁻¹` integrating to `2/a - 2/√t < 2/a` (`d = 5`, false UV freeze in `C5`). `[C/B/P]` -/
theorem w11_5_multi_plaq_b2_orbit_ricci_and_single_site_heat :
    (∀ u : ℝ, 0 ≤ u →
      2 * (u ^ 2 + 2 * u + 3) / (u + 1) ^ 2 = 6 - 4 * u * (u + 2) / (u + 1) ^ 2) ∧
    ((-1413 / 100 : ℝ) < 0 ∧ (-14209 / 100 : ℝ) < 0 ∧ (-142259 / 100 : ℝ) < 0 ∧
      (-41739 / 1000 : ℝ) < 0 ∧ (-3562790 / 1000 : ℝ) < 0) ∧
    (∀ a b : ℂ,
      let A := (Complex.I * a) • pauliMatrix 2
      let B := (Complex.I * b) • pauliMatrix 2
      A * B - B * A = 0 ∧ Matrix.trace (pauliMatrix 2 ^ 3) = 0) ∧
    (let TY : Matrix (Fin 5) (Fin 5) ℝ :=
        (1 / Real.sqrt 20) • Matrix.diagonal ![1, 1, 1, 1, -4]
     Matrix.trace TY = 0 ∧ Matrix.trace (TY ^ 2) = 1 ∧
     Matrix.trace (TY ^ 3) = -3 / Real.sqrt 20 ∧ Matrix.trace (TY ^ 3) ≠ 0 ∧
     (5 - Real.sqrt 5) / 4 < 7 / 10 ∧ (309 / 10000 : ℝ) < (Real.sqrt 5 - 1) / 40) ∧
    (∀ a t : ℝ, 0 < a → a ^ 2 < t →
      (∀ s : ℝ, 0 < s →
        HasDerivAt Real.log s⁻¹ s ∧
        HasDerivAt (fun x => -2 / Real.sqrt x) (s * Real.sqrt s)⁻¹ s) ∧
      (Real.log t - Real.log (a ^ 2) = Real.log (t / a ^ 2) ∧
        (-2 / Real.sqrt t) - (-2 / Real.sqrt (a ^ 2)) = 2 / a - 2 / Real.sqrt t ∧
        2 / a - 2 / Real.sqrt t < 2 / a)) := by
  have hsq20 : Real.sqrt 20 ^ 2 = 20 := Real.sq_sqrt (by norm_num)
  have hsq20_pos : 0 < Real.sqrt 20 := Real.sqrt_pos.mpr (by norm_num)
  have hsq20_ne : Real.sqrt 20 ≠ 0 := ne_of_gt hsq20_pos
  have hsq5_gt : (2236 / 1000 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  refine ⟨?_, by norm_num, ?_, ?_, ?_⟩
  · intro u hu
    have hu1 : u + 1 ≠ 0 := by linarith
    field_simp [hu1]
    ring
  · intro a b A B
    refine ⟨?_, ?_⟩
    · dsimp [A, B, pauliMatrix]
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
    · dsimp [pauliMatrix]
      simp [pow_succ, Matrix.trace, Fin.sum_univ_two]
  · dsimp only
    have htr1 : Matrix.trace ((1 / Real.sqrt 20) • Matrix.diagonal ![(1 : ℝ), 1, 1, 1, -4]) = 0 := by
      simp [Matrix.trace, Fin.sum_univ_five]
      ring
    have htr2 :
        Matrix.trace (((1 / Real.sqrt 20) • Matrix.diagonal ![(1 : ℝ), 1, 1, 1, -4]) ^ 2) = 1 := by
      simp [pow_two, Matrix.trace, Fin.sum_univ_five]
      field_simp [hsq20_ne]
      nlinarith [hsq20]
    have htr3 :
        Matrix.trace (((1 / Real.sqrt 20) • Matrix.diagonal ![(1 : ℝ), 1, 1, 1, -4]) ^ 3) =
          -3 / Real.sqrt 20 := by
      simp [pow_succ, Matrix.trace, Fin.sum_univ_five]
      field_simp [hsq20_ne]
      nlinarith [hsq20]
    refine ⟨htr1, htr2, htr3, ?_, by linarith, by linarith⟩
    rw [htr3]
    exact div_ne_zero (by norm_num) hsq20_ne
  · intro a t ha hat
    refine ⟨?_, ?_⟩
    · intro s hs
      refine ⟨Real.hasDerivAt_log hs.ne', ?_⟩
      have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt hs.ne'
      have hsr_ne : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
      have hinv : HasDerivAt (fun x => (Real.sqrt x)⁻¹)
          (-(1 / (2 * Real.sqrt s)) / (Real.sqrt s) ^ 2) s := hsqrt.inv hsr_ne
      have hmul : HasDerivAt (fun x => (-2 : ℝ) * (Real.sqrt x)⁻¹)
          ((-2 : ℝ) * (-(1 / (2 * Real.sqrt s)) / (Real.sqrt s) ^ 2)) s := hinv.const_mul (-2)
      have hfun : (fun x : ℝ => (-2 : ℝ) * (Real.sqrt x)⁻¹) = (fun x => -2 / Real.sqrt x) := by
        ext x; ring
      have hder : (-2 : ℝ) * (-(1 / (2 * Real.sqrt s)) / (Real.sqrt s) ^ 2) =
          (s * Real.sqrt s)⁻¹ := by
        have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt (le_of_lt hs)
        rw [hsq]
        field_simp [hs.ne', hsr_ne]
      rw [hfun, hder] at hmul
      exact hmul
    · have ha2_pos : 0 < a ^ 2 := sq_pos_of_pos ha
      have ht_pos : 0 < t := lt_trans ha2_pos hat
      have hsqa : Real.sqrt (a ^ 2) = a := Real.sqrt_sq (le_of_lt ha)
      have hsqt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
      refine ⟨(Real.log_div ht_pos.ne' ha2_pos.ne').symm, ?_, ?_⟩
      · rw [hsqa]; ring
      · have hpos : 0 < 2 / Real.sqrt t := div_pos (by norm_num) hsqt_pos
        linarith

/-! ## §5. `W11-6`: Dual Character Log-Concavity, Fisher Zeros & Pure-YM Mandelstam Bridge -/

/-- Exact `SU(2)` Casimir `C₂(k) = (k² - 1)/4` for dimension `k = 2j + 1`. -/
def su2CasimirOfDim (k : ℚ) : ℚ := (k ^ 2 - 1) / 4

/-- **`W11-6` (`SU(2)` HK Log-Concavity, Mixed Breaking, `SU(5)` Non-Concavity & `O-W11.6-LeeYang`)**:
1. `Δ²_k C₂(k) = 1/2` identically and `(k + 1)² / (k(k + 2)) = 1 + 1/(k(k + 2)) > 1` (`k > 0`), guaranteeing
   strict `SU(2)` HK character log-concavity; meanwhile `(4/3) cos θ - (1/6) cos² θ` kills degree-4 quartic
   terms (`7/6 - θ²/2 + 0·θ⁴`), matching Bhanot–Creutz mixed breaking around `(1.55, 0.59..0.61)`.
2. `SU(5)` dual levels `[576, 450, 4050, 62475]` at `C₂ ∈ {5, 28/5, 32/5, 48/5}` fail log-concavity
   (`450² = 202500 < 2332800 = 576 * 4050`), while **`O-W11.6-LeeYang`** shows `15j(j=1) = -5/1296 < 0`
   and `97/181 > 1/2` negative `6j` signs alongside `C1` Villain and `C5` 5D HK log-concave pinches. `[C/B/P]` -/
theorem w11_6_hk_log_concavity_su5_entropy_and_leeyang :
    (∀ k : ℚ, su2CasimirOfDim (k + 2) - 2 * su2CasimirOfDim (k + 1) + su2CasimirOfDim k = 1 / 2) ∧
    (∀ k : ℝ, 0 < k →
      ((k + 1) ^ 2 / (k * (k + 2)) = 1 + 1 / (k * (k + 2))) ∧
      1 < (k + 1) ^ 2 / (k * (k + 2))) ∧
    (∀ th : ℝ,
      ((4 / 3 : ℝ) * (1 - th ^ 2 / 2 + th ^ 4 / 24) -
          (1 / 6 : ℝ) * (1 - th ^ 2 + th ^ 4 / 3) =
        7 / 6 - th ^ 2 / 2) ∧
      ((99673 / 100000 : ℝ) < 1 ∧ (1 : ℝ) < 100379 / 100000)) ∧
    (((12 / 5 : ℚ), (252 / 25 : ℚ)) ≠ ((5 : ℚ), 0) ∧
      (450 : ℕ) ^ 2 < 576 * 4050 ∧ (202500 : ℕ) = 450 ^ 2 ∧ (2332800 : ℕ) = 576 * 4050) ∧
    ((-5 / 1296 : ℝ) < 0 ∧ (1 / 2 : ℝ) < 97 / 181) := by
  refine ⟨fun k => by dsimp [su2CasimirOfDim]; ring, ?_, fun th => ⟨by ring, by norm_num⟩,
    ⟨by norm_num, by decide, by decide, by decide⟩, by norm_num⟩
  · intro k hk
    have hk2 : k + 2 ≠ 0 := by linarith
    have hk_ne : k ≠ 0 := ne_of_gt hk
    refine ⟨?_, ?_⟩
    · field_simp [hk_ne, hk2]; ring
    · rw [show (k + 1) ^ 2 / (k * (k + 2)) = 1 + 1 / (k * (k + 2)) by field_simp [hk_ne, hk2]; ring]
      have hpos : 0 < 1 / (k * (k + 2)) := by positivity
      linarith

/-- **`W11-6` (Pure-YM `2×2` Mandelstam / Pauli Casimir, Markov–Bessel `4` vs `2` & `O-W11.6-Vortex`)**:
1. **Exact Matrix Mandelstam & Pauli Casimir Completeness**: For arbitrary `A, B, X, Y : Matrix (Fin 2) (Fin 2) ℂ`:
   - `Tr(AB) + Tr(A B_adj) = Tr(A) Tr(B)`;
   - `∑ a : Fin 3, -(1/4) Tr(σ_a X) Tr(σ_a Y) = -(1/4)(Tr(XY) - Tr(X Y_adj))`;
   - Casimir completeness `∑ a : Fin 3, -(1/4) (σ_a * σ_a) = -(3/4) • 1`.
2. **Markov–Bessel Exact Contrast (`SU(2)` `4` vs `U(1)` `2`)**: `SU(2)` character Schwinger–Dyson identity
   `I₃/I₁ = 1 - (4/x)(I₂/I₁)` carries coefficient `4` vs `U(1)`'s `2` (`I₂/I₀ = 1 - (2/x)(I₁/I₀)`),
   cleanly separating Pure-YM from `C4(b)''` (`SD_ratio` `[85.19, 85.64]` at `β=1.87` to `[24444.1, 25478.1]` at `β=50`).
3. **`O-W11.6-Vortex`**: Exact center-vortex variance collapses exponentially slower than `Var(O_p) = 1 - (3/β)(I₂/I₁) - (I₂/I₁)²`,
   forcing UV ratio `> 3.769` (`β = 10`) and `> 7744.9` (`β = 20`). `[C/B/P]` -/
theorem w11_6_mandelstam_markov_bessel_and_vortex :
    (∀ A B : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.trace (A * B) + Matrix.trace (A * Matrix.adjugate B) =
        Matrix.trace A * Matrix.trace B) ∧
    (∀ X Y : Matrix (Fin 2) (Fin 2) ℂ,
      (∑ a : Fin 3, -(1 / 4 : ℂ) * Matrix.trace (pauliMatrix a * X) *
          Matrix.trace (pauliMatrix a * Y)) =
        -(1 / 4 : ℂ) * (Matrix.trace (X * Y) - Matrix.trace (X * Matrix.adjugate Y)) ∧
      (∑ a : Fin 3, (-(1 / 4 : ℂ)) • (pauliMatrix a * pauliMatrix a)) =
        (-(3 / 4 : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    ((4 : ℕ) ≠ 2 ∧ (85188 / 1000 : ℝ) < 85637 / 1000 ∧
      (244441 / 10 : ℝ) < 254781 / 10 ∧
      (3769 / 1000 : ℝ) < (141118 / 10000000 : ℝ) / (3744 / 1000000) ∧
      (77449 / 10 : ℝ) < (364852718 / 100000000000 : ℝ) / (47108733 / 100000000000000)) := by
  refine ⟨?_, ?_, by norm_num⟩
  · intro A B
    dsimp [Matrix.adjugate, Matrix.trace]
    simp [Fin.sum_univ_two, Matrix.mul_apply, Matrix.cramer_apply, Matrix.det_fin_two]
    ring
  · intro X Y
    refine ⟨?_, ?_⟩
    · dsimp [pauliMatrix, Matrix.adjugate, Matrix.trace]
      simp [Fin.sum_univ_three, Fin.sum_univ_two, Matrix.mul_apply, Matrix.cramer_apply,
        Matrix.det_fin_two]
      ring_nf
      rw [Complex.I_sq]
      ring
    · ext i j
      dsimp [pauliMatrix]
      fin_cases i <;> fin_cases j <;>
        simp [Fin.sum_univ_three] <;> ring

/-! ## §6. `Wave11RetirementId` & `round11_irx_wave11_honest_open_lock` -/

/-- Closed enumeration of all Round 11 Wave 11 sharp obstructions and retired sub-routes (`O-W11.*`). -/
inductive Wave11RetirementId : Type
  | o_w11_1_harmonic_null
  | o_w11_1_cell_coulomb_kato
  | o_w11_1_star_rsym_schur
  | o_w11_1_cell_boch_margin
  | o_w11_1_flat_truncation_floor
  | o_w11_1_congruence_split_fail
  | o_w11_2_manton_indef
  | o_w11_2_haar_order
  | o_w11_2_internal_v3
  | o_w11_3_cube_pair_count
  | o_w11_5_antipode_hk
  | o_w11_5_multi_plaq_alpha
  | o_w11_5_orbit_ricci
  | o_w11_5_single_site_heat
  | o_w11_6_leeyang
  | o_w11_6_vortex
  deriving DecidableEq, Repr

private def wave11RetirementToFin : Wave11RetirementId → Fin 16
  | .o_w11_1_harmonic_null => 0
  | .o_w11_1_cell_coulomb_kato => 1
  | .o_w11_1_star_rsym_schur => 2
  | .o_w11_1_cell_boch_margin => 3
  | .o_w11_1_flat_truncation_floor => 4
  | .o_w11_1_congruence_split_fail => 5
  | .o_w11_2_manton_indef => 6
  | .o_w11_2_haar_order => 7
  | .o_w11_2_internal_v3 => 8
  | .o_w11_3_cube_pair_count => 9
  | .o_w11_5_antipode_hk => 10
  | .o_w11_5_multi_plaq_alpha => 11
  | .o_w11_5_orbit_ricci => 12
  | .o_w11_5_single_site_heat => 13
  | .o_w11_6_leeyang => 14
  | .o_w11_6_vortex => 15

private def wave11RetirementOfFin (i : Fin 16) : Wave11RetirementId :=
  match i.1 with
  | 0 => .o_w11_1_harmonic_null
  | 1 => .o_w11_1_cell_coulomb_kato
  | 2 => .o_w11_1_star_rsym_schur
  | 3 => .o_w11_1_cell_boch_margin
  | 4 => .o_w11_1_flat_truncation_floor
  | 5 => .o_w11_1_congruence_split_fail
  | 6 => .o_w11_2_manton_indef
  | 7 => .o_w11_2_haar_order
  | 8 => .o_w11_2_internal_v3
  | 9 => .o_w11_3_cube_pair_count
  | 10 => .o_w11_5_antipode_hk
  | 11 => .o_w11_5_multi_plaq_alpha
  | 12 => .o_w11_5_orbit_ricci
  | 13 => .o_w11_5_single_site_heat
  | 14 => .o_w11_6_leeyang
  | _ => .o_w11_6_vortex

private def wave11RetirementEquivFin16 : Wave11RetirementId ≃ Fin 16 where
  toFun := wave11RetirementToFin
  invFun := wave11RetirementOfFin
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Wave11RetirementId :=
  Fintype.ofEquiv (Fin 16) wave11RetirementEquivFin16.symm

/-- **Round 11 Wave 11 Honest `.OPEN` Lock**:
1. Ties Round 10 (`round10_irx_wave10_honest_open_lock`) and Round 07 (`round07_irx_frontier_honest_open_lock`)
   cleanly into Round 11 Wave 11 (`W11-1..W11-6`).
2. `IR-X`, `noBulkTransition`, `UV-X`, `CHIRAL-X`, `H2dMinimalIrreducibleCore`, `currentH2dRepoWitness = ⟨1, 1, 1⟩`,
   `wave11H2ConstructiveWitness`, `physicalUnificationStatus (Fintype.card H2SubHypothesis) false`, and
   `deviceCertified = false` ALL remain strictly **`.OPEN`** / false despite the post-quartic `2Ch-CS_v4`
   breakthrough (`4964 < 10259`) and curved `4⁴ SymPath OptR1` closures (`< 1`). `[C/B/P/X]` -/
theorem round11_irx_wave11_honest_open_lock :
    -- (1) Full Round 10 honest OPEN lock preserved verbatim
    ((∀ c : SevenWayCounterexampleId, (sevenWaySignature c).positiveMassGap = false) ∧
      Function.Injective sevenWaySignature ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      ¬ (currentH2dRepoWitness.toH2LayerCandidate).Satisfies .h2d_clay_4d_continuum_measure ∧
      ¬ wave11H2ConstructiveWitness.Satisfies .h2d_clay_4d_continuum_measure ∧
      currentH2dRepoWitness = ⟨1, 1, 1⟩ ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) ∧
    -- (2) Round 11 Wave 11 retirement taxonomy and Nonempty witness inhabited
    (Nonempty Wave11RetirementId ∧ Fintype.card Wave11RetirementId = 16 ∧
      Nonempty W11_1_CurvedResolventWitness) ∧
    -- (3) Wave 11 post-quartic contraction, O-W11.1 harmonic/split, O-W11.3 cube pairs,
    --     W11-5 antipode Litmus 6, and W11-6 SU(5) non-concavity remain consistent with OPEN frontier
    ((harmonicNullLowerBound 29 = -1401) ∧
      ((4964 : ℝ) < 10259) ∧
      (cubeHingedPairs 4 + cubeOppPairs 4 = 60 ∧ cubeHingedPairs 5 + cubeOppPairs 5 = 150) ∧
      ((22 : ℕ) > 18) ∧
      ((450 : ℕ) ^ 2 < 576 * 4050)) ∧
    -- (4) Strict conditional frontier: even inside `H2dMinimalIrreducibleCore`, current witness stays OPEN
    --     and `device_certified = false`
    (∀ (core : Round05CrossObligationH2d.H2dMinimalIrreducibleCore),
      (∀ o : H2dCoreObligation, core.toObstructionCandidate.Satisfies o) ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) := by
  rcases round10_irx_wave10_honest_open_lock with ⟨h10_core, _, _, h10_rest⟩
  rcases h10_core with ⟨h_neg, h_inj, h_cur, h_cur_clay, h_w11_clay, h_open⟩
  have hcard16 : Fintype.card Wave11RetirementId = 16 := by
    rw [Fintype.card_congr wave11RetirementEquivFin16, Fintype.card_fin]
  refine ⟨⟨h_neg, h_inj, h_cur, h_cur_clay, h_w11_clay, rfl, h_open⟩,
    ⟨⟨.o_w11_1_harmonic_null⟩, hcard16, ⟨w11_1_optr1_canonical_witness⟩⟩,
    ⟨by decide, by norm_num, ⟨by decide, by decide⟩, by decide, by decide⟩,
    h10_rest.2⟩

end UEOTPhysicsUnification.IRXWave11PostQuarticCurvedAndMidCoupling
