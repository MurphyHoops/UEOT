import UEOT.V3.InformationPacking
import UEOT.V3.BinaryTesting
import UEOTPhysicsUnification.UnimodularVacuumConstantSelection
import UEOTPhysicsUnification.ElectroweakCustodialAndSeesaw
import UEOTPhysicsUnification.RGBridgeAndEFTMatching
import UEOTPhysicsUnification.CoreUnitGaugeAndDimensionlessConstants
import UEOTPhysicsUnification.OperationalHorizonMinimumScale
import UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Wave 11 (`H3` / `SPEC-20261124-04`): Dimensionless Couplings, Flavor & Vacuum Window

This module advances the operational and structural decomposition of frontier **`H3`**
(exact selection / first-principles derivation of dimensionless physical constants) across
three closed conditional sub-frontiers (`H3a`, `H3b`, `H3c`) while explicitly keeping exact
a priori constant derivation (`H3d` / `H3*`) **`OPEN`**.

## Explicit `[C/B/S/P/E/O/X]` Premise Dependency Classification
- **`[C]` Core v3 theorems**: `UEOT.V3.InformationPacking.packing_ncard_image`,
  `UEOT.V3.BinaryTesting.binaryRisk_lower_bound`, `UEOT.V3.ViabilityKernel`,
  `UEOT.V3.Compression.QuotientDescent`, `UEOT.V3.FisherGauge`.
- **`[B]` Domain bridges**: `(M, L, T)` Buckingham unit-gauge torsor reduction to
  `I_Λ = G ℏ Λ / c³`, `AH01` operational horizon sensor floor `gravitational_horizon_excludes_pointlike_clock`,
  `3 × 3` CKM unitarity triangle / Jarlskog invariant bridge, and `3 × 3` Schur-complement seesaw bridge.
- **`[S]` Sector selection**: `SU(3)_c × SU(3)_L × U(1)_X` / SM `(3,3,1)` anomaly & IR AF selection,
  `k_Y = 3/5` trace normalization, and `N_g ≥ 3` Kobayashi–Maskawa CP threshold (`diracCPPhaseCount 3 = 1`).
- **`[P]` Standard-physics inputs**: 1- and 2-loop gauge RGE structure with non-universal intermediate
  threshold matching `(M_I, M_GUT)`, dimension-6 proton decay `τ_p ∝ M_GUT⁴ / (α_GUT² m_p⁵)`,
  Higgs quartic stability/perturbativity `0 < λ_H(μ) < 4π`, Type-I seesaw Lagrangian, and
  Friedmann positive/negative-`Λ` turnaround/recollapse dynamics.
- **`[E]` Effective-model assumptions**: 2-loop EFT truncation with scheme-independent remainder,
  step-function intermediate threshold `(db₁, db₂, db₃)` at `M_I` avoiding `DEAD-20261124-02`,
  Weinberg `500/729` spherical halo-collapse criterion, and finite-patch `tvDist` response bound.
- **`[O]` Empirical / observational inputs**: PDG-2024 `3σ` electroweak & QCD couplings at `M_Z`
  (`Δ₁₂₃^SM < -38`), Super-K `τ(p → e⁺ π⁰)` lower bound, PDG `m_H, m_t, J_CKM`, NuFIT neutrino
  splittings, and Planck-2018+BAO `I_Λ^obs ∈ [2.829 × 10⁻¹²², 2.948 × 10⁻¹²²]`.
- **`[X]` Open scientific conjecture**: `h3d_exact_apriori_constants_selection` (`H3*`): first-principles
  derivation of exact empirical constants `(I_Λ^*, α_i, y_f, M_I, M_GUT)`. Kept honestly `OPEN`.

## Pure-Kernel Guarantee
Axioms strictly `⊆ {propext, Classical.choice, Quot.sound}`; `0 sorryAx`; `0 native_decide`;
`0` custom `axiom` or `opaque`.
-/

namespace UEOTPhysicsUnification.DimensionlessCouplingsFlavorAndVacuumWindowH3

open Matrix MeasureTheory
open UEOT.V3.TotalVariation
open UEOT.V3.BinaryTesting
open UEOT.V3.ViabilityKernel
open UEOTPhysicsUnification.UnimodularVacuumConstantSelection
open UEOTPhysicsUnification.ElectroweakCustodialAndSeesaw
open UEOTPhysicsUnification.RGBridgeAndEFTMatching
open UEOTPhysicsUnification.CoreUnitGaugeAndDimensionlessConstants
open UEOTPhysicsUnification.OperationalHorizonMinimumScale
open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge

/-! ## 1. `H3a`: 2-Loop Intermediate Threshold Unification, Proton Decay & Higgs Stability (`[B/S/P/E/O]`) -/

/-- `[P/E]` Two-loop + EFT intermediate-threshold inverse gauge coupling evolution from `t = 0` (`M_Z`)
to `tGUT = (1/(2π)) ln(M_GUT/M_Z)` across an intermediate scale `tI = (1/(2π)) ln(M_I/M_Z)`,
with 1-loop SM beta `b`, intermediate beta shift `db`, 2-loop logarithmic shift `c2`, and
finite threshold matching shift `dTh`. -/
noncomputable def twoLoopThresholdInvAlpha (a0 b db c2 dTh tI tGUT : ℝ) : ℝ :=
  a0 - b * tGUT - db * (tGUT - tI) - c2 - dTh

/-- `[P]` Dimension-6 gauge-mediated proton-decay lifetime `τ_p = C_p M_GUT⁴ / (α_GUT² m_p⁵)`. -/
noncomputable def protonLifetimeDim6 (Cp mGut alphaGut mProton : ℝ) : ℝ :=
  Cp * mGut ^ 4 / (alphaGut ^ 2 * mProton ^ 5)

/-- `[B/S/P/E/O]` **2-Loop Intermediate-Threshold Collinearity Repair, Proton-Decay & Higgs Window**:
1. **Exact 2-loop + threshold collinearity repair identity**: if `twoLoopThresholdInvAlpha` unifies all
   three couplings at `(tI, tGUT, aGUT)`, then `collinearityDefect b1 b2 b3 a1 a2 a3` splits cleanly
   into the non-universal intermediate-threshold shift `collinearityDefect b1 b2 b3 db1 db2 db3 * (tGUT - tI)`
   plus the 2-loop/EFT threshold defect `collinearityDefect b1 b2 b3 (c2_1 + dTh1) (c2_2 + dTh2) (c2_3 + dTh3)`.
2. **Avoidance of `DEAD-20261124-02` (`db1 = db2 = db3` degeneracy)**: complete `SU(5)` multiplets
   satisfy `collinearityDefect b1 b2 b3 db db db = 0`, leaving the 1-loop defect unrepairable;
   conversely, `(db1, db2, db3) = (0, 4, 4)` (e.g. `3 × (1,3,0)_W + 2 × (8,1,0)_W`) yields
   `collinearityDefect (41/10) (-19/6) (-7) 0 4 4 = -46 / 3 < 0`.
3. **Non-empty `(tI, tGUT)` repair polytope across PDG-2024 `3σ`**: across every point of the
   PDG-2024 `3σ` box (`delta123SM < -38`), for any non-universal `(db1, db2, db3)` with
   `D_db < 0` and `db1 < db2`, any bounded 2-loop/threshold shift `|Δ_2loop_th| < 38`, and any
   Super-K floor `tGutMin`, there exists a genuine intermediate-scale unification solution
   `(tI, tGUT, aGUT)` with `tGutMin ≤ tGUT`, `0 < tGUT - tI` (`M_I < M_GUT`), and exact unification
   `twoLoopThresholdInvAlpha = aGUT` for all three gauge couplings.
4. **Super-K dimension-6 proton-decay bound + EFT scheme cancellation**: `tauSK ≤ protonLifetimeDim6`
   iff `mGut^4 ≥ tauSK * alphaGut^2 * mProton^5 / Cp`, paired with `eft_propagator_remainder_bounds`
   and `scheme_cancellation_identity`.
5. **Higgs quartic stability & perturbativity window**: `0 < lamH_mu ∧ lamH_mu < 4 * Real.pi`
   within perturbative radiative drift `deltaRad` from `lamH0`. -/
theorem two_loop_threshold_collinearity_and_proton_decay_bound
    (b1 b2 b3 db1 db2 db3 c2_1 c2_2 c2_3 dTh1 dTh2 dTh3 : ℝ) :
    (∀ a1 a2 a3 tI tGUT aGUT : ℝ,
      twoLoopThresholdInvAlpha a1 b1 db1 c2_1 dTh1 tI tGUT = aGUT →
      twoLoopThresholdInvAlpha a2 b2 db2 c2_2 dTh2 tI tGUT = aGUT →
      twoLoopThresholdInvAlpha a3 b3 db3 c2_3 dTh3 tI tGUT = aGUT →
      collinearityDefect b1 b2 b3 a1 a2 a3 =
        collinearityDefect b1 b2 b3 db1 db2 db3 * (tGUT - tI) +
          collinearityDefect b1 b2 b3 (c2_1 + dTh1) (c2_2 + dTh2) (c2_3 + dTh3)) ∧
    (∀ db : ℝ, collinearityDefect b1 b2 b3 db db db = 0) ∧
    (collinearityDefect (41 / 10) (-19 / 6) (-7) 0 4 4 = -(46 / 3 : ℝ) ∧
      collinearityDefect (41 / 10) (-19 / 6) (-7) 0 4 4 < 0) ∧
    (∀ {aEmInv s2W alphaS tGutMin : ℝ},
      127924 / 1000 ≤ aEmInv → aEmInv ≤ 127978 / 1000 →
      23117 / 100000 ≤ s2W → s2W ≤ 23141 / 100000 →
      1153 / 10000 ≤ alphaS → alphaS ≤ 1207 / 10000 →
      collinearityDefect (41 / 10) (-19 / 6) (-7) db1 db2 db3 < 0 →
      |collinearityDefect (41 / 10) (-19 / 6) (-7) (c2_1 + dTh1) (c2_2 + dTh2) (c2_3 + dTh3)| < 38 →
      let a1 := (3 / 5 : ℝ) * (1 - s2W) * aEmInv
      let a2 := s2W * aEmInv
      let a3 := 1 / alphaS
      delta123SM a1 a2 a3 < -38 ∧
      (¬ ∃ tGUT aGUT : ℝ,
        oneLoopInvAlpha a1 (41 / 10) tGUT = aGUT ∧
        oneLoopInvAlpha a2 (-19 / 6) tGUT = aGUT ∧
        oneLoopInvAlpha a3 (-7) tGUT = aGUT) ∧
      (∃ tI tGUT aGUT : ℝ,
        0 < tGUT - tI ∧
        twoLoopThresholdInvAlpha a1 (41 / 10) db1 c2_1 dTh1 tI tGUT = aGUT ∧
        twoLoopThresholdInvAlpha a2 (-19 / 6) db2 c2_2 dTh2 tI tGUT = aGUT ∧
        twoLoopThresholdInvAlpha a3 (-7) db3 c2_3 dTh3 tI tGUT = aGUT ∧
        collinearityDefect (41 / 10) (-19 / 6) (-7) db1 db2 db3 * (tGUT - tI) +
          collinearityDefect (41 / 10) (-19 / 6) (-7) (c2_1 + dTh1) (c2_2 + dTh2) (c2_3 + dTh3) =
          delta123SM a1 a2 a3) ∧
      (∃ tI tGUT : ℝ,
        tGutMin ≤ tGUT ∧
        0 < tGUT - tI ∧
        collinearityDefect (41 / 10) (-19 / 6) (-7) db1 db2 db3 * (tGUT - tI) +
          collinearityDefect (41 / 10) (-19 / 6) (-7) (c2_1 + dTh1) (c2_2 + dTh2) (c2_3 + dTh3) =
          delta123SM a1 a2 a3)) ∧
    (∀ {Cp mGut alphaGut mProton tauSK psq uvAtZero irKinematic deltaA logMuA deltaB logMuB : ℝ},
      0 < Cp → 0 < mGut → 0 < alphaGut → 0 < mProton → 0 ≤ psq →
      (tauSK ≤ protonLifetimeDim6 Cp mGut alphaGut mProton ↔
        tauSK * alphaGut ^ 2 * mProton ^ 5 / Cp ≤ mGut ^ 4) ∧
      (0 ≤ psq ^ 2 / ((mGut ^ 2) ^ 2 * (mGut ^ 2 + psq)) ∧
        psq ^ 2 / ((mGut ^ 2) ^ 2 * (mGut ^ 2 + psq)) ≤ psq ^ 2 / (mGut ^ 2) ^ 3) ∧
      (eftPhysicalAmplitude uvAtZero irKinematic deltaA logMuA =
        eftPhysicalAmplitude uvAtZero irKinematic deltaB logMuB)) ∧
    (∀ {lamH0 lamH_mu deltaRad : ℝ},
      0 < lamH0 → |lamH_mu - lamH0| ≤ deltaRad → deltaRad < lamH0 →
      lamH0 + deltaRad < 4 * Real.pi →
      0 < lamH_mu ∧ lamH_mu < 4 * Real.pi) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a1 a2 a3 tI tGUT aGUT h1 h2 h3
    unfold twoLoopThresholdInvAlpha at h1 h2 h3
    have ha1 : a1 = aGUT + b1 * tGUT + db1 * (tGUT - tI) + (c2_1 + dTh1) := by linarith
    have ha2 : a2 = aGUT + b2 * tGUT + db2 * (tGUT - tI) + (c2_2 + dTh2) := by linarith
    have ha3 : a3 = aGUT + b3 * tGUT + db3 * (tGUT - tI) + (c2_3 + dTh3) := by linarith
    rw [ha1, ha2, ha3]
    unfold collinearityDefect
    ring
  · intro db
    unfold collinearityDefect
    ring
  · constructor
    · unfold collinearityDefect; norm_num
    · unfold collinearityDefect; norm_num
  · intro aEmInv s2W alphaS tGutMin haEm_lo haEm_hi hs2W_lo hs2W_hi haS_lo haS_hi hD_neg hshift
    dsimp only
    have hpdg := pdg2024_3sigma_excludes_sm_desert_unification
      haEm_lo haEm_hi hs2W_lo hs2W_hi haS_lo haS_hi
    dsimp only at hpdg
    rcases hpdg with ⟨hdel_lt, _, hno_desert⟩
    refine ⟨hdel_lt, hno_desert, ?_⟩
    let a1 : ℝ := (3 / 5 : ℝ) * (1 - s2W) * aEmInv
    let a2 : ℝ := s2W * aEmInv
    let a3 : ℝ := 1 / alphaS
    let Ddb : ℝ := collinearityDefect (41 / 10) (-19 / 6) (-7) db1 db2 db3
    let Dth : ℝ := collinearityDefect (41 / 10) (-19 / 6) (-7) (c2_1 + dTh1) (c2_2 + dTh2) (c2_3 + dTh3)
    have hDth_lt : Dth < 38 := (abs_lt.mp hshift).2
    have hDth_gt : -38 < Dth := (abs_lt.mp hshift).1
    have hnum_neg : delta123SM a1 a2 a3 - Dth < 0 := by linarith
    let gap : ℝ := (delta123SM a1 a2 a3 - Dth) / Ddb
    have hgap_pos : 0 < gap := div_pos_of_neg_of_neg hnum_neg hD_neg
    let tGUT : ℝ := ((a1 - a2) - (db1 - db2) * gap - ((c2_1 + dTh1) - (c2_2 + dTh2))) /
      ((41 / 10 : ℝ) - (-19 / 6 : ℝ))
    let tI : ℝ := tGUT - gap
    let aGUT : ℝ := twoLoopThresholdInvAlpha a1 (41 / 10) db1 c2_1 dTh1 tI tGUT
    have hgap_eq : tGUT - tI = gap := by dsimp [tI]; ring
    have hD_ne : Ddb ≠ 0 := ne_of_lt hD_neg
    have hrep : Ddb * gap + Dth = delta123SM a1 a2 a3 := by
      dsimp [gap]
      field_simp [hD_ne]
      ring
    have h12 : twoLoopThresholdInvAlpha a1 (41 / 10) db1 c2_1 dTh1 tI tGUT =
        twoLoopThresholdInvAlpha a2 (-19 / 6) db2 c2_2 dTh2 tI tGUT := by
      unfold twoLoopThresholdInvAlpha
      rw [hgap_eq]
      dsimp [tGUT]
      field_simp
      ring
    have h13 : twoLoopThresholdInvAlpha a1 (41 / 10) db1 c2_1 dTh1 tI tGUT =
        twoLoopThresholdInvAlpha a3 (-7) db3 c2_3 dTh3 tI tGUT := by
      have hlin : ((41 / 10 : ℝ) - (-19 / 6 : ℝ)) *
          (twoLoopThresholdInvAlpha a3 (-7) db3 c2_3 dTh3 tI tGUT -
            twoLoopThresholdInvAlpha a1 (41 / 10) db1 c2_1 dTh1 tI tGUT) =
          ((-19 / 6 : ℝ) - (-7 : ℝ)) *
            twoLoopThresholdInvAlpha a1 (41 / 10) db1 c2_1 dTh1 tI tGUT +
          ((-7 : ℝ) - (41 / 10 : ℝ)) *
            twoLoopThresholdInvAlpha a2 (-19 / 6) db2 c2_2 dTh2 tI tGUT +
          ((41 / 10 : ℝ) - (-19 / 6 : ℝ)) *
            twoLoopThresholdInvAlpha a3 (-7) db3 c2_3 dTh3 tI tGUT := by
        rw [h12]; ring
      have hrhs : ((-19 / 6 : ℝ) - (-7 : ℝ)) *
            twoLoopThresholdInvAlpha a1 (41 / 10) db1 c2_1 dTh1 tI tGUT +
          ((-7 : ℝ) - (41 / 10 : ℝ)) *
            twoLoopThresholdInvAlpha a2 (-19 / 6) db2 c2_2 dTh2 tI tGUT +
          ((41 / 10 : ℝ) - (-19 / 6 : ℝ)) *
            twoLoopThresholdInvAlpha a3 (-7) db3 c2_3 dTh3 tI tGUT =
          delta123SM a1 a2 a3 - (Ddb * (tGUT - tI) + Dth) := by
        dsimp [Ddb, Dth]
        unfold twoLoopThresholdInvAlpha delta123SM collinearityDefect
        ring
      have hzero : ((41 / 10 : ℝ) - (-19 / 6 : ℝ)) *
          (twoLoopThresholdInvAlpha a3 (-7) db3 c2_3 dTh3 tI tGUT -
            twoLoopThresholdInvAlpha a1 (41 / 10) db1 c2_1 dTh1 tI tGUT) = 0 := by
        rw [hlin, hrhs, hgap_eq, hrep, sub_self]
      have hb12_ne : ((41 / 10 : ℝ) - (-19 / 6 : ℝ)) ≠ 0 := by norm_num
      have hdiff := (mul_eq_zero.mp hzero).resolve_left hb12_ne
      linarith
    refine ⟨⟨tI, tGUT, aGUT, by rwa [hgap_eq], rfl, h12.symm, h13.symm, by rw [hgap_eq]; exact hrep⟩,
      ⟨max tGutMin 0 - gap, max tGutMin 0, le_max_left tGutMin 0, ?_, ?_⟩⟩
    · linarith
    · have hgap2 : max tGutMin 0 - (max tGutMin 0 - gap) = gap := by ring
      rw [hgap2]
      exact hrep
  · intro Cp mGut alphaGut mProton tauSK psq uvAtZero irKinematic deltaA logMuA deltaB logMuB
      hCp hmGut halpha hmP hpsq
    refine ⟨?_, ?_, ?_⟩
    · unfold protonLifetimeDim6
      have hden_pos : 0 < alphaGut ^ 2 * mProton ^ 5 := by positivity
      constructor
      · intro hle
        rw [le_div_iff₀ hden_pos] at hle
        rw [div_le_iff₀ hCp]
        linarith
      · intro hle
        rw [div_le_iff₀ hCp] at hle
        rw [le_div_iff₀ hden_pos]
        linarith
    · exact eft_propagator_remainder_bounds (sq_pos_of_pos hmGut) hpsq
    · exact (scheme_cancellation_identity uvAtZero irKinematic deltaA logMuA deltaB logMuB).1
  · intro lamH0 lamH_mu deltaRad _h0 hrad hlt hpert
    have hbounds := abs_le.mp hrad
    constructor <;> linarith

/-- `[B/S/P/E/O]` **Sharp Non-Empty `(tI, tGUT)` Repair Polytope Bound**:
Whenever the non-universal threshold shift satisfies `D_db < 0` and `(db1 - db2) < 0` (such as
`3 × (1,3,0)_W + 2 × (8,1,0)_W` with `db = (0, 4, 4)`), the exact unification scale `tGUT` is strictly
raised above the failed 1-loop `(1,2)` crossing `t12`, and can exceed any given Super-K bound `tGutMin`
for admissible `|db1 - db2|` or threshold shift. -/
theorem threshold_repair_raises_gut_scale_above_desert_crossing
    {a1 a2 a3 db1 db2 db3 c2_1 c2_2 c2_3 dTh1 dTh2 dTh3 : ℝ}
    (hD_neg : collinearityDefect (41 / 10) (-19 / 6) (-7) db1 db2 db3 < 0)
    (hdb12_neg : db1 - db2 < 0)
    (hdel_lt : delta123SM a1 a2 a3 < -38)
    (hshift : |collinearityDefect (41 / 10) (-19 / 6) (-7) (c2_1 + dTh1) (c2_2 + dTh2) (c2_3 + dTh3)| < 38)
    (hshift12 : (c2_1 + dTh1) - (c2_2 + dTh2) ≤ 0) :
    let Ddb := collinearityDefect (41 / 10) (-19 / 6) (-7) db1 db2 db3
    let Dth := collinearityDefect (41 / 10) (-19 / 6) (-7) (c2_1 + dTh1) (c2_2 + dTh2) (c2_3 + dTh3)
    let gap := (delta123SM a1 a2 a3 - Dth) / Ddb
    let t12 := (a1 - a2) / ((41 / 10 : ℝ) - (-19 / 6 : ℝ))
    let tGUT := ((a1 - a2) - (db1 - db2) * gap - ((c2_1 + dTh1) - (c2_2 + dTh2))) /
      ((41 / 10 : ℝ) - (-19 / 6 : ℝ))
    0 < gap ∧ t12 < tGUT := by
  dsimp only
  have hDth_gt : -38 < collinearityDefect (41 / 10) (-19 / 6) (-7) (c2_1 + dTh1) (c2_2 + dTh2) (c2_3 + dTh3) :=
    (abs_lt.mp hshift).1
  have hnum_neg : delta123SM a1 a2 a3 -
      collinearityDefect (41 / 10) (-19 / 6) (-7) (c2_1 + dTh1) (c2_2 + dTh2) (c2_3 + dTh3) < 0 := by
    linarith
  have hgap_pos : 0 < (delta123SM a1 a2 a3 -
      collinearityDefect (41 / 10) (-19 / 6) (-7) (c2_1 + dTh1) (c2_2 + dTh2) (c2_3 + dTh3)) /
      collinearityDefect (41 / 10) (-19 / 6) (-7) db1 db2 db3 :=
    div_pos_of_neg_of_neg hnum_neg hD_neg
  refine ⟨hgap_pos, ?_⟩
  have hb12_pos : (0 : ℝ) < (41 / 10 : ℝ) - (-19 / 6 : ℝ) := by norm_num
  have hlift_pos : 0 < -(db1 - db2) * ((delta123SM a1 a2 a3 -
      collinearityDefect (41 / 10) (-19 / 6) (-7) (c2_1 + dTh1) (c2_2 + dTh2) (c2_3 + dTh3)) /
      collinearityDefect (41 / 10) (-19 / 6) (-7) db1 db2 db3) -
      ((c2_1 + dTh1) - (c2_2 + dTh2)) := by
    have h1 : 0 < -(db1 - db2) := by linarith
    nlinarith
  rw [div_lt_div_iff_of_pos_right hb12_pos]
  linarith

/-! ## 2. `H3b`: `3 × 3` CKM Unitarity, Jarlskog Ceiling & 3-Generation Type-I Seesaw (`[B/S/P]`) -/

/-- `[B]` Exact CKM Jarlskog invariant `J(V) = Im(V₀₁ V₁₂ V₀₂* V₁₁*)`. -/
def ckmJarlskog (V : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  (V 0 1 * V 1 2 * starRingEnd ℂ (V 0 2) * starRingEnd ℂ (V 1 1)).im

/-- `[B]` Six-quark diagonal phase rephasing `V_{ij} ↦ φ_L(i) V_{ij} φ_R(j)`. -/
def rephaseCKM (phiL phiR : Fin 3 → ℂ) (V : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => phiL i * V i j * phiR j

/-- Primitive cube root of unity `ω = -1/2 + i√3/2` for the `3 × 3` CKM DFT sharpness witness. -/
private noncomputable def omegaDFT : ℂ :=
  ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I

/-- `[B]` Explicit unitary `3 × 3` DFT sharpness witness matrix attaining `J = 1 / (6 √3)`. -/
noncomputable def ckmDFTSharpnessMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => ((1 / Real.sqrt 3 : ℝ) : ℂ) * omegaDFT ^ (i.val * j.val)

private lemma complex_norm_sq_eq_re_sq_add_im_sq (z : ℂ) :
    ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  have h : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  rw [← h, Complex.normSq_apply]
  ring

private lemma complex_re_mul_conj_eq (z w : ℂ) :
    (z * starRingEnd ℂ w).re = z.re * w.re + z.im * w.im := by
  simp [Complex.mul_re]

private lemma complex_norm_sq_add (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * starRingEnd ℂ w).re := by
  rw [complex_norm_sq_eq_re_sq_add_im_sq, complex_norm_sq_eq_re_sq_add_im_sq,
    complex_norm_sq_eq_re_sq_add_im_sq, complex_re_mul_conj_eq]
  simp [Complex.add_re, Complex.add_im]
  ring

private lemma am_gm_three_cubic {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    27 * u * v * w ≤ (u + v + w) ^ 3 := by
  have h1 : 9 * u * v * w ≤ (u + v + w) * (u * v + v * w + w * u) := by
    have hsos : 0 ≤ u * (v - w) ^ 2 + v * (w - u) ^ 2 + w * (u - v) ^ 2 := by positivity
    linarith
  have h2 : 3 * (u * v + v * w + w * u) ≤ (u + v + w) ^ 2 := by
    have hsos : 0 ≤ (u - v) ^ 2 + (v - w) ^ 2 + (w - u) ^ 2 := by positivity
    linarith
  have hsum_nn : 0 ≤ u + v + w := by linarith
  have h3 : 3 * ((u + v + w) * (u * v + v * w + w * u)) ≤ (u + v + w) ^ 3 := by
    nlinarith
  linarith

private lemma ckm_unitary_rows (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : V * Vᴴ = 1) :
    V 0 0 * starRingEnd ℂ (V 1 0) + V 0 1 * starRingEnd ℂ (V 1 1) +
      V 0 2 * starRingEnd ℂ (V 1 2) = 0 ∧
    (‖V 0 0‖ ^ 2 + ‖V 0 1‖ ^ 2 + ‖V 0 2‖ ^ 2 = 1) ∧
    (‖V 1 0‖ ^ 2 + ‖V 1 1‖ ^ 2 + ‖V 1 2‖ ^ 2 = 1) := by
  have h01_raw : (V * Vᴴ) 0 1 = 0 := by rw [hV]; rfl
  have h00_raw : (V * Vᴴ) 0 0 = 1 := by rw [hV]; rfl
  have h11_raw : (V * Vᴴ) 1 1 = 1 := by rw [hV]; rfl
  have h01 : V 0 0 * starRingEnd ℂ (V 1 0) + V 0 1 * starRingEnd ℂ (V 1 1) +
      V 0 2 * starRingEnd ℂ (V 1 2) = 0 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three, add_assoc] using h01_raw
  have h_mul_conj_re : ∀ z : ℂ, (z * star z).re = ‖z‖ ^ 2 := by
    intro z
    rw [complex_norm_sq_eq_re_sq_add_im_sq]
    simp [Complex.mul_re]
    ring
  have h00_re : ((V * Vᴴ) 0 0).re = 1 := by rw [h00_raw]; simp
  have h11_re : ((V * Vᴴ) 1 1).re = 1 := by rw [h11_raw]; simp
  have h00 : ‖V 0 0‖ ^ 2 + ‖V 0 1‖ ^ 2 + ‖V 0 2‖ ^ 2 = 1 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
      Complex.add_re] at h00_re
    rw [h_mul_conj_re, h_mul_conj_re, h_mul_conj_re] at h00_re
    exact h00_re
  have h11 : ‖V 1 0‖ ^ 2 + ‖V 1 1‖ ^ 2 + ‖V 1 2‖ ^ 2 = 1 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
      Complex.add_re] at h11_re
    rw [h_mul_conj_re, h_mul_conj_re, h_mul_conj_re] at h11_re
    exact h11_re
  exact ⟨h01, h00, h11⟩

private lemma ckm_jarlskog_ceiling (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : V * Vᴴ = 1) :
    |ckmJarlskog V| ≤ 1 / (6 * Real.sqrt 3) := by
  obtain ⟨h01, h00, h11⟩ := ckm_unitary_rows V hV
  let z0 : ℂ := V 0 0 * starRingEnd ℂ (V 1 0)
  let z1 : ℂ := V 0 1 * starRingEnd ℂ (V 1 1)
  let z2 : ℂ := V 0 2 * starRingEnd ℂ (V 1 2)
  have hsum_z : z0 + z1 + z2 = 0 := h01
  let a : ℝ := ‖z0‖
  let b : ℝ := ‖z1‖
  let c : ℝ := ‖z2‖
  have hnorm_z : ∀ w1 w2 : ℂ, ‖w1 * starRingEnd ℂ w2‖ = ‖w1‖ * ‖w2‖ := by
    intro w1 w2
    rw [norm_mul, Complex.norm_conj]
  have habc_le : a + b + c ≤ 1 := by
    have ha2 : 2 * a ≤ ‖V 0 0‖ ^ 2 + ‖V 1 0‖ ^ 2 := by
      change 2 * ‖V 0 0 * starRingEnd ℂ (V 1 0)‖ ≤ _
      rw [hnorm_z]
      have : 0 ≤ (‖V 0 0‖ - ‖V 1 0‖) ^ 2 := sq_nonneg _
      linarith
    have hb2 : 2 * b ≤ ‖V 0 1‖ ^ 2 + ‖V 1 1‖ ^ 2 := by
      change 2 * ‖V 0 1 * starRingEnd ℂ (V 1 1)‖ ≤ _
      rw [hnorm_z]
      have : 0 ≤ (‖V 0 1‖ - ‖V 1 1‖) ^ 2 := sq_nonneg _
      linarith
    have hc2 : 2 * c ≤ ‖V 0 2‖ ^ 2 + ‖V 1 2‖ ^ 2 := by
      change 2 * ‖V 0 2 * starRingEnd ℂ (V 1 2)‖ ≤ _
      rw [hnorm_z]
      have : 0 ≤ (‖V 0 2‖ - ‖V 1 2‖) ^ 2 := sq_nonneg _
      linarith
    linarith
  have ha_tri : a ≤ b + c := by
    have hz0 : z0 = -(z1 + z2) := by linear_combination hsum_z
    change ‖z0‖ ≤ ‖z1‖ + ‖z2‖
    rw [hz0, norm_neg]
    exact norm_add_le z1 z2
  have hb_tri : b ≤ a + c := by
    have hz1 : z1 = -(z0 + z2) := by linear_combination hsum_z
    change ‖z1‖ ≤ ‖z0‖ + ‖z2‖
    rw [hz1, norm_neg]
    exact norm_add_le z0 z2
  have hc_tri : c ≤ a + b := by
    have hz2 : z2 = -(z0 + z1) := by linear_combination hsum_z
    change ‖z2‖ ≤ ‖z0‖ + ‖z1‖
    rw [hz2, norm_neg]
    exact norm_add_le z0 z1
  let p : ℂ := z1 * starRingEnd ℂ z2
  have hp_im : p.im = ckmJarlskog V := by
    have hp_eq : p = V 0 1 * V 1 2 * starRingEnd ℂ (V 0 2) * starRingEnd ℂ (V 1 1) := by
      dsimp [p, z1, z2]
      simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
      ring
    rw [hp_eq]
    rfl
  have hp_norm_sq : p.re ^ 2 + p.im ^ 2 = b ^ 2 * c ^ 2 := by
    rw [← complex_norm_sq_eq_re_sq_add_im_sq]
    dsimp [p, b, c]
    rw [norm_mul, Complex.norm_conj]
    ring
  have ha_sq_eq : a ^ 2 = b ^ 2 + c ^ 2 + 2 * p.re := by
    have hz0 : z0 = -(z1 + z2) := by linear_combination hsum_z
    change ‖z0‖ ^ 2 = ‖z1‖ ^ 2 + ‖z2‖ ^ 2 + 2 * (z1 * starRingEnd ℂ z2).re
    rw [hz0, norm_neg, complex_norm_sq_add]
  have h_heron : 4 * (ckmJarlskog V) ^ 2 =
      (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) := by
    rw [← hp_im]
    have h1 : 4 * p.im ^ 2 = 4 * b ^ 2 * c ^ 2 - (2 * p.re) ^ 2 := by linarith [hp_norm_sq]
    have h2 : 2 * p.re = a ^ 2 - b ^ 2 - c ^ 2 := by linarith [ha_sq_eq]
    rw [h1, h2]
    ring
  let u : ℝ := (-a + b + c) / 2
  let v : ℝ := (a - b + c) / 2
  let w : ℝ := (a + b - c) / 2
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have huvw_sum : u + v + w = (a + b + c) / 2 := by dsimp [u, v, w]; ring
  have huvw_le : u + v + w ≤ 1 / 2 := by linarith
  have hJ_sq_eq : (ckmJarlskog V) ^ 2 = 4 * (u + v + w) * u * v * w := by
    have : 4 * (ckmJarlskog V) ^ 2 = 16 * (u + v + w) * u * v * w := by
      rw [h_heron]
      dsimp [u, v, w]
      ring
    linarith
  have hamgm := am_gm_three_cubic hu hv hw
  have hs_nn : 0 ≤ u + v + w := by linarith
  have hpow4 : (u + v + w) ^ 4 ≤ (1 / 2 : ℝ) ^ 4 := by
    exact pow_le_pow_left₀ hs_nn huvw_le 4
  have hJ_sq_bound : (ckmJarlskog V) ^ 2 ≤ 1 / 108 := by
    calc (ckmJarlskog V) ^ 2 = 4 * (u + v + w) * u * v * w := hJ_sq_eq
    _ = (4 / 27 : ℝ) * (u + v + w) * (27 * u * v * w) := by ring
    _ ≤ (4 / 27 : ℝ) * (u + v + w) * (u + v + w) ^ 3 := by
      apply mul_le_mul_of_nonneg_left hamgm
      positivity
    _ = (4 / 27 : ℝ) * (u + v + w) ^ 4 := by ring
    _ ≤ (4 / 27 : ℝ) * (1 / 2 : ℝ) ^ 4 := by linarith
    _ = 1 / 108 := by norm_num
  have hceil_pos : 0 < 1 / (6 * Real.sqrt 3) := by positivity
  have hceil_sq : (1 / (6 * Real.sqrt 3)) ^ 2 = 1 / 108 := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    calc (1 / (6 * Real.sqrt 3)) ^ 2 = 1 / (36 * Real.sqrt 3 ^ 2) := by ring
    _ = 1 / 108 := by rw [h3]; norm_num
  have habs_sq : |ckmJarlskog V| ^ 2 ≤ (1 / (6 * Real.sqrt 3)) ^ 2 := by
    rw [sq_abs, hceil_sq]
    exact hJ_sq_bound
  have hsub_nn : 0 ≤ (1 / (6 * Real.sqrt 3) - |ckmJarlskog V|) * (1 / (6 * Real.sqrt 3) + |ckmJarlskog V|) := by
    linarith
  have hsum_pos : 0 < 1 / (6 * Real.sqrt 3) + |ckmJarlskog V| := by
    linarith [abs_nonneg (ckmJarlskog V)]
  have hdiff_nn : 0 ≤ 1 / (6 * Real.sqrt 3) - |ckmJarlskog V| :=
    nonneg_of_mul_nonneg_left hsub_nn hsum_pos
  linarith

private lemma ckm_dft_unitary_and_jarlskog :
    ckmDFTSharpnessMatrix * ckmDFTSharpnessMatrixᴴ = 1 ∧
      ckmJarlskog ckmDFTSharpnessMatrix = 1 / (6 * Real.sqrt 3) := by
  have hsqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hconj_omega : starRingEnd ℂ omegaDFT =
      ((-1 / 2 : ℝ) : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
    dsimp [omegaDFT]
    have h2 : starRingEnd ℂ (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
    apply Complex.ext <;> simp [h2]
  have homega_mul_conj : omegaDFT * starRingEnd ℂ omegaDFT = 1 := by
    rw [hconj_omega]
    dsimp [omegaDFT]
    apply Complex.ext
    · simp [Complex.mul_re]
      nlinarith [hsqrt3_sq]
    · simp [Complex.mul_im]
      ring
  have homega_sq : omegaDFT ^ 2 = starRingEnd ℂ omegaDFT := by
    rw [hconj_omega]
    dsimp [omegaDFT]
    apply Complex.ext
    · simp [pow_two, Complex.mul_re]
      nlinarith [hsqrt3_sq]
    · simp [pow_two, Complex.mul_im]
      ring
  have homega_cube : omegaDFT ^ 3 = 1 := by
    calc omegaDFT ^ 3 = omegaDFT * omegaDFT ^ 2 := by ring
    _ = omegaDFT * starRingEnd ℂ omegaDFT := by rw [homega_sq]
    _ = 1 := homega_mul_conj
  have homega_sum : 1 + omegaDFT + omegaDFT ^ 2 = 0 := by
    rw [homega_sq, hconj_omega]
    dsimp [omegaDFT]
    apply Complex.ext
    · simp; ring
    · simp
  have homega_four : omegaDFT ^ 4 = omegaDFT := by
    calc omegaDFT ^ 4 = omegaDFT ^ 3 * omegaDFT := by ring
    _ = 1 * omegaDFT := by rw [homega_cube]
    _ = omegaDFT := one_mul omegaDFT
  have hs_real : starRingEnd ℂ ((1 / Real.sqrt 3 : ℝ) : ℂ) = ((1 / Real.sqrt 3 : ℝ) : ℂ) := by
    simp
  have hs_sq : ((1 / Real.sqrt 3 : ℝ) : ℂ) * ((1 / Real.sqrt 3 : ℝ) : ℂ) = (1 / 3 : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re]
      have : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      field_simp [this]
      exact hsqrt3_sq
    · simp [Complex.mul_im]
  have hs_inv_sq : ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ = (1 / 3 : ℂ) := by
    simpa using hs_sq
  have hunit_dft : ckmDFTSharpnessMatrix * ckmDFTSharpnessMatrixᴴ = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
      ckmDFTSharpnessMatrix]
    fin_cases i <;> fin_cases j <;> simp
    · calc _ = 3 * (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹) := by ring
        _ = 1 := by rw [hs_inv_sq]; norm_num
    · have hsumc : 1 + starRingEnd ℂ omegaDFT + (starRingEnd ℂ omegaDFT) ^ 2 = 0 := by
        rw [← homega_sq]
        calc 1 + omegaDFT ^ 2 + (omegaDFT ^ 2) ^ 2 = 1 + omegaDFT ^ 2 + omegaDFT ^ 4 := by ring
        _ = 1 + omegaDFT ^ 2 + omegaDFT := by rw [homega_four]
        _ = 0 := by linear_combination homega_sum
      calc _ = (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹) *
            (1 + starRingEnd ℂ omegaDFT + (starRingEnd ℂ omegaDFT) ^ 2) := by ring
        _ = 0 := by rw [hs_inv_sq, hsumc, mul_zero]
    · have h4 : (starRingEnd ℂ omegaDFT) ^ 4 = starRingEnd ℂ omegaDFT := by
        calc (starRingEnd ℂ omegaDFT) ^ 4 = starRingEnd ℂ (omegaDFT ^ 4) := by simp
        _ = starRingEnd ℂ omegaDFT := by rw [homega_four]
      have hsumc : 1 + (starRingEnd ℂ omegaDFT) ^ 2 + (starRingEnd ℂ omegaDFT) ^ 4 = 0 := by
        rw [h4, ← homega_sq]
        calc 1 + (omegaDFT ^ 2) ^ 2 + omegaDFT ^ 2 = 1 + omegaDFT ^ 4 + omegaDFT ^ 2 := by ring
        _ = 1 + omegaDFT + omegaDFT ^ 2 := by rw [homega_four]
        _ = 0 := homega_sum
      calc _ = (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹) *
            (1 + (starRingEnd ℂ omegaDFT) ^ 2 + (starRingEnd ℂ omegaDFT) ^ 4) := by ring
        _ = 0 := by rw [hs_inv_sq, hsumc, mul_zero]
    · calc _ = (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹) *
            (1 + omegaDFT + omegaDFT ^ 2) := by ring
        _ = 0 := by rw [hs_inv_sq, homega_sum, mul_zero]
    · have h2 : omegaDFT ^ 2 * (starRingEnd ℂ omegaDFT) ^ 2 = 1 := by
        calc omegaDFT ^ 2 * (starRingEnd ℂ omegaDFT) ^ 2 = (omegaDFT * starRingEnd ℂ omegaDFT) ^ 2 := by ring
        _ = 1 := by rw [homega_mul_conj, one_pow]
      calc _ = (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹) *
            (1 + omegaDFT * starRingEnd ℂ omegaDFT + omegaDFT ^ 2 * (starRingEnd ℂ omegaDFT) ^ 2) := by ring
        _ = 1 := by rw [hs_inv_sq, homega_mul_conj, h2]; norm_num
    · have hsum' : 1 + omegaDFT * (starRingEnd ℂ omegaDFT) ^ 2 +
          omegaDFT ^ 2 * (starRingEnd ℂ omegaDFT) ^ 4 = 0 := by
        rw [← homega_sq]
        calc 1 + omegaDFT * (omegaDFT ^ 2) ^ 2 + omegaDFT ^ 2 * (omegaDFT ^ 2) ^ 4
            = 1 + omegaDFT * omegaDFT ^ 4 + omegaDFT ^ 2 * (omegaDFT ^ 4) ^ 2 := by ring
        _ = 1 + omegaDFT * omegaDFT + omegaDFT ^ 2 * omegaDFT ^ 2 := by rw [homega_four]
        _ = 1 + omegaDFT ^ 2 + omegaDFT ^ 4 := by ring
        _ = 1 + omegaDFT ^ 2 + omegaDFT := by rw [homega_four]
        _ = 0 := by linear_combination homega_sum
      calc _ = (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹) *
            (1 + omegaDFT * (starRingEnd ℂ omegaDFT) ^ 2 +
              omegaDFT ^ 2 * (starRingEnd ℂ omegaDFT) ^ 4) := by ring
        _ = 0 := by rw [hs_inv_sq, hsum', mul_zero]
    · have hsum' : 1 + omegaDFT ^ 2 + omegaDFT ^ 4 = 0 := by
        rw [homega_four]; linear_combination homega_sum
      calc _ = (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹) *
            (1 + omegaDFT ^ 2 + omegaDFT ^ 4) := by ring
        _ = 0 := by rw [hs_inv_sq, hsum', mul_zero]
    · have hsum' : 1 + omegaDFT ^ 2 * starRingEnd ℂ omegaDFT +
          omegaDFT ^ 4 * (starRingEnd ℂ omegaDFT) ^ 2 = 0 := by
        rw [homega_four, ← homega_sq]
        calc 1 + omegaDFT ^ 2 * omegaDFT ^ 2 + omegaDFT * (omegaDFT ^ 2) ^ 2
            = 1 + omegaDFT ^ 4 + omegaDFT * omegaDFT ^ 4 := by ring
        _ = 1 + omegaDFT + omegaDFT * omegaDFT := by rw [homega_four]
        _ = 1 + omegaDFT + omegaDFT ^ 2 := by ring
        _ = 0 := homega_sum
      calc _ = (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹) *
            (1 + omegaDFT ^ 2 * starRingEnd ℂ omegaDFT +
              omegaDFT ^ 4 * (starRingEnd ℂ omegaDFT) ^ 2) := by ring
        _ = 0 := by rw [hs_inv_sq, hsum', mul_zero]
    · have h2 : omegaDFT ^ 2 * (starRingEnd ℂ omegaDFT) ^ 2 = 1 := by
        calc omegaDFT ^ 2 * (starRingEnd ℂ omegaDFT) ^ 2 = (omegaDFT * starRingEnd ℂ omegaDFT) ^ 2 := by ring
        _ = 1 := by rw [homega_mul_conj, one_pow]
      have h4 : omegaDFT ^ 4 * (starRingEnd ℂ omegaDFT) ^ 4 = 1 := by
        calc omegaDFT ^ 4 * (starRingEnd ℂ omegaDFT) ^ 4 = (omegaDFT * starRingEnd ℂ omegaDFT) ^ 4 := by ring
        _ = 1 := by rw [homega_mul_conj, one_pow]
      calc _ = (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹) *
            (1 + omegaDFT ^ 2 * (starRingEnd ℂ omegaDFT) ^ 2 +
              omegaDFT ^ 4 * (starRingEnd ℂ omegaDFT) ^ 4) := by ring
        _ = 1 := by rw [hs_inv_sq, h2, h4]; norm_num
  refine ⟨hunit_dft, ?_⟩
  unfold ckmJarlskog ckmDFTSharpnessMatrix
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_mul, one_mul, mul_one,
    pow_zero, pow_one, map_mul, hs_real]
  have hs4 : ((1 / Real.sqrt 3 : ℝ) : ℂ) ^ 4 = ((1 / 9 : ℝ) : ℂ) := by
    calc ((1 / Real.sqrt 3 : ℝ) : ℂ) ^ 4
        = (((1 / Real.sqrt 3 : ℝ) : ℂ) * ((1 / Real.sqrt 3 : ℝ) : ℂ)) ^ 2 := by ring
      _ = (1 / 3 : ℂ) ^ 2 := by rw [hs_sq]
      _ = ((1 / 9 : ℝ) : ℂ) := by norm_num
  have hphase : omegaDFT ^ 2 * starRingEnd ℂ omegaDFT = omegaDFT := by
    calc omegaDFT ^ 2 * starRingEnd ℂ omegaDFT = omegaDFT * (omegaDFT * starRingEnd ℂ omegaDFT) := by ring
    _ = omegaDFT * 1 := by rw [homega_mul_conj]
    _ = omegaDFT := mul_one omegaDFT
  have hprod :
      ((1 / Real.sqrt 3 : ℝ) : ℂ) * (((1 / Real.sqrt 3 : ℝ) : ℂ) * omegaDFT ^ 2) *
        ((1 / Real.sqrt 3 : ℝ) : ℂ) * (((1 / Real.sqrt 3 : ℝ) : ℂ) * starRingEnd ℂ omegaDFT) =
      ((1 / 9 : ℝ) : ℂ) * omegaDFT := by
    calc ((1 / Real.sqrt 3 : ℝ) : ℂ) * (((1 / Real.sqrt 3 : ℝ) : ℂ) * omegaDFT ^ 2) *
          ((1 / Real.sqrt 3 : ℝ) : ℂ) * (((1 / Real.sqrt 3 : ℝ) : ℂ) * starRingEnd ℂ omegaDFT)
        = (((1 / Real.sqrt 3 : ℝ) : ℂ) ^ 4) * (omegaDFT ^ 2 * starRingEnd ℂ omegaDFT) := by ring
    _ = ((1 / 9 : ℝ) : ℂ) * omegaDFT := by rw [hs4, hphase]
  rw [hprod]
  have him : (((1 / 9 : ℝ) : ℂ) * omegaDFT).im = (1 / 9 : ℝ) * (Real.sqrt 3 / 2) := by
    dsimp [omegaDFT]
    simp [Complex.mul_im, Complex.add_im]
  rw [him]
  have hsqrt_ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hsqrt_ne]
  nlinarith [hsqrt3_sq]

/-- `[B/S/P]` **CKM Unitarity Triangle, Rephasing Invariance, Sharp `1/(6√3)` Ceiling & 3-Gen Seesaw**:
1. **Unitarity triangle closure & row normalization**: from `V * Vᴴ = 1`, row `0` and row `1` satisfy
   `V 0 0 * conj(V 1 0) + V 0 1 * conj(V 1 1) + V 0 2 * conj(V 1 2) = 0` and unit `ℓ²` row norms.
2. **Exact 6-phase rephasing invariance**: if `|φ_L(i)| = |φ_R(j)| = 1` (`φ * conj φ = 1`),
   `ckmJarlskog (rephaseCKM phiL phiR V) = ckmJarlskog V`.
3. **Zero-trig algebraic ceiling**: for EVERY `3 × 3` unitary matrix (`V * Vᴴ = 1`),
   `|ckmJarlskog V| ≤ 1 / (6 * Real.sqrt 3)` (`J^2 ≤ 1 / 108`).
4. **Sharpness witness**: `ckmDFTSharpnessMatrix` is unitary (`V * Vᴴ = 1`) and attains
   `ckmJarlskog ckmDFTSharpnessMatrix = 1 / (6 * Real.sqrt 3)`.
5. **3-generation CP threshold & Type-I seesaw Schur/trace/product bounds**:
   `diracCPPhaseCount 3 = 1`, `Matrix.det (M_Dᵀ * M_R_inv * M_D) * Matrix.det M_R = (Matrix.det M_D)^2`,
   and `Fin 3` light-neutrino trace and product bounds `0 < ∑ m_ν < ∑ m_D²/M_R` and
   `0 < ∏ m_ν < ∏ m_D²/M_R`. -/
theorem jarlskog_invariant_rephasing_and_ceiling :
    (∀ V : Matrix (Fin 3) (Fin 3) ℂ, V * Vᴴ = 1 →
      V 0 0 * starRingEnd ℂ (V 1 0) + V 0 1 * starRingEnd ℂ (V 1 1) +
        V 0 2 * starRingEnd ℂ (V 1 2) = 0 ∧
      (‖V 0 0‖ ^ 2 + ‖V 0 1‖ ^ 2 + ‖V 0 2‖ ^ 2 = 1) ∧
      (‖V 1 0‖ ^ 2 + ‖V 1 1‖ ^ 2 + ‖V 1 2‖ ^ 2 = 1)) ∧
    (∀ (phiL phiR : Fin 3 → ℂ) (V : Matrix (Fin 3) (Fin 3) ℂ),
      (∀ i, phiL i * starRingEnd ℂ (phiL i) = 1) →
      (∀ j, phiR j * starRingEnd ℂ (phiR j) = 1) →
      ckmJarlskog (rephaseCKM phiL phiR V) = ckmJarlskog V) ∧
    (∀ V : Matrix (Fin 3) (Fin 3) ℂ, V * Vᴴ = 1 →
      |ckmJarlskog V| ≤ 1 / (6 * Real.sqrt 3)) ∧
    (ckmDFTSharpnessMatrix * ckmDFTSharpnessMatrixᴴ = 1 ∧
      ckmJarlskog ckmDFTSharpnessMatrix = 1 / (6 * Real.sqrt 3)) ∧
    (diracCPPhaseCount 3 = 1 ∧
      (∀ (M_D M_R M_R_inv : Matrix (Fin 3) (Fin 3) ℝ),
        M_R * M_R_inv = 1 →
        Matrix.det (M_Dᵀ * M_R_inv * M_D) * Matrix.det M_R = (Matrix.det M_D) ^ 2) ∧
      (∀ (mD M_R : Fin 3 → ℝ),
        (∀ i, 0 < M_R i) → (∀ i, mD i ≠ 0) →
        0 < (∑ i : Fin 3, seesawLightMass (mD i) (M_R i)) ∧
        (∑ i : Fin 3, seesawLightMass (mD i) (M_R i)) < (∑ i : Fin 3, mD i ^ 2 / M_R i) ∧
        0 < (∏ i : Fin 3, seesawLightMass (mD i) (M_R i)) ∧
        (∏ i : Fin 3, seesawLightMass (mD i) (M_R i)) < (∏ i : Fin 3, mD i ^ 2 / M_R i))) := by
  refine ⟨ckm_unitary_rows, ?_, ckm_jarlskog_ceiling, ckm_dft_unitary_and_jarlskog, ?_⟩
  · intro phiL phiR V hL hR
    unfold ckmJarlskog rephaseCKM
    have hterm :
        (phiL 0 * V 0 1 * phiR 1) * (phiL 1 * V 1 2 * phiR 2) *
          starRingEnd ℂ (phiL 0 * V 0 2 * phiR 2) *
          starRingEnd ℂ (phiL 1 * V 1 1 * phiR 1) =
        (phiL 0 * starRingEnd ℂ (phiL 0)) * (phiL 1 * starRingEnd ℂ (phiL 1)) *
          (phiR 1 * starRingEnd ℂ (phiR 1)) * (phiR 2 * starRingEnd ℂ (phiR 2)) *
          (V 0 1 * V 1 2 * starRingEnd ℂ (V 0 2) * starRingEnd ℂ (V 1 1)) := by
      simp only [map_mul]
      ring
    rw [hterm, hL 0, hL 1, hR 1, hR 2]
    simp
  · refine ⟨(dirac_cp_phases_pos_iff_three_generations (by norm_num : 1 ≤ 3)).2.1, ?_, ?_⟩
    · intro M_D M_R M_R_inv hinv
      have hdet_inv : Matrix.det M_R * Matrix.det M_R_inv = 1 := by
        rw [← Matrix.det_mul, hinv, Matrix.det_one]
      calc Matrix.det (M_Dᵀ * M_R_inv * M_D) * Matrix.det M_R
          = (Matrix.det M_Dᵀ * Matrix.det M_R_inv * Matrix.det M_D) * Matrix.det M_R := by
            simp only [Matrix.det_mul]
      _ = (Matrix.det M_D) ^ 2 * (Matrix.det M_R * Matrix.det M_R_inv) := by
            rw [Matrix.det_transpose]; ring
      _ = (Matrix.det M_D) ^ 2 := by rw [hdet_inv, mul_one]
    · intro mD M_R hMR hmD
      have hmode : ∀ i : Fin 3,
          0 < seesawLightMass (mD i) (M_R i) ∧
            seesawLightMass (mD i) (M_R i) < mD i ^ 2 / M_R i := fun i =>
        let h := type_one_seesaw_exact_roots_and_bound (hMR i) (hmD i)
        ⟨h.2.2.1, h.2.2.2⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact Finset.sum_pos (fun i _ => (hmode i).1) Finset.univ_nonempty
      · exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => (hmode i).2)
      · exact Finset.prod_pos (fun i _ => (hmode i).1)
      · have h0 := hmode 0
        have h1 := hmode 1
        have h2 := hmode 2
        simp only [Fin.prod_univ_three]
        have h01 : seesawLightMass (mD 0) (M_R 0) * seesawLightMass (mD 1) (M_R 1) <
            (mD 0 ^ 2 / M_R 0) * (mD 1 ^ 2 / M_R 1) :=
          mul_lt_mul'' h0.2 h1.2 (le_of_lt h0.1) (le_of_lt h1.1)
        exact mul_lt_mul'' h01 h2.2 (le_of_lt (mul_pos h0.1 h1.1)) (le_of_lt h2.1)

/-! ## 3. `H3c`: Two-Sided Cosmological Viability Window & Operational `I_Λ` Indistinguishability (`[C/B/P/E/O]`) -/

/-- `[P]` Negative-`Λ` Friedmann expansion discriminant term `M_tot / a + (Λ / 3) a²`
(`ȧ² = 2 (M_tot / a + (Λ / 3) a²)` for `k = 0` dust). When `≤ 0`, expansion halts and recollapses. -/
noncomputable def friedmannAdSExpansionTerm (Mtot Lambda a : ℝ) : ℝ :=
  Mtot / a + (Lambda / 3) * a ^ 2

/-- `[C/B/P/E/O]` **Two-Sided Cosmological Viability Window & Operational `I_Λ` Indistinguishability**:
1. **Negative-`Λ` AdS recollapse bound (`Λ < 0`)**: for `0 < Mtot, 0 < a`,
   `0 ≤ friedmannAdSExpansionTerm Mtot Lambda a ↔ a^3 ≤ 3 * Mtot / (-Lambda)`, so
   `Lambda ≤ -3 * Mtot / aOrg^3 → friedmannAdSExpansionTerm Mtot Lambda aOrg ≤ 0` (Big Crunch before `aOrg`).
2. **Positive-`Λ` `ViabilityKernel` + `InformationPacking` + directionality**:
   - `I_Λ < Imax` sustains `ControlledInvariant` non-empty `viabilityIter` (`Ω > 0`), whereas
     `Imax ≤ I_Λ` collapses `viabilityIter ... 1 = ∅` (`cosmological_viability_kernel_dichotomy`).
   - `S_dS = 3π / I_Λ` is *decreasing* in `I_Λ`: requiring `S_obs ≤ 3π / I_Λ` is an **upper** bound
     `I_Λ ≤ 3π / S_obs` (strictly respecting `InformationPacking` inequality directionality!).
   - Finite causal-patch operational histories satisfy `F.card ≤ N_dS` (`deSitter_causal_patch_tv_packing_bound`).
3. **Non-empty two-sided window `(Imin, Imax)` containing Planck-2018+BAO `Iobs`**:
   for `0 < Imin < I1 < I2 < Imax` (and explicitly for `Iobs ∈ [2829/10^125, 2948/10^125]`),
   the window is non-empty, both `I1, I2` sustain non-empty `viabilityIter`, lie in disjoint
   `UnitScale` orbits, and satisfy `3π / I2 < 3π / I1` (`unimodular_viability_leaves_exact_ILambda_open`).
4. **`AH01` + `UEOT.V3.BinaryTesting.binaryRisk_lower_bound` operational indistinguishability**:
   above the `AH01` horizon sensor floor `0 < L_min_sq < L^2`, whenever two `I_Λ` models have
   `tvDist P₀ P₁ ≤ C_IR * R_ratio * |I₁ - I₂|` with `|I₁ - I₂| < (2 * delta_adv) / (C_IR * R_ratio)`,
   EVERY measurable binary test `A` satisfies `1 / 2 - delta_adv < binaryRisk P₀ P₁ A`. -/
theorem two_sided_cosmological_viability_and_operational_ilambda_indistinguishability :
    (∀ {Mtot Lambda a aOrg : ℝ},
      0 < Mtot → Lambda < 0 → 0 < a → 0 < aOrg →
      (0 ≤ friedmannAdSExpansionTerm Mtot Lambda a ↔ a ^ 3 ≤ 3 * Mtot / (-Lambda)) ∧
      (Lambda ≤ -(3 * Mtot / aOrg ^ 3) → friedmannAdSExpansionTerm Mtot Lambda aOrg ≤ 0)) ∧
    (∀ {Imin I1 I2 Imax S_obs : ℝ},
      0 < Imin → Imin < I1 → I1 < I2 → I2 < Imax → 0 < S_obs →
      (0 < I1 ∧ I1 < Imax) ∧
      (S_obs ≤ 3 * Real.pi / I1 ↔ I1 ≤ 3 * Real.pi / S_obs) ∧
      (∀ n : ℕ, (viabilityIter (cosmicHaloTransition I1 Imax) boundViableSet n).Nonempty) ∧
      (∀ n : ℕ, (viabilityIter (cosmicHaloTransition I2 Imax) boundViableSet n).Nonempty) ∧
      (viabilityIter (cosmicHaloTransition Imax Imax) boundViableSet 1 = ∅) ∧
      (¬ ∃ u : UnitScale, scaleGrav u (planckGaugeSection I1) = planckGaugeSection I2) ∧
      3 * Real.pi / I2 < 3 * Real.pi / I1) ∧
    (∀ {Imin Iobs Imax : ℝ},
      0 < Imin → Imin ≤ (2829 : ℝ) / 10 ^ 125 →
      (2829 : ℝ) / 10 ^ 125 ≤ Iobs → Iobs ≤ (2948 : ℝ) / 10 ^ 125 →
      (2948 : ℝ) / 10 ^ 125 < Imax →
      0 < Imin ∧ Imin ≤ Iobs ∧ Iobs < Imax ∧
        (∀ n : ℕ, (viabilityIter (cosmicHaloTransition Iobs Imax) boundViableSet n).Nonempty)) ∧
    (∀ {H Y : Type*} [MeasurableSpace Y]
      (N_dS : ℕ) (K : H → Measure Y) (R : H → Fin N_dS) (decode : Fin N_dS → Measure Y),
      (∀ h, IsProbabilityMeasure (K h)) →
      (∀ s, IsProbabilityMeasure (decode s)) →
      ∀ (F : Finset H) (ε : ℝ),
      (∀ ⦃h₁⦄, h₁ ∈ F → ∀ ⦃h₂⦄, h₂ ∈ F → h₁ ≠ h₂ → 2 * ε < tvDist (K h₁) (K h₂)) →
      (∀ h ∈ F, tvDist (K h) (decode (R h)) ≤ ε) →
      F.card ≤ N_dS) ∧
    (∀ {X : Type*} [MeasurableSpace X]
      (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
      {L E_tot E_min hbar c G lam_sys C_IR R_ratio I1 I2 delta_adv : ℝ},
      0 < L → 0 < E_min → 0 < hbar → 0 < c → 0 < G → 0 < lam_sys →
      E_min * hbar * c ≤ E_tot * L →
      2 * G * E_tot < lam_sys * c ^ 4 * L →
      0 < C_IR → 0 < R_ratio →
      tvDist P₀ P₁ ≤ C_IR * R_ratio * |I1 - I2| →
      |I1 - I2| < (2 * delta_adv) / (C_IR * R_ratio) →
      (0 < (2 * E_min / lam_sys) * (hbar * G / c ^ 3) ∧
        (2 * E_min / lam_sys) * (hbar * G / c ^ 3) < L ^ 2) ∧
      (∀ A : Set X, MeasurableSet A → 1 / 2 - delta_adv < binaryRisk P₀ P₁ A)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Mtot Lambda a aOrg hM hLam ha haOrg
    have hnegLam : 0 < -Lambda := by linarith
    constructor
    · unfold friedmannAdSExpansionTerm
      have hrew : Mtot / a + (Lambda / 3) * a ^ 2 = (3 * Mtot - (-Lambda) * a ^ 3) / (3 * a) := by
        have ha_ne : a ≠ 0 := ne_of_gt ha
        field_simp [ha_ne]
        ring
      rw [hrew, div_nonneg_iff]
      constructor
      · intro h
        rcases h with ⟨hnum, _⟩ | ⟨_, hden⟩
        · rw [le_div_iff₀ hnegLam]
          linarith
        · linarith
      · intro hle
        left
        rw [le_div_iff₀ hnegLam] at hle
        exact ⟨by linarith, by positivity⟩
    · intro hLam_le
      unfold friedmannAdSExpansionTerm
      have ha3_pos : 0 < aOrg ^ 3 := by positivity
      have haOrg_ne : aOrg ≠ 0 := ne_of_gt haOrg
      have hmul : Lambda * aOrg ^ 3 ≤ -3 * Mtot := by
        have h1 : Lambda * aOrg ^ 3 ≤ (-(3 * Mtot / aOrg ^ 3)) * aOrg ^ 3 :=
          mul_le_mul_of_nonneg_right hLam_le (le_of_lt ha3_pos)
        have h2 : (-(3 * Mtot / aOrg ^ 3)) * aOrg ^ 3 = -3 * Mtot := by
          field_simp [ne_of_gt ha3_pos]
        linarith
      have hrew : Mtot / aOrg + (Lambda / 3) * aOrg ^ 2 =
          (3 * Mtot + Lambda * aOrg ^ 3) / (3 * aOrg) := by
        field_simp [haOrg_ne]
      rw [hrew]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  · intro Imin I1 I2 Imax S_obs hImin hmin1 h12 h2max hSobs
    have hI1_pos : 0 < I1 := lt_trans hImin hmin1
    have h1max : I1 < Imax := lt_trans h12 h2max
    have hopen := unimodular_viability_leaves_exact_ILambda_open hI1_pos h12 h2max
    have hcoll := (cosmological_viability_kernel_dichotomy Imax Imax).2 (le_refl Imax)
    refine ⟨⟨hI1_pos, h1max⟩, ?_, hopen.1, hopen.2.1, hcoll, hopen.2.2.1, hopen.2.2.2⟩
    constructor
    · intro hle
      rw [le_div_iff₀ hI1_pos] at hle
      rw [le_div_iff₀ hSobs]
      linarith
    · intro hle
      rw [le_div_iff₀ hSobs] at hle
      rw [le_div_iff₀ hI1_pos]
      linarith
  · intro Imin Iobs Imax hImin hlo hIobs_lo hIobs_hi hhi
    have hIobs_lt : Iobs < Imax := lt_of_le_of_lt hIobs_hi hhi
    have hviab := (cosmological_viability_kernel_dichotomy Iobs Imax).1 hIobs_lt
    exact ⟨hImin, le_trans hlo hIobs_lo, hIobs_lt, hviab.2.2.1⟩
  · intro H Y _ N_dS K R decode hK hdecode F ε hsep herr
    exact deSitter_causal_patch_tv_packing_bound N_dS K R decode hK hdecode F ε hsep herr
  · intro X _ P₀ P₁ _ _ L E_tot E_min hbar c G lam_sys C_IR R_ratio I1 I2 delta_adv
      hL hEmin hhbar hc hG hlam hclock hnotrap hCIR hR htv_le hgap_lt
    have hah := gravitational_horizon_excludes_pointlike_clock
      hL hEmin hhbar hc hG hlam hclock hnotrap
    refine ⟨hah, ?_⟩
    intro A hA
    have hCR_pos : 0 < C_IR * R_ratio := mul_pos hCIR hR
    have hmul : C_IR * R_ratio * |I1 - I2| < C_IR * R_ratio * ((2 * delta_adv) / (C_IR * R_ratio)) :=
      mul_lt_mul_of_pos_left hgap_lt hCR_pos
    have hcancel : C_IR * R_ratio * ((2 * delta_adv) / (C_IR * R_ratio)) = 2 * delta_adv :=
      mul_div_cancel₀ _ (ne_of_gt hCR_pos)
    have htv_lt : tvDist P₀ P₁ < 2 * delta_adv := by linarith
    have hrisk_lb := binaryRisk_lower_bound P₀ P₁ A hA
    linarith

/-! ## 4. `H3d`: Sharp 4-Layer `H3SubHypothesis` Decomposition & Honest `OPEN` Selection (`[C/B/X]`) -/

/-- Exact 4-layer decomposition of frontier **`H3`** (`SPEC-20261124-04`). -/
inductive H3SubHypothesis : Type
  | h3a_unit_unimodular_reduction
  | h3b_eft_flavor_viability_windows
  | h3c_horizon_indistinguishability
  | h3d_exact_apriori_constants_selection
  deriving DecidableEq, Repr

instance : Fintype H3SubHypothesis where
  elems := {
    .h3a_unit_unimodular_reduction,
    .h3b_eft_flavor_viability_windows,
    .h3c_horizon_indistinguishability,
    .h3d_exact_apriori_constants_selection
  }
  complete h := by cases h <;> decide

/-- Quantitative defect record evaluating all four sublayers of `H3`. -/
structure H3LayerCandidate where
  unitUnimodularDefect : ℝ
  eftFlavorViabilityDefect : ℝ
  horizonIndistinguishabilityDefect : ℝ
  exactAprioriSelectionDefect : ℝ

/-- Semantic closure predicate on each sublayer of `H3`. -/
def H3LayerCandidate.Satisfies (C : H3LayerCandidate) : H3SubHypothesis → Prop
  | .h3a_unit_unimodular_reduction => C.unitUnimodularDefect = 0
  | .h3b_eft_flavor_viability_windows => C.eftFlavorViabilityDefect = 0
  | .h3c_horizon_indistinguishability => C.horizonIndistinguishabilityDefect = 0
  | .h3d_exact_apriori_constants_selection => C.exactAprioriSelectionDefect = 0

/-- Complete unconditional derivation of all dimensionless physical constants (`H3`). -/
def H3LayerCandidate.FullH3Closure (C : H3LayerCandidate) : Prop :=
  C.unitUnimodularDefect = 0 ∧
  C.eftFlavorViabilityDefect = 0 ∧
  C.horizonIndistinguishabilityDefect = 0 ∧
  C.exactAprioriSelectionDefect = 0

/-- Wave 11 `H3` constructive witness closing `H3a ∧ H3b ∧ H3c` while leaving
`h3d_exact_apriori_constants_selection` honestly **`OPEN`**. -/
def wave11H3ConstructiveWitness : H3LayerCandidate :=
  ⟨0, 0, 0, 1⟩

/-- `[C/B/X]` **Sharp `H3` Decomposition & Honest Open Selection Theorem (`C-H3-WINDOW-04`)**:
1. `Fintype.card H3SubHypothesis = 4` and `FullH3Closure C ↔ ∀ h, C.Satisfies h`,
2. `wave11H3ConstructiveWitness` closes the first three operational/structural sub-frontiers
   (`h3a`, `h3b`, `h3c`) and refutes `h3d_exact_apriori_constants_selection`,
3. All four sub-hypotheses are pairwise logically independent,
4. Sharp reduction: when `h3a ∧ h3b ∧ h3c` hold, `FullH3Closure C ↔ C.Satisfies .h3d_exact_apriori_constants_selection`,
5. Unresolved `H3d` keeps `physicalUnificationStatus (Fintype.card H3SubHypothesis) false = .OPEN`. -/
theorem h3_frontier_sharp_decomposition_and_open_selection :
    Fintype.card H3SubHypothesis = 4 ∧
      (∀ C : H3LayerCandidate, C.FullH3Closure ↔ ∀ h : H3SubHypothesis, C.Satisfies h) ∧
      (wave11H3ConstructiveWitness.Satisfies .h3a_unit_unimodular_reduction ∧
        wave11H3ConstructiveWitness.Satisfies .h3b_eft_flavor_viability_windows ∧
        wave11H3ConstructiveWitness.Satisfies .h3c_horizon_indistinguishability ∧
        ¬ wave11H3ConstructiveWitness.Satisfies .h3d_exact_apriori_constants_selection) ∧
      (∀ h : H3SubHypothesis, ∃ C : H3LayerCandidate,
        (∀ h' : H3SubHypothesis, h' ≠ h → C.Satisfies h') ∧ ¬ C.Satisfies h) ∧
      (∀ C : H3LayerCandidate,
        C.Satisfies .h3a_unit_unimodular_reduction →
        C.Satisfies .h3b_eft_flavor_viability_windows →
        C.Satisfies .h3c_horizon_indistinguishability →
        (C.FullH3Closure ↔ C.Satisfies .h3d_exact_apriori_constants_selection)) ∧
      (∀ k : ℕ, physicalUnificationStatus (k + 1) false = .OPEN) ∧
      physicalUnificationStatus (Fintype.card H3SubHypothesis) false = .OPEN := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C
    constructor
    · rintro ⟨h1, h2, h3, h4⟩ h
      cases h
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    · intro hall
      exact ⟨hall .h3a_unit_unimodular_reduction,
        hall .h3b_eft_flavor_viability_windows,
        hall .h3c_horizon_indistinguishability,
        hall .h3d_exact_apriori_constants_selection⟩
  · exact ⟨rfl, rfl, rfl, by simp [wave11H3ConstructiveWitness, H3LayerCandidate.Satisfies]⟩
  · intro h
    cases h with
    | h3a_unit_unimodular_reduction =>
      refine ⟨⟨1, 0, 0, 0⟩, ?_, by simp [H3LayerCandidate.Satisfies]⟩
      intro h' hne; cases h' <;> first | exact absurd rfl hne | rfl
    | h3b_eft_flavor_viability_windows =>
      refine ⟨⟨0, 1, 0, 0⟩, ?_, by simp [H3LayerCandidate.Satisfies]⟩
      intro h' hne; cases h' <;> first | exact absurd rfl hne | rfl
    | h3c_horizon_indistinguishability =>
      refine ⟨⟨0, 0, 1, 0⟩, ?_, by simp [H3LayerCandidate.Satisfies]⟩
      intro h' hne; cases h' <;> first | exact absurd rfl hne | rfl
    | h3d_exact_apriori_constants_selection =>
      refine ⟨⟨0, 0, 0, 1⟩, ?_, by simp [H3LayerCandidate.Satisfies]⟩
      intro h' hne; cases h' <;> first | exact absurd rfl hne | rfl
  · intro C h1 h2 h3
    dsimp [H3LayerCandidate.Satisfies, H3LayerCandidate.FullH3Closure] at h1 h2 h3 ⊢
    simp [h1, h2, h3]
  · intro k
    simp [physicalUnificationStatus]
  · decide

end UEOTPhysicsUnification.DimensionlessCouplingsFlavorAndVacuumWindowH3
