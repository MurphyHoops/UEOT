import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Electroweak Custodial Symmetry, Kobayashi-Maskawa Phase Threshold & Type-I Seesaw
(`P-EW-01`, `P-QFLAV-02`, `P-QNU-02`)

Closes the electroweak, generation-phase, and neutrino-mass unification obligations of
`PREMISES_AND_RESPONSIBILITIES.md` §5 Row 10 and `PHYSICS_RESULT_MAPPING.md` Chapters 30–31:

1. **P-EW-01 — Neutral Boson Mass Matrix, Exact Photon Zero Mode & Custodial `ρ_0 = 1`**:
   - `photon_zero_mode_and_z_eigenmode`: Diagonalizes `(v^2 / 4) [[g^2, -g g'], [-g g', g'^2]]`, proving
     an exact massless `U(1)_em` photon eigenvector `(g', g)` (`det = 0`) and heavy `Z` eigenvalue
     `v^2 (g^2 + g'^2) / 4`.
   - `custodial_rho_tree_level_one` vs `higgs_triplet_breaks_custodial_rho`: Doublet breaking yields
     `M_W^2 / (M_Z^2 cos^2 θ_W) = 1` identically, whereas a nonzero `Y = 1` Higgs-triplet VEV `v_T ≠ 0`
     shifts `1 - ρ_0 = 2 v_T^2 / (v^2 + 4 v_T^2) > 0`.

2. **P-QFLAV-02 — Kobayashi-Maskawa Three-Generation Dirac CP Threshold vs Majorana Phases**:
   - `dirac_cp_phases_pos_iff_three_generations`: `(N_g - 1)(N_g - 2) / 2 > 0 ↔ 3 ≤ N_g` for all `N_g ≥ 1`,
     proving that `N_g = 3` is the minimal quark generation count supporting Dirac CP violation (`1` phase),
     whereas Majorana lepton mixing `N_g(N_g - 1) / 2` already admits `1` phase at `N_g = 2` and `3` at `N_g = 3`.

3. **P-QNU-02 — Exact Type-I Seesaw Eigenvalues & Non-Asymptotic `m_D^2 / M_R` Bound**:
   - `type_one_seesaw_exact_roots_and_bound`: For `M_R > 0` and `m_D ≠ 0`, the exact positive seesaw mass
     magnitudes `λ_± = (√(M_R^2 + 4 m_D^2) ± M_R) / 2` satisfy `λ_+ - λ_- = M_R`, `λ_+ * λ_- = m_D^2`,
     and `0 < λ_- < m_D^2 / M_R`.
-/

namespace UEOTPhysicsUnification.ElectroweakCustodialAndSeesaw

open Matrix

/-! ## 1. Electroweak Neutral Gauge Mass Matrix & Custodial `ρ_0 = 1` -/

/-- Neutral `(W^3, B)` squared-mass matrix after `SU(2)_L × U(1)_Y` doublet symmetry breaking. -/
noncomputable def ewNeutralMassSq (v g gp : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![v ^ 2 * g ^ 2 / 4,       -(v ^ 2 * g * gp / 4);
     -(v ^ 2 * g * gp / 4),   v ^ 2 * gp ^ 2 / 4]

/-- Exact massless photon zero mode `(gp, g)` and heavy `Z` eigenmode `(g, -gp)`. -/
theorem photon_zero_mode_and_z_eigenmode (v g gp : ℝ) :
    (ewNeutralMassSq v g gp).det = 0 ∧
      (ewNeutralMassSq v g gp).mulVec ![gp, g] = 0 ∧
      (ewNeutralMassSq v g gp).mulVec ![g, -gp] =
        (v ^ 2 * (g ^ 2 + gp ^ 2) / 4) • ![g, -gp] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ewNeutralMassSq, Matrix.det_fin_two]
    ring
  · ext i
    fin_cases i <;>
      (simp [ewNeutralMassSq, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring)
  · ext i
    fin_cases i <;>
      (simp [ewNeutralMassSq, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring)

/-- Exact tree-level custodial relation `M_W^2 / (M_Z^2 * cos^2 θ_W) = 1` for arbitrary Higgs doublets. -/
theorem custodial_rho_tree_level_one
    {v g gp : ℝ} (hv : v ≠ 0) (hg : g ≠ 0) :
    let mwSq := v ^ 2 * g ^ 2 / 4
    let mzSq := v ^ 2 * (g ^ 2 + gp ^ 2) / 4
    let cosSqThetaW := g ^ 2 / (g ^ 2 + gp ^ 2)
    mwSq / (mzSq * cosSqThetaW) = 1 := by
  intro mwSq mzSq cosSqThetaW
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  have hg2_pos : 0 < g ^ 2 := sq_pos_of_ne_zero hg
  have hsum_pos : 0 < g ^ 2 + gp ^ 2 := by nlinarith [sq_nonneg gp]
  have hsum_ne : g ^ 2 + gp ^ 2 ≠ 0 := ne_of_gt hsum_pos
  have hg2_ne : g ^ 2 ≠ 0 := ne_of_gt hg2_pos
  dsimp [mwSq, mzSq, cosSqThetaW]
  field_simp [hv2, hg2_ne, hsum_ne]

/-- Falsifiable custodial symmetry breaking by a `Y = 1` complex Higgs triplet with VEV `vT ≠ 0`:
`ρ_0 = (v^2 + 2 vT^2) / (v^2 + 4 vT^2)` satisfies `0 < 1 - ρ_0`. -/
theorem higgs_triplet_breaks_custodial_rho
    {v vT : ℝ} (hv : v ≠ 0) (hvT : vT ≠ 0) :
    let rho := (v ^ 2 + 2 * vT ^ 2) / (v ^ 2 + 4 * vT ^ 2)
    1 - rho = 2 * vT ^ 2 / (v ^ 2 + 4 * vT ^ 2) ∧ 0 < 1 - rho := by
  intro rho
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hvT2 : 0 < vT ^ 2 := sq_pos_of_ne_zero hvT
  have hden_pos : 0 < v ^ 2 + 4 * vT ^ 2 := by linarith
  have hden_ne : v ^ 2 + 4 * vT ^ 2 ≠ 0 := ne_of_gt hden_pos
  have hdiff : 1 - rho = 2 * vT ^ 2 / (v ^ 2 + 4 * vT ^ 2) := by
    dsimp [rho]
    field_simp [hden_ne]
    ring
  exact ⟨hdiff, by rw [hdiff]; positivity⟩

/-! ## 2. Kobayashi-Maskawa Dirac vs Majorana Physical CP-Phase Counting -/

/-- Number of physical Dirac CKM CP-violating phases `(Ng - 1) * (Ng - 2) / 2`. -/
def diracCPPhaseCount (Ng : ℕ) : ℕ :=
  (Ng - 1) * (Ng - 2) / 2

/-- Number of physical Majorana PMNS CP-violating phases `Ng * (Ng - 1) / 2`. -/
def majoranaCPPhaseCount (Ng : ℕ) : ℕ :=
  Ng * (Ng - 1) / 2

/-- Exact Kobayashi-Maskawa threshold: for `Ng ≥ 1`, Dirac CP violation exists iff `Ng ≥ 3`,
with exactly `1` Dirac phase and `3` Majorana phases at `Ng = 3`. -/
theorem dirac_cp_phases_pos_iff_three_generations {Ng : ℕ} (_h1 : 1 ≤ Ng) :
    (0 < diracCPPhaseCount Ng ↔ 3 ≤ Ng) ∧
      diracCPPhaseCount 3 = 1 ∧
      majoranaCPPhaseCount 2 = 1 ∧
      majoranaCPPhaseCount 3 = 3 := by
  refine ⟨?_, rfl, rfl, rfl⟩
  unfold diracCPPhaseCount
  constructor
  · intro hpos
    by_contra hlt
    interval_cases Ng <;> simp at hpos
  · intro h3
    have hprod : 2 ≤ (Ng - 1) * (Ng - 2) := by
      have ha : 2 ≤ Ng - 1 := by omega
      have hb : 1 ≤ Ng - 2 := by omega
      nlinarith
    omega

/-! ## 3. Exact Type-I Seesaw Spectrum & Strict `m_D^2 / M_R` Upper Bound -/

/-- Light and heavy positive mass magnitudes of the `2 × 2` Type-I seesaw matrix `[[0, mD], [mD, MR]]`. -/
noncomputable def seesawLightMass (mD MR : ℝ) : ℝ :=
  (Real.sqrt (MR ^ 2 + 4 * mD ^ 2) - MR) / 2

noncomputable def seesawHeavyMass (mD MR : ℝ) : ℝ :=
  (Real.sqrt (MR ^ 2 + 4 * mD ^ 2) + MR) / 2

/-- Exact trace, determinant, and strict non-asymptotic inequality `0 < m_light < m_D^2 / M_R`. -/
theorem type_one_seesaw_exact_roots_and_bound
    {mD MR : ℝ} (hMR : 0 < MR) (hmD : mD ≠ 0) :
    seesawHeavyMass mD MR - seesawLightMass mD MR = MR ∧
      seesawHeavyMass mD MR * seesawLightMass mD MR = mD ^ 2 ∧
      0 < seesawLightMass mD MR ∧
      seesawLightMass mD MR < mD ^ 2 / MR := by
  have hmD2 : 0 < mD ^ 2 := sq_pos_of_ne_zero hmD
  have hrad_pos : 0 ≤ MR ^ 2 + 4 * mD ^ 2 := by positivity
  have hsqrt_sq : Real.sqrt (MR ^ 2 + 4 * mD ^ 2) ^ 2 = MR ^ 2 + 4 * mD ^ 2 :=
    Real.sq_sqrt hrad_pos
  have hsqrt_gt : MR < Real.sqrt (MR ^ 2 + 4 * mD ^ 2) := by
    have hlt_sq : MR ^ 2 < MR ^ 2 + 4 * mD ^ 2 := by linarith
    exact (Real.lt_sqrt (le_of_lt hMR)).mpr hlt_sq
  have hdiff : seesawHeavyMass mD MR - seesawLightMass mD MR = MR := by
    unfold seesawHeavyMass seesawLightMass
    ring
  have hprod : seesawHeavyMass mD MR * seesawLightMass mD MR = mD ^ 2 := by
    unfold seesawHeavyMass seesawLightMass
    calc
      (Real.sqrt (MR ^ 2 + 4 * mD ^ 2) + MR) / 2 *
          ((Real.sqrt (MR ^ 2 + 4 * mD ^ 2) - MR) / 2)
          = (Real.sqrt (MR ^ 2 + 4 * mD ^ 2) ^ 2 - MR ^ 2) / 4 := by ring
      _ = mD ^ 2 := by rw [hsqrt_sq]; ring
  have hlight_pos : 0 < seesawLightMass mD MR := by
    unfold seesawLightMass
    linarith
  have hheavy_gt : MR < seesawHeavyMass mD MR := by
    unfold seesawHeavyMass
    linarith
  have hlight_lt : seesawLightMass mD MR < mD ^ 2 / MR := by
    have hmul_lt : MR * seesawLightMass mD MR < seesawHeavyMass mD MR * seesawLightMass mD MR :=
      mul_lt_mul_of_pos_right hheavy_gt hlight_pos
    rw [hprod] at hmul_lt
    exact (lt_div_iff₀ hMR).mpr (by linarith)
  exact ⟨hdiff, hprod, hlight_pos, hlight_lt⟩

end UEOTPhysicsUnification.ElectroweakCustodialAndSeesaw
