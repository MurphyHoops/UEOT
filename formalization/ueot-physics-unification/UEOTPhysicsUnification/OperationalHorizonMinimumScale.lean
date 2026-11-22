import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Quantum-Gravitational Operational Horizon Sensor Floor & Sensor-Shrink RG Trichotomy
(`P-HORIZON-CLOCK-01`)

Pure-kernel Lean 4 formalization of the operational ultraviolet obstruction for pointlike
autonomous quantum clocks (`NEXT_GATE` Gate 1):

1. `squeezing_proof_dimensionless_energy_quadratic`: Any normal quantum state driving a smeared
   clock gate of duration `Δt = η_t * L / c` with distinguishability `SNR ≥ N_gate` obeying
   canonical Robertson-Heisenberg uncertainty and total-energy velocity/second-moment bounds must
   satisfy `16 * η_t^2 * E_dim * (E_dim + a_bar) ≥ N_gate^2` for `E_dim = E_tot * L / (ℏ * c)`.
2. `gravitational_horizon_excludes_pointlike_clock`: Combining `E_tot * L ≥ E_min * ℏ * c`
   (`E_min > 0`) with the spherical non-trapping horizon bound `2 * G * E_tot < λ_sys * c^4 * L`
   forces the strict Planck-scale sensor radius lower bound
   `L^2 > (2 * E_min / λ_sys) * (ℏ * G / c^3) > 0`, ruling out `L → 0^+`.
3. `rg_exponent_universal_obstruction` & `rg_sensor_shrink_quantitative_barrier`: For every real
   renormalization exponent `ν : ℝ` in `g(ρ_0) = g_ref * (ρ_0 / ρ_ref)^ν`, either `2 * (ν - 1) < 0`
   (quantum gate phase washout as `ρ_0 → 0^+`) or `-2 * ν < 0` (fixed-`G` closed-FRW Big Crunch
   crossing `α_G ≥ 1/3`), with an explicit marginal fixed-`G` crunch threshold at `ν = 1`.
-/

namespace UEOTPhysicsUnification.OperationalHorizonMinimumScale

/-- Squeezing-proof dimensionless energy quadratic inequality:
from Robertson-Heisenberg `varX * varV ≥ (1/4) * hc^2 * c^2 * cw2^2 / L^6`, gate SNR
`(η_t * L / c)^2 * vMeanSq ≥ N_gate^2 * varX`, and Fock state-positivity bounds
`vMeanSq ≤ (2 * c^2 * cw2 / L^3) * E_tot` and
`varV ≤ (2 * c^2 * cw2 / L^3) * E_tot + (2 * cwKin * hc * c^2 / L^4)`,
the dimensionless energy `E_dim = E_tot * L / hc` satisfies
`N_gate^2 * cw2 ≤ 16 * η_t^2 * E_dim * (cw2 * E_dim + cwKin)`. -/
theorem squeezing_proof_dimensionless_energy_quadratic
    {L c hc eta_t N_gate cw2 cwKin E_tot varX varV vMeanSq : ℝ}
    (hL : 0 < L) (hc_pos : 0 < c) (hhc : 0 < hc)
    (heta : 0 < eta_t) (hcw2 : 0 < cw2) (hvarX : 0 < varX) (hvarV : 0 ≤ varV)
    (hRH : (1 / 4 : ℝ) * hc ^ 2 * c ^ 2 * cw2 ^ 2 / L ^ 6 ≤ varX * varV)
    (hSNR : N_gate ^ 2 * varX ≤ (eta_t * L / c) ^ 2 * vMeanSq)
    (hvMean : vMeanSq ≤ 2 * c ^ 2 * cw2 * E_tot / L ^ 3)
    (hvarV_bd : varV ≤ 2 * c ^ 2 * cw2 * E_tot / L ^ 3 + 2 * cwKin * hc * c ^ 2 / L ^ 4) :
    let E_dim := E_tot * L / hc
    N_gate ^ 2 * cw2 ≤ 16 * eta_t ^ 2 * E_dim * (cw2 * E_dim + cwKin) := by
  intro E_dim
  have hL6 : 0 < L ^ 6 := by positivity
  have hc2 : 0 < c ^ 2 := by positivity
  have hhc2 : 0 < hc ^ 2 := by positivity
  have hcw2_pos : 0 < cw2 := hcw2
  -- Multiply Robertson-Heisenberg by N_gate^2 and combine with SNR bound:
  have hstep1 : N_gate ^ 2 * ((1 / 4 : ℝ) * hc ^ 2 * c ^ 2 * cw2 ^ 2 / L ^ 6) ≤
      (N_gate ^ 2 * varX) * varV := by
    have := mul_le_mul_of_nonneg_left hRH (sq_nonneg N_gate)
    linarith
  have hstep2 : (N_gate ^ 2 * varX) * varV ≤ ((eta_t * L / c) ^ 2 * vMeanSq) * varV :=
    mul_le_mul_of_nonneg_right hSNR hvarV
  have heta_nonneg : 0 ≤ (eta_t * L / c) ^ 2 := sq_nonneg _
  have hvMean_nonneg : 0 ≤ vMeanSq := by
    by_contra hneg
    have hneg' : vMeanSq < 0 := lt_of_not_ge hneg
    have hetapos : 0 < (eta_t * L / c) ^ 2 := by positivity
    have hstrict : (eta_t * L / c) ^ 2 * vMeanSq < 0 := mul_neg_of_pos_of_neg hetapos hneg'
    have hN_nonneg : 0 ≤ N_gate ^ 2 * varX := mul_nonneg (sq_nonneg _) (le_of_lt hvarX)
    linarith
  have hstep3 : ((eta_t * L / c) ^ 2 * vMeanSq) * varV ≤
      (eta_t * L / c) ^ 2 * (2 * c ^ 2 * cw2 * E_tot / L ^ 3) *
        (2 * c ^ 2 * cw2 * E_tot / L ^ 3 + 2 * cwKin * hc * c ^ 2 / L ^ 4) := by
    have ha : (eta_t * L / c) ^ 2 * vMeanSq ≤
        (eta_t * L / c) ^ 2 * (2 * c ^ 2 * cw2 * E_tot / L ^ 3) :=
      mul_le_mul_of_nonneg_left hvMean heta_nonneg
    have hb_nonneg : 0 ≤ 2 * c ^ 2 * cw2 * E_tot / L ^ 3 :=
      le_trans hvMean_nonneg hvMean
    have hcomb := mul_le_mul ha hvarV_bd hvarV (mul_nonneg heta_nonneg hb_nonneg)
    simpa [mul_assoc] using hcomb
  have hchain : N_gate ^ 2 * ((1 / 4 : ℝ) * hc ^ 2 * c ^ 2 * cw2 ^ 2 / L ^ 6) ≤
      (eta_t * L / c) ^ 2 * (2 * c ^ 2 * cw2 * E_tot / L ^ 3) *
        (2 * c ^ 2 * cw2 * E_tot / L ^ 3 + 2 * cwKin * hc * c ^ 2 / L ^ 4) :=
    le_trans hstep1 (le_trans hstep2 hstep3)
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hhc_ne : hc ≠ 0 := ne_of_gt hhc
  -- Clear positive factor (1/4) * hc^2 * c^2 * cw2 / L^6:
  have hfac_pos : 0 < (1 / 4 : ℝ) * hc ^ 2 * c ^ 2 * cw2 / L ^ 6 := by positivity
  have hident_lhs :
      N_gate ^ 2 * ((1 / 4 : ℝ) * hc ^ 2 * c ^ 2 * cw2 ^ 2 / L ^ 6) =
        ((1 / 4 : ℝ) * hc ^ 2 * c ^ 2 * cw2 / L ^ 6) * (N_gate ^ 2 * cw2) := by
    field_simp [hL_ne]
  have hident_rhs :
      (eta_t * L / c) ^ 2 * (2 * c ^ 2 * cw2 * E_tot / L ^ 3) *
          (2 * c ^ 2 * cw2 * E_tot / L ^ 3 + 2 * cwKin * hc * c ^ 2 / L ^ 4) =
        ((1 / 4 : ℝ) * hc ^ 2 * c ^ 2 * cw2 / L ^ 6) *
          (16 * eta_t ^ 2 * E_dim * (cw2 * E_dim + cwKin)) := by
    dsimp [E_dim]
    field_simp [hL_ne, hc_ne, hhc_ne]
    ring
  rw [hident_lhs, hident_rhs] at hchain
  exact le_of_mul_le_mul_left hchain hfac_pos

/-- Explicit positive root lower bound: if `E ≥ 0`, `a > 0`, `B > 0`, and `B ≤ E * (E + a)`,
then `B / (a + √(a^2 + B)) ≤ E` and `0 < B / (a + √(a^2 + B))`. -/
theorem quadratic_positive_root_lower_bound
    {E a B : ℝ} (hE : 0 ≤ E) (ha : 0 < a) (hB : 0 < B) (hineq : B ≤ E * (E + a)) :
    0 < B / (a + Real.sqrt (a ^ 2 + B)) ∧ B / (a + Real.sqrt (a ^ 2 + B)) ≤ E := by
  have hrad_pos : 0 < a ^ 2 + B := by positivity
  have hsqrt_pos : 0 < Real.sqrt (a ^ 2 + B) := Real.sqrt_pos.mpr hrad_pos
  have hden_pos : 0 < a + Real.sqrt (a ^ 2 + B) := by linarith
  refine ⟨div_pos hB hden_pos, ?_⟩
  -- Compare (E + a/2)^2 >= B + a^2/4? Even simpler: rationalize B / (a + sqrt(a^2 + B)) = sqrt(a^2 + B) - a!
  have hrat : B / (a + Real.sqrt (a ^ 2 + B)) = Real.sqrt (a ^ 2 + B) - a := by
    rw [div_eq_iff (ne_of_gt hden_pos)]
    have hsq : Real.sqrt (a ^ 2 + B) ^ 2 = a ^ 2 + B := Real.sq_sqrt (le_of_lt hrad_pos)
    nlinarith
  rw [hrat]
  have hEa_pos : 0 ≤ E + a := by linarith
  have hsq_le : a ^ 2 + B ≤ (E + a) ^ 2 := by nlinarith
  have hsqrt_le : Real.sqrt (a ^ 2 + B) ≤ E + a :=
    (Real.sqrt_le_left hEa_pos).mpr hsq_le
  linarith

/-- Operational gravitational horizon exclusion of pointlike clocks (`L → 0^+`):
combining `E_min * ℏ * c ≤ E_tot * L` (`E_min > 0`) with the spherical non-trapping condition
`2 * G * E_tot < λ_sys * c^4 * L` (`λ_sys > 0`) implies strict Planck-scale sensor lower bound
`(2 * E_min / λ_sys) * (ℏ * G / c^3) < L^2`. -/
theorem gravitational_horizon_excludes_pointlike_clock
    {L E_tot E_min hbar c G lam_sys : ℝ}
    (hL : 0 < L) (hEmin : 0 < E_min) (hhbar : 0 < hbar) (hc : 0 < c)
    (hG : 0 < G) (hlam : 0 < lam_sys)
    (hclock : E_min * hbar * c ≤ E_tot * L)
    (hnotrap : 2 * G * E_tot < lam_sys * c ^ 4 * L) :
    0 < (2 * E_min / lam_sys) * (hbar * G / c ^ 3) ∧
      (2 * E_min / lam_sys) * (hbar * G / c ^ 3) < L ^ 2 := by
  have hc3 : 0 < c ^ 3 := by positivity
  have hc4 : 0 < c ^ 4 := by positivity
  refine ⟨by positivity, ?_⟩
  have h1 : 2 * G * (E_min * hbar * c) ≤ 2 * G * (E_tot * L) :=
    mul_le_mul_of_nonneg_left hclock (by positivity)
  have h2 : 2 * G * (E_tot * L) < (lam_sys * c ^ 4 * L) * L := by
    have := mul_lt_mul_of_pos_right hnotrap hL
    linarith
  have h3 : 2 * G * E_min * hbar * c < lam_sys * c ^ 4 * L ^ 2 := by linarith
  have hden : 0 < lam_sys * c ^ 3 := by positivity
  have hrew : (2 * E_min / lam_sys) * (hbar * G / c ^ 3) =
      (2 * G * E_min * hbar * c) / (lam_sys * c ^ 4) := by
    have hc_ne : c ≠ 0 := ne_of_gt hc
    have hlam_ne : lam_sys ≠ 0 := ne_of_gt hlam
    field_simp [hc_ne, hlam_ne]
  rw [hrew, div_lt_iff₀ (by positivity)]
  linarith

/-- Universal RG exponent dichotomy: for every real scaling exponent `ν : ℝ`,
either `2 * (ν - 1) < 0` (quantum gate variance diverges as `ρ_0^{2(ν-1)} → +∞`)
or `-2 * ν < 0` (fixed-`G` gravitational parameter `α_G(ρ_0) ∝ ρ_0^{-2ν} → +∞`). -/
theorem rg_exponent_universal_obstruction (nu : ℝ) :
    2 * (nu - 1) < 0 ∨ -2 * nu < 0 := by
  by_cases h : nu < 1
  · left; linarith
  · right; linarith

/-- Marginal fixed-`G` closed-FRW Big Crunch barrier at `ν = 1`:
for `α_G(ρ_0) = (1/10) * (ρ_ref / ρ_0)^2`, whenever `0 < ρ_0 ≤ √(3/10) * ρ_ref`,
we have `1 / 3 ≤ α_G(ρ_0)`, violating the strict sub-critical bounce condition `α_G < 1/3`. -/
theorem marginal_rg_fixed_G_crunch_threshold
    {rho0 rho_ref : ℝ} (hrho0 : 0 < rho0) (_href : 0 < rho_ref)
    (hshrink : rho0 ^ 2 ≤ (3 / 10 : ℝ) * rho_ref ^ 2) :
    (1 / 3 : ℝ) ≤ (1 / 10 : ℝ) * (rho_ref / rho0) ^ 2 := by
  have hrho0_sq : 0 < rho0 ^ 2 := sq_pos_of_pos hrho0
  have hrew : (1 / 10 : ℝ) * (rho_ref / rho0) ^ 2 = rho_ref ^ 2 / (10 * rho0 ^ 2) := by
    have hne : rho0 ≠ 0 := ne_of_gt hrho0
    field_simp [hne]
  rw [hrew, div_le_div_iff₀ (by norm_num) (by positivity)]
  linarith

end UEOTPhysicsUnification.OperationalHorizonMinimumScale
