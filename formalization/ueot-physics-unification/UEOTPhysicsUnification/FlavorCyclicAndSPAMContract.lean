import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Three-Channel Flavor Cyclic Closure & SPAM/Leakage Calibration Identifiability
(`P-FLAVOR-04`, `P-SPAM-05`)

Closes two empirical-interface identifiability gates from `sectors/RESULTS.md` §3 (`PREMISES` Row 11)
and `PREMISES_AND_RESPONSIBILITIES.md` §5 Row 2:

1. **P-FLAVOR-04 — Rank-One `ΔF = 2` Two-Channel Surjectivity vs Three-Channel Rephasing-Invariant Lock**:
   - `two_channel_bd_bs_always_realizable`: Formalizes the exact non-identifiability construction of
     `sectors/RESULTS.md` §3: for *any* two complex `ΔF = 2` targets `(zd, zs)` (represented via polar
     square roots `wd^2 = zd, ws^2 = zs` with `|wd|^2 + |ws|^2 > 0`), setting `ub = 1/√2` and
     `κ = 4(|zd| + |zs|)` realizes both `(zd, zs)` simultaneously with a strictly normalized 3-flavor
     unit vector `|ud|^2 + |us|^2 + |ub|^2 = 1`. Thus `(B_d, B_s)` alone cannot falsify rank-one matching.
   - `cyclicJ_quark_rephasing_invariant` & `rank_one_cyclicJ_real_nonneg`: Adding the kaon channel `C_ds`
     forms the cyclic product `J_ΔF2 = C_ds C_sb C_bd`, which is strictly invariant under arbitrary
     independent phase rotations of `(d, s, b)` and satisfies `Im(J_ΔF2) = 0` and `Re(J_ΔF2) ≥ 0`.

2. **P-SPAM-05 — Asymmetric SPAM + Leakage Calibration Identifiability & Lipschitz Stability**:
   - `uncalibrated_visibility_contrast_degeneracy`: Without reference shots, symmetric SPAM visibility `η`
     and dynamical coherence `C` enter only through `η * C`, rendering `(η, C)` unidentifiable from a
     single Ramsey curve.
   - `spam_leakage_affine_exact_recovery` & `spam_leakage_estimator_lipschitz`: Retaining all three
     detector outcomes `{0, 1, leak}` and adding zero-time reference preparations `|0⟩` and `|1⟩`
     (`y_1 - y_0 = (1 - ℓ)(1 - e_0 - e_1) > 0`) uniquely recovers the true subspace probability `p_1`
     free of `(e_0, e_1, ℓ)` bias, with exact Lipschitz error amplification `1 / ((1 - ℓ)(1 - e_0 - e_1))`.
-/

namespace UEOTPhysicsUnification.FlavorCyclicAndSPAMContract

/-! ## 1. P-FLAVOR-04: Two-Channel Surjectivity vs Three-Channel Cyclic Phase Lock -/

/-- Rank-one `ΔF = 2` Wilson coefficient `C_{ab} = κ (u_a * conj(u_b))^2` for real `κ`. -/
def wilsonC (kappa : ℝ) (ua ub : ℂ) : ℂ :=
  (kappa : ℂ) * (ua * star ub) ^ 2

/-- Cyclic three-meson `(K, B_s, B_d)` product `C_ds * C_sb * C_bd`. -/
def cyclicJ (Cds Csb Cbd : ℂ) : ℂ :=
  Cds * Csb * Cbd

/-- Rephasing invariance: under arbitrary unit-norm quark phase rotations `u_q ↦ z_q u_q`
(`z_q * conj(z_q) = 1`), `cyclicJ` is strictly invariant. -/
theorem cyclicJ_quark_rephasing_invariant
    (kappa : ℝ) (ud us ub zd zs zb : ℂ)
    (hzd : zd * star zd = 1) (hzs : zs * star zs = 1) (hzb : zb * star zb = 1) :
    cyclicJ (wilsonC kappa (zd * ud) (zs * us))
            (wilsonC kappa (zs * us) (zb * ub))
            (wilsonC kappa (zb * ub) (zd * ud)) =
      cyclicJ (wilsonC kappa ud us) (wilsonC kappa us ub) (wilsonC kappa ub ud) := by
  unfold cyclicJ wilsonC
  simp only [star_mul]
  calc
    (kappa : ℂ) * (zd * ud * (star us * star zs)) ^ 2 *
        ((kappa : ℂ) * (zs * us * (star ub * star zb)) ^ 2) *
        ((kappa : ℂ) * (zb * ub * (star ud * star zd)) ^ 2)
        = ((zd * star zd) ^ 2 * (zs * star zs) ^ 2 * (zb * star zb) ^ 2) *
            ((kappa : ℂ) * (ud * star us) ^ 2 *
              ((kappa : ℂ) * (us * star ub) ^ 2) *
              ((kappa : ℂ) * (ub * star ud) ^ 2)) := by ring
    _ = (kappa : ℂ) * (ud * star us) ^ 2 *
          ((kappa : ℂ) * (us * star ub) ^ 2) *
          ((kappa : ℂ) * (ub * star ud) ^ 2) := by
          rw [hzd, hzs, hzb]
          ring

/-- Exact closed-form evaluation of `cyclicJ` in any rank-one model:
`C_ds * C_sb * C_bd = ↑(κ^3 * normSq(ud)^2 * normSq(us)^2 * normSq(ub)^2)`. -/
theorem rank_one_cyclicJ_closed_form (kappa : ℝ) (ud us ub : ℂ) :
    cyclicJ (wilsonC kappa ud us) (wilsonC kappa us ub) (wilsonC kappa ub ud) =
      ((kappa ^ 3 * (Complex.normSq ud) ^ 2 * (Complex.normSq us) ^ 2 *
        (Complex.normSq ub) ^ 2 : ℝ) : ℂ) := by
  unfold cyclicJ wilsonC
  have hd : ud * star ud = ((Complex.normSq ud : ℝ) : ℂ) := Complex.mul_conj ud
  have hs : us * star us = ((Complex.normSq us : ℝ) : ℂ) := Complex.mul_conj us
  have hb : ub * star ub = ((Complex.normSq ub : ℝ) : ℂ) := Complex.mul_conj ub
  calc
    (kappa : ℂ) * (ud * star us) ^ 2 *
        ((kappa : ℂ) * (us * star ub) ^ 2) *
        ((kappa : ℂ) * (ub * star ud) ^ 2)
        = (kappa : ℂ) ^ 3 * (ud * star ud) ^ 2 * (us * star us) ^ 2 * (ub * star ub) ^ 2 := by ring
    _ = ((kappa ^ 3 * (Complex.normSq ud) ^ 2 * (Complex.normSq us) ^ 2 *
          (Complex.normSq ub) ^ 2 : ℝ) : ℂ) := by
          rw [hd, hs, hb]
          push_cast
          ring

/-- Reality and nonnegativity lock (`P-FLAVOR-04`): for any real coupling `κ ≥ 0` (`κ = Δ_L^2 / (2 M_{Z'}^2)`),
the cyclic three-meson invariant has strictly zero imaginary part and nonnegative real part. -/
theorem rank_one_cyclicJ_real_nonneg
    {kappa : ℝ} (hk : 0 ≤ kappa) (ud us ub : ℂ) :
    (cyclicJ (wilsonC kappa ud us) (wilsonC kappa us ub) (wilsonC kappa ub ud)).im = 0 ∧
      0 ≤ (cyclicJ (wilsonC kappa ud us) (wilsonC kappa us ub) (wilsonC kappa ub ud)).re := by
  rw [rank_one_cyclicJ_closed_form]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  positivity

/-- Two-channel `(B_d, B_s)` unconstrained realizability theorem (`sectors/RESULTS.md` §3):
for any nonzero pair of complex targets `(wd^2, ws^2)`, there exist `κ > 0` and `(ud, us, ub) ∈ ℂ^3`
satisfying `normSq ud + normSq us + normSq ub = 1` that simultaneously realize `C_bd = wd^2` and `C_bs = ws^2`. -/
theorem two_channel_bd_bs_always_realizable
    (wd ws : ℂ) (hne : 0 < Complex.normSq wd + Complex.normSq ws) :
    let kappa : ℝ := 4 * (Complex.normSq wd + Complex.normSq ws)
    let invSqrt2 : ℝ := 1 / Real.sqrt 2
    let scale : ℝ := Real.sqrt (2 / kappa)
    let ub : ℂ := (invSqrt2 : ℂ)
    let ud : ℂ := (scale : ℂ) * star wd
    let us : ℂ := (scale : ℂ) * star ws
    0 < kappa ∧
      Complex.normSq ud + Complex.normSq us + Complex.normSq ub = 1 ∧
      wilsonC kappa ub ud = wd ^ 2 ∧
      wilsonC kappa ub us = ws ^ 2 := by
  intro kappa invSqrt2 scale ub ud us
  have hk_pos : 0 < kappa := by
    dsimp [kappa]
    linarith
  have hk_ne : kappa ≠ 0 := ne_of_gt hk_pos
  have h2_pos : (0 : ℝ) ≤ 2 := by norm_num
  have h2k_nonneg : 0 ≤ 2 / kappa := by positivity
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2_pos
  have hscale_sq : scale ^ 2 = 2 / kappa := Real.sq_sqrt h2k_nonneg
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hub_norm : Complex.normSq ub = 1 / 2 := by
    dsimp [ub, invSqrt2]
    rw [Complex.normSq_ofReal]
    calc
      1 / Real.sqrt 2 * (1 / Real.sqrt 2) = 1 / (Real.sqrt 2 ^ 2) := by ring
      _ = 1 / 2 := by rw [hsqrt2_sq]
  have hud_norm : Complex.normSq ud = (2 / kappa) * Complex.normSq wd := by
    dsimp [ud]
    rw [map_mul, Complex.normSq_ofReal, Complex.normSq_conj]
    calc
      scale * scale * Complex.normSq wd = scale ^ 2 * Complex.normSq wd := by ring
      _ = (2 / kappa) * Complex.normSq wd := by rw [hscale_sq]
  have hus_norm : Complex.normSq us = (2 / kappa) * Complex.normSq ws := by
    dsimp [us]
    rw [map_mul, Complex.normSq_ofReal, Complex.normSq_conj]
    calc
      scale * scale * Complex.normSq ws = scale ^ 2 * Complex.normSq ws := by ring
      _ = (2 / kappa) * Complex.normSq ws := by rw [hscale_sq]
  refine ⟨hk_pos, ?_, ?_, ?_⟩
  · rw [hud_norm, hus_norm, hub_norm]
    dsimp [kappa]
    have hsum_ne : Complex.normSq wd + Complex.normSq ws ≠ 0 := ne_of_gt hne
    field_simp [hsum_ne]
    ring
  · unfold wilsonC
    have hud_star : star ud = (scale : ℂ) * wd := by
      dsimp [ud]
      simp [Complex.star_def]
    rw [hud_star]
    dsimp [ub]
    have hprod_sq : ((invSqrt2 : ℂ) * ((scale : ℂ) * wd)) ^ 2 =
        (((invSqrt2 ^ 2 * scale ^ 2 : ℝ) : ℂ)) * wd ^ 2 := by
      push_cast
      ring
    rw [hprod_sq]
    have hinv_sq : invSqrt2 ^ 2 = 1 / 2 := by
      dsimp [invSqrt2]
      calc
        (1 / Real.sqrt 2) ^ 2 = 1 / (Real.sqrt 2 ^ 2) := by ring
        _ = 1 / 2 := by rw [hsqrt2_sq]
    rw [hinv_sq, hscale_sq]
    have hkC : (kappa : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk_ne
    push_cast
    field_simp [hkC]
  · unfold wilsonC
    have hus_star : star us = (scale : ℂ) * ws := by
      dsimp [us]
      simp [Complex.star_def]
    rw [hus_star]
    dsimp [ub]
    have hprod_sq : ((invSqrt2 : ℂ) * ((scale : ℂ) * ws)) ^ 2 =
        (((invSqrt2 ^ 2 * scale ^ 2 : ℝ) : ℂ)) * ws ^ 2 := by
      push_cast
      ring
    rw [hprod_sq]
    have hinv_sq : invSqrt2 ^ 2 = 1 / 2 := by
      dsimp [invSqrt2]
      calc
        (1 / Real.sqrt 2) ^ 2 = 1 / (Real.sqrt 2 ^ 2) := by ring
        _ = 1 / 2 := by rw [hsqrt2_sq]
    rw [hinv_sq, hscale_sq]
    have hkC : (kappa : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk_ne
    push_cast
    field_simp [hkC]

/-! ## 2. P-SPAM-05: Asymmetric SPAM + Leakage Calibration Identifiability -/

/-- Observed bright-outcome probability under leakage `leak ∈ [0, 1)` and asymmetric SPAM `(e0, e1)`. -/
def observedBrightProb (leak e0 e1 p1 : ℝ) : ℝ :=
  (1 - leak) * (e0 + (1 - e0 - e1) * p1)

/-- Single-curve multiplicative scale degeneracy: under symmetric SPAM `e0 = e1 = (1 - η)/2`,
rescaling `(η, C) ↦ (α η, C / α)` (`α ≠ 0`) produces identical bright-outcome probabilities. -/
theorem uncalibrated_visibility_contrast_degeneracy
    (leak eta C alpha : ℝ) (ha : alpha ≠ 0) :
    observedBrightProb leak ((1 - alpha * eta) / 2) ((1 - alpha * eta) / 2) ((1 + C / alpha) / 2) =
      observedBrightProb leak ((1 - eta) / 2) ((1 - eta) / 2) ((1 + C) / 2) := by
  unfold observedBrightProb
  field_simp [ha]
  ring

/-- Affine SPAM-and-leakage-calibrated estimator `(y - y0) / (y1 - y0)` from reference shots `|0⟩, |1⟩`. -/
noncomputable def calibratedProbEstimator (y0 y1 y : ℝ) : ℝ :=
  (y - y0) / (y1 - y0)

/-- Exact bias-free recovery of `p1` across arbitrary asymmetric `(e0, e1)` and leakage `leak < 1`
whenever `e0 + e1 < 1`. -/
theorem spam_leakage_affine_exact_recovery
    {leak e0 e1 : ℝ} (hleak : leak < 1) (hspam : e0 + e1 < 1) (p1 : ℝ) :
    let y0 := observedBrightProb leak e0 e1 0
    let y1 := observedBrightProb leak e0 e1 1
    0 < y1 - y0 ∧
      calibratedProbEstimator y0 y1 (observedBrightProb leak e0 e1 p1) = p1 := by
  intro y0 y1
  have h1l : 0 < 1 - leak := by linarith
  have hvis : 0 < 1 - e0 - e1 := by linarith
  have hgap_eq : y1 - y0 = (1 - leak) * (1 - e0 - e1) := by
    dsimp [y0, y1, observedBrightProb]
    ring
  have hgap_pos : 0 < y1 - y0 := by
    rw [hgap_eq]
    positivity
  have hgap_ne : y1 - y0 ≠ 0 := ne_of_gt hgap_pos
  refine ⟨hgap_pos, ?_⟩
  unfold calibratedProbEstimator
  have hnum : observedBrightProb leak e0 e1 p1 - y0 = (y1 - y0) * p1 := by
    dsimp [y0, y1, observedBrightProb]
    ring
  rw [hnum]
  field_simp [hgap_ne]

/-- Quantitative Lipschitz stability of the calibrated estimator with respect to empirical shot error. -/
theorem spam_leakage_estimator_lipschitz
    {leak e0 e1 y y' : ℝ} (hleak : leak < 1) (hspam : e0 + e1 < 1) :
    let y0 := observedBrightProb leak e0 e1 0
    let y1 := observedBrightProb leak e0 e1 1
    |calibratedProbEstimator y0 y1 y' - calibratedProbEstimator y0 y1 y| =
      |y' - y| / ((1 - leak) * (1 - e0 - e1)) := by
  intro y0 y1
  have h1l : 0 < 1 - leak := by linarith
  have hvis : 0 < 1 - e0 - e1 := by linarith
  have hgap_eq : y1 - y0 = (1 - leak) * (1 - e0 - e1) := by
    dsimp [y0, y1, observedBrightProb]
    ring
  have hpos : 0 < (1 - leak) * (1 - e0 - e1) := by positivity
  unfold calibratedProbEstimator
  have hsub : (y' - y0) / (y1 - y0) - (y - y0) / (y1 - y0) = (y' - y) / (y1 - y0) := by ring
  rw [hsub, hgap_eq, abs_div, abs_of_pos hpos]

end UEOTPhysicsUnification.FlavorCyclicAndSPAMContract
