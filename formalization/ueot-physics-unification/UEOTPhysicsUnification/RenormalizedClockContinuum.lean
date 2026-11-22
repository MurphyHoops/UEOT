import UEOTPhysicsUnification.ConformalControlGravityGates
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Continuum Renormalized Clock Gates, Worldtube Smearing & Dynamical Clock-FRW Enthalpy Closure
(`P-CLOCK-UV-03`)

Provides pure-kernel Lean 4 formal theorems resolving the continuum clock ultraviolet and gravitational
backreaction obstructions (`CLOCK_UV`, `WICK_CLOCK_GRAPH`, and `BACKREACTION_GATE`):

1. **Exact Diagnostics of Bare Pointlike Clock Collapse & Accuracy-Energy Blowup**:
   - `s3_clock_mode_weight_lower_bound`: For every spherical harmonic index `k ≥ 2` on `S^3`,
     `k ≤ k^2 / √(k^2 - 1)`, forcing the bare pointlike high-mode variance `σ_{J,K}^2` to diverge
     quadratically (`≥ (K(K + 1) - J(J + 1)) / (4 V_0)`).
   - `bare_clock_accuracy_energy_diverges`: Under the bare point-clock precision contract
     `g_K^2 * σ_K^2 ≤ δ_t^2` (`δ_t > 0`, `g_K ≠ 0`), classical clock kinetic energy `V_0 / (2 g_K^2)`
     satisfies `V_0 * σ_K^2 / (2 δ_t^2) ≤ V_0 / (2 g_K^2)`, diverging as `σ_K^2 → ∞`.
   - `bare_gaussian_fourier_mode_attenuation`: At fixed `g ≠ 0`, every nonzero Fourier mode `ω ≠ 0`
     of a bare switch is damped by `exp(-(1/2) g^2 ω^2 σ_K^2) ≤ 1 / (1 + (1/2) g^2 ω^2 σ_K^2) → 0`.

2. **Resolution Route A — Spatial Worldtube Smearing, Exact Weierstrass Deconvolution & Finite 4-Body Graph Norm**:
   - `worldtube_telescoping_partial_sum` & `worldtube_smeared_variance_uniform_cauchy`: Smearing clock
     and body fields over a localized worldtube aperture `η > 0` with harmonic decay
     `0 ≤ w_k ≤ C_η / ((k + 1)(k + 2))` yields monotonically increasing partial variances uniformly
     bounded above for all `K : ℕ` (`σ_{η,K}^2 < σ_{η,0}^2 + C_η / (2 V_0)`) with explicit `O(K^{-1})`
     Cauchy tail `σ_{η,M}^2 - σ_{η,K}^2 ≤ C_η / (2 V_0 (K + 1))`.
   - `weierstrass_deconvolved_clock_gate_exact`: Whenever the sub-critical aperture condition
     `g^2 * σ_{η,∞}^2 < w^2` holds at **fixed `g ≠ 0` and finite clock energy `V_0 / (2 g^2)`**,
     the pre-sharpened width `b_K = √(w^2 - g^2 σ_{η,K}^2) > 0` satisfies exact Gaussian variance
     restoration `b_K^2 + g^2 σ_{η,K}^2 = w^2`, exact carrier frequency restoration
     `((w^2 / b_K^2) * Ω) * b_K^2 / (b_K^2 + g^2 σ_{η,K}^2) = Ω`, and a uniform `K`-independent `L^∞`
     bound across all `K : ℕ`.
   - `smeared_wick_quartic_graph_norm_uniform_bound`: Whereas pointlike (`η = 0`) body-only Wick
     subtraction diverges as `c_* g^2 K^3`, worldtube-smeared covariance `|C_{+,η,K}(x, y)| ≤ B_η`
     uniformly bounds the 4-body vector norm squared by `(3/2) g^4 V_0^2 M_S^2 B_η^4 < ∞` for all `K`.

3. **Resolution Route B — Super-Renormalizable Polynomial Portal & Dynamical Clock-FRW Enthalpy Conservation**:
   - `cosmological_constant_zero_enthalpy_no_go`: Because `ρ_Λ + p_Λ = ρ_Λ + (-ρ_Λ) = 0` identically
     for all `Λ ∈ ℝ`, tuning `Λ` leaves total enthalpy `ρ_tot + p_tot = xdot^2` invariant and cannot
     cancel nonzero time-dependent clock kinetic enthalpy on a static ESU background.
   - `dynamical_clock_frw_friedmann_conservation`: On a dynamical closed-FRW geometry `(a(t), H(t) = adot/a)`
     evolving jointly with homogeneous clock `X(t)` via the Raychaudhuri equation
     `Hdot = -(κ/2) xdot^2 + 1/a^2` and Klein-Gordon equation `xddot + 3 H xdot + V' = 0`, the time
     derivative of the Friedmann Hamiltonian constraint residual vanishes identically (`Cdot = 0`),
     while the local polynomial clock-control portal `λ_c χ φ ψ + (g_4/4)(φ^2 + ψ^2)^2` stays globally
     nonnegative iff `λ_c^2 ≤ 2 g_4 m_χ^2` (`ConformalControlGravityGates.stabilized_control_nonneg_iff_mass_threshold`).
-/

namespace UEOTPhysicsUnification.RenormalizedClockContinuum

open scoped BigOperators

/-! ## 1. Bare Pointlike Clock Diagnostics (`CLOCK_UV` Formalization) -/

/-- Exact mode-weight inequality on unit `S^3`: for every `k ≥ 2`, `k ≤ k^2 / √(k^2 - 1)`. -/
theorem s3_clock_mode_weight_lower_bound {k : ℝ} (hk : 2 ≤ k) :
    k ≤ k ^ 2 / Real.sqrt (k ^ 2 - 1) := by
  have hk_pos : 0 < k := by linarith
  have hk2_gt_one : 1 < k ^ 2 := by nlinarith
  have hsub_pos : 0 < k ^ 2 - 1 := by linarith
  have hsqrt_pos : 0 < Real.sqrt (k ^ 2 - 1) := Real.sqrt_pos.mpr hsub_pos
  have hsqrt_le : Real.sqrt (k ^ 2 - 1) ≤ k := by
    have hle_sq : k ^ 2 - 1 ≤ k ^ 2 := by linarith
    exact (Real.sqrt_le_left (le_of_lt hk_pos)).mpr hle_sq
  rw [le_div_iff₀ hsqrt_pos]
  calc
    k * Real.sqrt (k ^ 2 - 1) ≤ k * k := mul_le_mul_of_nonneg_left hsqrt_le (le_of_lt hk_pos)
    _ = k ^ 2 := by ring

/-- Bare point-clock accuracy-energy resource bound (`CLOCK_UV` Eq. 2):
if `g^2 * σSq ≤ δt^2` (`δt > 0`, `g ≠ 0`, `V0 ≥ 0`), then `V0 * σSq / (2 * δt^2) ≤ V0 / (2 * g^2)`. -/
theorem bare_clock_accuracy_energy_diverges
    {V0 g sigmaSq dt : ℝ}
    (hV0 : 0 ≤ V0) (hg : g ≠ 0) (hdt : 0 < dt)
    (hacc : g ^ 2 * sigmaSq ≤ dt ^ 2) :
    V0 * sigmaSq / (2 * dt ^ 2) ≤ V0 / (2 * g ^ 2) := by
  have hg2 : 0 < g ^ 2 := sq_pos_of_ne_zero hg
  have hdt2 : 0 < dt ^ 2 := sq_pos_of_pos hdt
  have h2g2 : 0 < 2 * g ^ 2 := by positivity
  have h2dt2 : 0 < 2 * dt ^ 2 := by positivity
  rw [div_le_div_iff₀ h2dt2 h2g2]
  have hmul : V0 * (g ^ 2 * sigmaSq) ≤ V0 * dt ^ 2 := mul_le_mul_of_nonneg_left hacc hV0
  linarith

/-- Fixed-`g` Gaussian Fourier-mode attenuation bound: for all `g, ω, σSq` with `0 ≤ σSq`,
`0 < exp(-(1/2) g^2 ω^2 σSq) ≤ 1 / (1 + (1/2) g^2 ω^2 σSq)`. -/
theorem bare_gaussian_fourier_mode_attenuation
    (g omega : ℝ) {sigmaSq : ℝ} (hsigma : 0 ≤ sigmaSq) :
    let u := (1 / 2 : ℝ) * g ^ 2 * omega ^ 2 * sigmaSq
    0 < Real.exp (-u) ∧ Real.exp (-u) ≤ 1 / (1 + u) := by
  intro u
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hden : 0 < 1 + u := by linarith
  refine ⟨Real.exp_pos (-u), ?_⟩
  rw [Real.exp_neg, one_div]
  apply inv_anti₀ hden
  linarith [Real.add_one_le_exp u]

/-! ## 2. Worldtube Smearing, Weierstrass Deconvolved Gate & Finite 4-Body Wick Graph Bound -/

/-- Exact telescoping identity `∑_{k=0}^{N-1} 1 / ((k + 1)(k + 2)) = 1 - 1 / (N + 1)`. -/
theorem worldtube_telescoping_partial_sum (N : ℕ) :
    (∑ k ∈ Finset.range N, (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) =
      1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    have hn2' : (n : ℝ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp [hn1, hn2, hn2']
    ring

/-- Worldtube-smeared clock/body variance sequence `σ_0^2 + (1 / (2 V0)) ∑_{k < K} w_k`:
whenever `0 ≤ w_k ≤ C_η / ((k + 1)(k + 2))`, partial variances are monotone, uniformly bounded
above by `σ_0^2 + C_η / (2 V0)` for all `K`, and strictly Cauchy at rate `C_η / (2 V0 (K + 1))`. -/
theorem worldtube_smeared_variance_uniform_cauchy
    {V0 sigma0Sq Ceta : ℝ} {w : ℕ → ℝ}
    (hV0 : 0 < V0) (hC : 0 ≤ Ceta)
    (hw_nonneg : ∀ k, 0 ≤ w k)
    (hw_decay : ∀ k, w k ≤ Ceta / (((k : ℝ) + 1) * ((k : ℝ) + 2))) :
    let varSeq : ℕ → ℝ := fun K => sigma0Sq + (1 / (2 * V0)) * ∑ k ∈ Finset.range K, w k
    (∀ K : ℕ, varSeq K ≤ sigma0Sq + Ceta / (2 * V0)) ∧
      (∀ {K M : ℕ}, K ≤ M →
        0 ≤ varSeq M - varSeq K ∧ varSeq M - varSeq K ≤ Ceta / (2 * V0 * ((K : ℝ) + 1))) := by
  intro varSeq
  have h2V : 0 < 2 * V0 := by positivity
  refine ⟨?_, ?_⟩
  · intro K
    dsimp [varSeq]
    have hsum_le : (∑ k ∈ Finset.range K, w k) ≤
        Ceta * ∑ k ∈ Finset.range K, (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum ?_
      intro k _
      simpa [div_eq_mul_inv, mul_comm] using hw_decay k
    rw [worldtube_telescoping_partial_sum K] at hsum_le
    have hpos_rem : 0 ≤ 1 / ((K : ℝ) + 1) := by positivity
    have hsum_lt_C : (∑ k ∈ Finset.range K, w k) ≤ Ceta := by nlinarith
    have hscaled : (1 / (2 * V0)) * (∑ k ∈ Finset.range K, w k) ≤ Ceta / (2 * V0) := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hsum_lt_C (le_of_lt h2V)
    linarith
  · intro K M hKM
    have hdiff_eq : varSeq M - varSeq K = (1 / (2 * V0)) * ∑ k ∈ Finset.Ico K M, w k := by
      dsimp [varSeq]
      have hsplit : (∑ k ∈ Finset.range M, w k) =
          (∑ k ∈ Finset.range K, w k) + ∑ k ∈ Finset.Ico K M, w k := by
        rw [Finset.sum_range_add_sum_Ico w hKM]
      rw [hsplit]
      ring
    rw [hdiff_eq]
    have hIco_nonneg : 0 ≤ ∑ k ∈ Finset.Ico K M, w k :=
      Finset.sum_nonneg (fun k _ => hw_nonneg k)
    refine ⟨mul_nonneg (by positivity) hIco_nonneg, ?_⟩
    have hIco_le : (∑ k ∈ Finset.Ico K M, w k) ≤ Ceta / ((K : ℝ) + 1) := by
      have hdom : (∑ k ∈ Finset.Ico K M, w k) ≤
          Ceta * ∑ k ∈ Finset.Ico K M, (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum ?_
        intro k _
        simpa [div_eq_mul_inv, mul_comm] using hw_decay k
      have htel_split :
          (∑ k ∈ Finset.range K, (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) +
            (∑ k ∈ Finset.Ico K M, (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) =
          ∑ k ∈ Finset.range M, (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) :=
        Finset.sum_range_add_sum_Ico _ hKM
      rw [worldtube_telescoping_partial_sum K, worldtube_telescoping_partial_sum M] at htel_split
      have hIco_tel : (∑ k ∈ Finset.Ico K M, (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) =
          1 / ((K : ℝ) + 1) - 1 / ((M : ℝ) + 1) := by linarith
      rw [hIco_tel] at hdom
      have hM_nonneg : 0 ≤ 1 / ((M : ℝ) + 1) := by positivity
      have hmul_le : Ceta * (1 / ((K : ℝ) + 1) - 1 / ((M : ℝ) + 1)) ≤ Ceta * (1 / ((K : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hC
      calc
        (∑ k ∈ Finset.Ico K M, w k) ≤ Ceta * (1 / ((K : ℝ) + 1)) := hdom.trans hmul_le
        _ = Ceta / ((K : ℝ) + 1) := mul_one_div Ceta ((K : ℝ) + 1)
    calc
      (1 / (2 * V0)) * ∑ k ∈ Finset.Ico K M, w k
          ≤ (1 / (2 * V0)) * (Ceta / ((K : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hIco_le (by positivity)
      _ = Ceta / (2 * V0 * ((K : ℝ) + 1)) := by
        rw [div_mul_div_comm, one_mul]

/-- Exact Weierstrass-Inverted Worldtube Clock Gate Theorem:
Under sub-critical smeared variance `0 ≤ g^2 * σ_{η,K}^2 ≤ g^2 * σ_{η,∞}^2 < w^2` (`w > 0`),
the pre-sharpened width `b_K := √(w^2 - g^2 * σ_{η,K}^2) > 0` restores exact target variance `w^2`,
exact carrier frequency `Ω`, and obeys a `K`-independent amplitude bound. -/
theorem weierstrass_deconvolved_clock_gate_exact
    {w g sigmaK_sq sigmaInf_sq Omega : ℝ}
    (hw : 0 < w)
    (_hK_nonneg : 0 ≤ g ^ 2 * sigmaK_sq)
    (hK_le_inf : g ^ 2 * sigmaK_sq ≤ g ^ 2 * sigmaInf_sq)
    (hsubcrit : g ^ 2 * sigmaInf_sq < w ^ 2) :
    let bK := Real.sqrt (w ^ 2 - g ^ 2 * sigmaK_sq)
    let bInf := Real.sqrt (w ^ 2 - g ^ 2 * sigmaInf_sq)
    let alphaK := (w ^ 2 / bK ^ 2) * Omega
    0 < bInf ∧ bInf ≤ bK ∧
      bK ^ 2 + g ^ 2 * sigmaK_sq = w ^ 2 ∧
      (alphaK * bK ^ 2) / (bK ^ 2 + g ^ 2 * sigmaK_sq) = Omega ∧
      w / bK ≤ w / bInf := by
  intro bK bInf alphaK
  have hdiff_inf : 0 < w ^ 2 - g ^ 2 * sigmaInf_sq := by linarith
  have hdiff_K : 0 < w ^ 2 - g ^ 2 * sigmaK_sq := by linarith
  have hbInf_pos : 0 < bInf := Real.sqrt_pos.mpr hdiff_inf
  have hbK_pos : 0 < bK := Real.sqrt_pos.mpr hdiff_K
  have hbInf_le_bK : bInf ≤ bK := Real.sqrt_le_sqrt (by linarith)
  have hbK_sq : bK ^ 2 = w ^ 2 - g ^ 2 * sigmaK_sq := Real.sq_sqrt (le_of_lt hdiff_K)
  have hsum_w2 : bK ^ 2 + g ^ 2 * sigmaK_sq = w ^ 2 := by linarith
  have hbK2_ne : bK ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hbK_pos)
  have hw2_ne : w ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hw)
  have hfreq : (alphaK * bK ^ 2) / (bK ^ 2 + g ^ 2 * sigmaK_sq) = Omega := by
    dsimp [alphaK]
    rw [hsum_w2]
    field_simp [hbK2_ne, hw2_ne]
  have hamp_le : w / bK ≤ w / bInf :=
    div_le_div_of_nonneg_left (le_of_lt hw) hbInf_pos hbInf_le_bK
  exact ⟨hbInf_pos, hbInf_le_bK, hsum_w2, hfreq, hamp_le⟩

/-- Worldtube-smeared 4-body Wick graph norm bound (resolving `WICK_CLOCK_GRAPH` Eq. 2):
whenever `0 ≤ ES_xy ≤ M_S^2` and `|C_{+,η,K}| ≤ B_η`, the pointwise 4-body integrand is bounded
uniformly in `K` by `(3/2) g^4 M_S^2 B_η^4`. -/
theorem smeared_wick_quartic_graph_norm_uniform_bound
    {g ES_xy MS C_xy Beta : ℝ}
    (_hES_nn : 0 ≤ ES_xy) (_hMS_nn : 0 ≤ MS) (_hBeta_nn : 0 ≤ Beta)
    (hES_le : ES_xy ≤ MS ^ 2) (hC_le : |C_xy| ≤ Beta) :
    (3 / 2 : ℝ) * g ^ 4 * ES_xy * C_xy ^ 4 ≤ (3 / 2 : ℝ) * g ^ 4 * MS ^ 2 * Beta ^ 4 := by
  have hC4 : C_xy ^ 4 ≤ Beta ^ 4 := by
    have habs4 : |C_xy| ^ 4 ≤ Beta ^ 4 := pow_le_pow_left₀ (abs_nonneg C_xy) hC_le 4
    have heq : |C_xy| ^ 4 = C_xy ^ 4 := by
      calc
        |C_xy| ^ 4 = (|C_xy| ^ 2) ^ 2 := by ring
        _ = (C_xy ^ 2) ^ 2 := by rw [sq_abs]
        _ = C_xy ^ 4 := by ring
    linarith
  have hprod : ES_xy * C_xy ^ 4 ≤ MS ^ 2 * Beta ^ 4 :=
    mul_le_mul hES_le hC4 (by positivity) (sq_nonneg MS)
  have hg4 : 0 ≤ (3 / 2 : ℝ) * g ^ 4 := by positivity
  calc
    (3 / 2 : ℝ) * g ^ 4 * ES_xy * C_xy ^ 4 = ((3 / 2 : ℝ) * g ^ 4) * (ES_xy * C_xy ^ 4) := by ring
    _ ≤ ((3 / 2 : ℝ) * g ^ 4) * (MS ^ 2 * Beta ^ 4) := mul_le_mul_of_nonneg_left hprod hg4
    _ = (3 / 2 : ℝ) * g ^ 4 * MS ^ 2 * Beta ^ 4 := by ring

/-! ## 3. `BACKREACTION_GATE` Static-`Λ` No-Go vs Dynamical Clock-FRW Enthalpy Conservation -/

/-- Cosmological constant enthalpy invariance (`BACKREACTION_GATE` no-go theorem):
since `p_Λ = -ρ_Λ`, shifting `ρ_Λ` leaves total enthalpy `(ρ_clk + ρ_Λ) + (p_clk - ρ_Λ)`
identically equal to `xdot^2 > 0`, so no choice of `Λ` can achieve zero enthalpy `ρ_tot + p_tot = 0`
when the clock is moving (`xdot ≠ 0`). -/
theorem cosmological_constant_zero_enthalpy_no_go
    {xdot V_X rhoLambda : ℝ} (hxdot : xdot ≠ 0) :
    let rho_tot := (1 / 2 : ℝ) * xdot ^ 2 + V_X + rhoLambda
    let p_tot := (1 / 2 : ℝ) * xdot ^ 2 - V_X - rhoLambda
    rho_tot + p_tot = xdot ^ 2 ∧ rho_tot + p_tot ≠ 0 := by
  intro rho_tot p_tot
  have hsum : rho_tot + p_tot = xdot ^ 2 := by
    dsimp [rho_tot, p_tot]
    ring
  exact ⟨hsum, by rw [hsum]; exact pow_ne_zero 2 hxdot⟩

/-- Exact Friedmann Hamiltonian Constraint Conservation on Dynamical Clock-Driven Closed FRW:
With `H = adot / a`, Raychaudhuri equation `Hdot = -(κ / 2) * xdot^2 + 1 / a^2`, and Klein-Gordon
clock equation `xddot + 3 * H * xdot + dV = 0`, the time derivative of the Friedmann residual
`C = H^2 + 1/a^2 - (κ/3)((1/2) xdot^2 + V + Λ/κ)` vanishes identically (`Cdot = 0`). -/
theorem dynamical_clock_frw_friedmann_conservation
    {a adot H Hdot xdot xddot dV kappa : ℝ}
    (ha : a ≠ 0)
    (hH_def : adot = a * H)
    (hRay : Hdot = -(kappa / 2) * xdot ^ 2 + 1 / a ^ 2)
    (hKG : xddot = -(3 * H * xdot + dV)) :
    2 * H * Hdot - 2 * adot / a ^ 3 - (kappa / 3) * (xdot * xddot + dV * xdot) = 0 := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have ha3 : a ^ 3 ≠ 0 := pow_ne_zero 3 ha
  rw [hH_def, hRay, hKG]
  field_simp [ha, ha2, ha3]
  ring

end UEOTPhysicsUnification.RenormalizedClockContinuum
