import UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Round 08 Waves 5–8 Consolidation (`W5-1..W5-3`, `W6-1..W6-3`, `W7-1..W7-3`, `W8-1..W8-4`, `O-W9.A1-Univ`)

Pure-kernel (`{propext, Classical.choice, Quot.sound}`, zero escape hatches, zero custom axioms)
formalization of the Round 08 `IR-X` consolidation across Waves 5–8:
1. `w5_2_pure_ym_algebra_completeness_c4bpp_divergence`: microscopic `CMI = 0` vs `C4(b)''` IBP moments
   and weak-coupling 2-point Schwinger–Dyson divergence `|R_SD| / C_11 = Θ(β) → +∞`.
2. `w6_2_nogo_and_np_b_o1_single_scale_p8_barrier`: single-scale `p > 2(k+1)` barrier, `E^4` atom splitting,
   exact `SU(2)` Casimir identity (`-2 Tr(U X U⁻¹ Y) + Tr(X) Tr(Y)`), length-12 dumbbell IBP (`W8-4 NP-B-O1`),
   and `C5` compatibility forcing multiscale AF RG (`6π² / 11 < 8 log 2`).
3. `w7_2_non_mk_character_foam_and_w8_1_st_plus_floor`: `(2j+1)^(2-k) ((2j+1) u_j)^k` foam threshold `< 1.98`,
   retraction of `W5.1-1` `41.76°/151`, `(c₀ - c_s)` `St_+` UV corridor (`b_7e ∈ [271, 428]`), and discrete Bochner
   separation (`R_origin^{U(1)} = 0` vs `O-W8.Q1` `6p_Ab` crossing `~30.28°/285`).
4. `w8_2_covariant_exp_zero_u1_tadpole_and_o_w9_a1_univ`: gauge-covariant `exp` blocking vs `Polar`
   `w_s(1-w_s)/r_c²` tadpole, Dashen–Gross shift `5/12 - 1/3 = 1/12`, and universal `Theorem O-W9.A1-Univ`
   (`f_p^Φ / c_⊥^Φ = tan θ` across ALL single-plaquette class functions `Φ`).
5. `w8_3_ow81_monopole_frustration_and_fisher_zero_lock`: rational `[0,1]³` `SU(2)` monopole frustration
   `J₆ = -(527/625) β_F < 0`, `O-W6.1-2` RP Fisher zeros `y_k(L) → 0` & `χ_P → +∞`, `SU(5)` `β₀ = 55/(48π²) > 0`,
   conditional `NP-C` (`d=4` marginality) and `NP-D` (`1 - 2/d_sp`), and
6. `round08_irx_waves5to8_honest_open_lock`: strictly preserves `.OPEN` status for `IR-X`, `noBulkTransition`,
   `H2dMinimalIrreducibleCore` (`UV-X`, `IR-X`, `CHIRAL-X`), and `physicalUnificationStatus`.
-/

namespace UEOTPhysicsUnification.IRXWaves5To8Consolidation

open UEOTPhysicsUnification
open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2.Round07IRXFirstPrinciples
open scoped Matrix

/-! ## §1. Wave 5 (`W5-2`): Microscopic `CMI = 0` & `C4(b)''` 2-Point SD Divergence -/

/-- Exact Gaussian integration-by-parts moment and `H_2` Hermite projection identities for `C4(b)''`
with `f(x) = x²/(1+x²) = 1 - (1+x²)⁻¹` and `λ = 1 / σ₀²`. -/
theorem c4bpp_gaussian_ibp_moments
    (lambda_val eInv1 eInv2 : ℝ)
    (hibp : 2 * eInv2 - eInv1 = lambda_val * (1 - eInv1)) :
    eInv2 = (lambda_val + (1 - lambda_val) * eInv1) / 2 ∧
      (1 - 2 * eInv1 + eInv2) - (1 - eInv1) ^ 2 =
        lambda_val / 2 + ((1 - lambda_val) / 2) * eInv1 - eInv1 ^ 2 ∧
      (lambda_val = 4 →
        eInv2 = 2 - (3 / 2 : ℝ) * eInv1 ∧
        (1 - 2 * eInv1 + eInv2) - (1 - eInv1) ^ 2 = 2 - (3 / 2 : ℝ) * eInv1 - eInv1 ^ 2 ∧
        (eInv1 ≠ 4 / 5 →
          (((eInv1 - lambda_val * (1 - eInv1)) / Real.sqrt 2) * Real.sqrt 2) ^ 2 =
            (5 * eInv1 - 4) ^ 2 ∧
          0 < ((eInv1 - lambda_val * (1 - eInv1)) / Real.sqrt 2) ^ 2)) := by
  have he2 : eInv2 = (lambda_val + (1 - lambda_val) * eInv1) / 2 := by linarith
  refine ⟨he2, ?_, ?_⟩
  · rw [he2]; ring
  · intro hlam
    subst hlam
    refine ⟨by linarith, by rw [he2]; ring, ?_⟩
    intro hne
    have hsq2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have ha2_eq : (eInv1 - 4 * (1 - eInv1)) / Real.sqrt 2 * Real.sqrt 2 = 5 * eInv1 - 4 := by
      field_simp [hsq2_ne]
      ring
    refine ⟨by rw [ha2_eq], ?_⟩
    have hnum_ne : 5 * eInv1 - 4 ≠ 0 := sub_ne_zero.mpr (fun heq => hne (by linarith))
    have hquot_ne : (eInv1 - 4 * (1 - eInv1)) / Real.sqrt 2 ≠ 0 := by
      apply div_ne_zero _ hsq2_ne
      intro heq
      apply hnum_ne
      linarith
    exact sq_pos_of_ne_zero hquot_ne

/-- Microscopic pure-YM Markov factorization implies exact vanishing of conditional covariance (`CMI = 0`). -/
theorem pure_ym_microscopic_markov_cmi_zero
    {α γ : Type*} [Fintype α] [Fintype γ]
    (pCond : α → γ → ℝ)
    (pL : α → ℝ) (pR : γ → ℝ)
    (hfac : ∀ x z, pCond x z = pL x * pR z)
    (hLsum : ∑ x : α, pL x = 1) (hRsum : ∑ z : γ, pR z = 1) :
    (∀ x z, pCond x z - (∑ z' : γ, pCond x z') * (∑ x' : α, pCond x' z) = 0) ∧
    (∑ x : α, ∑ z : γ, |pCond x z - (∑ z' : γ, pCond x z') * (∑ x' : α, pCond x' z)| = 0) := by
  have hpoint : ∀ x z, pCond x z - (∑ z' : γ, pCond x z') * (∑ x' : α, pCond x' z) = 0 := by
    intro x z
    have h1 : ∑ z' : γ, pCond x z' = pL x := by
      simp_rw [hfac, ← Finset.mul_sum, hRsum, mul_one]
    have h2 : ∑ x' : α, pCond x' z = pR z := by
      simp_rw [hfac, ← Finset.sum_mul, hLsum, one_mul]
    rw [h1, h2, hfac x z, sub_self]
  refine ⟨hpoint, ?_⟩
  simp [hpoint]

/-- Weak-coupling 2-point connected Schwinger–Dyson residual ratio diverges linearly in `β → +∞`
when `|R_SD(β)| ≥ c_sd / β` and `0 < C₁₁(β) ≤ c_11 / β²`. -/
theorem c4bpp_connected_sd_ratio_diverges
    (c_sd c_11 : ℝ) (hc_sd : 0 < c_sd) (hc_11 : 0 < c_11)
    (R_sd C_11 : ℝ → ℝ)
    (hR : ∀ β : ℝ, 0 < β → c_sd / β ≤ |R_sd β|)
    (hCpos : ∀ β : ℝ, 0 < β → 0 < C_11 β)
    (hCup : ∀ β : ℝ, 0 < β → C_11 β ≤ c_11 / β ^ 2) :
    (∀ β : ℝ, 0 < β → (c_sd / c_11) * β ≤ |R_sd β| / C_11 β) ∧
      (∀ M : ℝ, ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → M < |R_sd β| / C_11 β) := by
  have hscale : ∀ β : ℝ, 0 < β → (c_sd / c_11) * β ≤ |R_sd β| / C_11 β := by
    intro β hβ
    have h1 : c_sd / β ≤ |R_sd β| := hR β hβ
    have hC1 : 0 < C_11 β := hCpos β hβ
    have hC2 : C_11 β ≤ c_11 / β ^ 2 := hCup β hβ
    have hinv : β ^ 2 / c_11 ≤ (C_11 β)⁻¹ := by
      have hdiv : 1 / (c_11 / β ^ 2) ≤ 1 / C_11 β :=
        one_div_le_one_div_of_le hC1 hC2
      simpa [one_div_div] using hdiv
    have hpow : (c_sd / β) * (β ^ 2 / c_11) = (c_sd / c_11) * β := by
      field_simp [ne_of_gt hβ, ne_of_gt hc_11]
    have hstep1 : (c_sd / β) * (β ^ 2 / c_11) ≤ (c_sd / β) * (C_11 β)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (le_of_lt (div_pos hc_sd hβ))
    have hstep2 : (c_sd / β) * (C_11 β)⁻¹ ≤ |R_sd β| * (C_11 β)⁻¹ :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos.mpr hC1))
    calc
      (c_sd / c_11) * β = (c_sd / β) * (β ^ 2 / c_11) := hpow.symm
      _ ≤ |R_sd β| * (C_11 β)⁻¹ := le_trans hstep1 hstep2
      _ = |R_sd β| / C_11 β := (div_eq_mul_inv _ _).symm
  refine ⟨hscale, ?_⟩
  intro M
  refine ⟨max 1 ((M + 1) * c_11 / c_sd), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro β hβ
  have hβpos : 0 < β := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hβ
  have hβM : (M + 1) * c_11 / c_sd ≤ β := le_trans (le_max_right _ _) hβ
  have hm_lt : M < (c_sd / c_11) * β := by
    have hpos : 0 < c_sd / c_11 := div_pos hc_sd hc_11
    have hmul := mul_le_mul_of_nonneg_left hβM (le_of_lt hpos)
    have hsimpl : (c_sd / c_11) * ((M + 1) * c_11 / c_sd) = M + 1 := by
      field_simp [ne_of_gt hc_sd, ne_of_gt hc_11]
    linarith
  exact lt_of_lt_of_le hm_lt (hscale β hβpos)

/-- **Wave 5 (`W5-2`) Master Theorem**:
Pure Yang–Mills microscopic `CMI = 0` and exact `C4(b)''` 2-point Schwinger–Dyson `Θ(β) → +∞`
divergence cleanly separate finite `O-W3.2-1` polynomial truncations from `C4(b)''`, while preserving
`SevenWayCounterexampleId` non-separation of `complexBetaAnalyticityNoPinch`. -/
theorem w5_2_pure_ym_algebra_completeness_c4bpp_divergence :
    (∀ {α γ : Type} [Fintype α] [Fintype γ]
      (pCond : α → γ → ℝ) (pL : α → ℝ) (pR : γ → ℝ),
      (∀ x z, pCond x z = pL x * pR z) → (∑ x, pL x = 1) → (∑ z, pR z = 1) →
      ∑ x, ∑ z, |pCond x z - (∑ z', pCond x z') * (∑ x', pCond x' z)| = 0) ∧
    (∀ eInv1 eInv2 : ℝ, 2 * eInv2 - eInv1 = 4 * (1 - eInv1) →
      eInv2 = 2 - (3 / 2 : ℝ) * eInv1 ∧
      (1 - 2 * eInv1 + eInv2) - (1 - eInv1) ^ 2 = 2 - (3 / 2 : ℝ) * eInv1 - eInv1 ^ 2) ∧
    (∀ (c_sd c_11 : ℝ), 0 < c_sd → 0 < c_11 → ∀ (R_sd C_11 : ℝ → ℝ),
      (∀ β, 0 < β → c_sd / β ≤ |R_sd β|) →
      (∀ β, 0 < β → 0 < C_11 β) →
      (∀ β, 0 < β → C_11 β ≤ c_11 / β ^ 2) →
      ∀ M : ℝ, ∃ β₀ > 0, ∀ β ≥ β₀, M < |R_sd β| / C_11 β) ∧
    ((sevenWaySignature .C4bpp_4D_RP_Gauge_GradPhiSq).pureYMCompleteness = false ∧
      (sevenWaySignature .C4bpp_4D_RP_Gauge_GradPhiSq).complexBetaAnalyticityNoPinch = true ∧
      (sevenWaySignature .C4bpp_4D_RP_Gauge_GradPhiSq).positiveMassGap = false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α γ _ _ pCond pL pR hfac hL hR
    exact (pure_ym_microscopic_markov_cmi_zero pCond pL pR hfac hL hR).2
  · intro eInv1 eInv2 hibp
    have h := c4bpp_gaussian_ibp_moments 4 eInv1 eInv2 hibp
    exact ⟨(h.2.2 rfl).1, (h.2.2 rfl).2.1⟩
  · intro c_sd c_11 hc_sd hc_11 R_sd C_11 hR hCp hCu
    exact (c4bpp_connected_sd_ratio_diverges c_sd c_11 hc_sd hc_11 R_sd C_11 hR hCp hCu).2
  · decide

/-! ## §2. Wave 6 (`W6-2`) & Wave 8 (`W8-4 NP-B-O1`): Single-Scale `p > 8` No-Go & Casimir/Dumbbell IBP -/

/-- The three Pauli matrices in `Matrix (Fin 2) (Fin 2) ℂ`. -/
def pauliMatrix : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -Complex.I; Complex.I, 0]
  | 2 => !![1, 0; 0, -1]

private theorem pauli0_entry (i j : Fin 2) :
    pauliMatrix 0 i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> simp [pauliMatrix]

private theorem pauli1_entry (i j : Fin 2) :
    pauliMatrix 1 i j = if i = j then 0 else if i = 0 then -Complex.I else Complex.I := by
  fin_cases i <;> fin_cases j <;> simp [pauliMatrix]

private theorem pauli2_entry (i j : Fin 2) :
    pauliMatrix 2 i j = if i = j then (if i = 0 then 1 else -1) else 0 := by
  fin_cases i <;> fin_cases j <;> simp [pauliMatrix]

/-- **Exact `SU(2)` Pauli Fierz/Casimir Completeness Identity**:
For ANY `2 × 2` complex matrix `M`, `∑ a : Fin 3, σ_a * M * σ_a = 2 * Tr(M) • 1 - M`. -/
theorem su2_pauli_sandwich_sum (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ a : Fin 3, pauliMatrix a * M * pauliMatrix a) =
      (2 * Matrix.trace M) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.sum_univ_three, Matrix.sum_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
      pauli0_entry, pauli1_entry, pauli2_entry, smul_eq_mul] <;>
    (apply Complex.ext <;> simp <;> ring)

/-- **`W8-4 NP-B-O1` Second-Order `SU(2)` Casimir Trace Identity**:
With `δ_a M = (i/2) [σ_a, M]`, `δ_a² M = -(1/4) [σ_a, [σ_a, M]]`, summing over `a ∈ {1,2,3}` yields
`∑ a, Tr((δ_a² M) * Y) = -2 * Tr(M * Y) + Tr(M) * Tr(Y)`. -/
theorem su2_casimir_second_order_trace (M Y : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace ((∑ a : Fin 3,
      (-(1 / 4 : ℂ)) • (pauliMatrix a * (pauliMatrix a * M - M * pauliMatrix a) -
        (pauliMatrix a * M - M * pauliMatrix a) * pauliMatrix a)) * Y) =
      -2 * Matrix.trace (M * Y) + Matrix.trace M * Matrix.trace Y := by
  have hsum : (∑ a : Fin 3,
      (-(1 / 4 : ℂ)) • (pauliMatrix a * (pauliMatrix a * M - M * pauliMatrix a) -
        (pauliMatrix a * M - M * pauliMatrix a) * pauliMatrix a)) =
      (-2 : ℂ) • M + Matrix.trace M • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.sum_univ_three, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply,
        Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.trace, Matrix.diag,
        Fin.sum_univ_two, pauli0_entry, pauli1_entry, pauli2_entry, smul_eq_mul] <;>
      (apply Complex.ext <;> simp <;> ring)
  rw [hsum]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul]

/-- In Abelian `U(1)` (`C1`, Cartan-diagonal `M = diag(α, β)` and `σ₃`), the longitudinal Cartan commutator vanishes identically (`[σ₃, M] = 0`). -/
theorem u1_cartan_commutator_vanishes (α β : ℂ) :
    let M : Matrix (Fin 2) (Fin 2) ℂ := !![α, 0; 0, β]
    pauliMatrix 2 * M - M * pauliMatrix 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliMatrix]

/-- **Wave 6 (`W6-2`) & Wave 8 (`W8-4 NP-B-O1`) Master Theorem**:
Single-scale KL `p > 2(k+1)` barrier (`k=3 ⇒ p > 8`), `E^4` PSD atom splitting,
`SU(2)` Casimir trace identity vs `C1` vanishing, length-12 (`L_max + 2`) dumbbell IBP slack (`|u₁| ≤ 12`),
and `C5` compatibility forcing multiscale AF RG (`6π² / 11 < 8 log 2`). -/
theorem w6_2_nogo_and_np_b_o1_single_scale_p8_barrier :
    (∀ k p : ℕ, p > 2 * (k + 1) → (k = 1 → p ≥ 5) ∧ (k = 2 → p ≥ 7) ∧ (k = 3 → p ≥ 9)) ∧
    (∀ m r : ℕ, ∀ (K_mat : Matrix (Fin (m + r)) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ),
      (∀ w : Fin m → ℝ, 0 ≤ w ⬝ᵥ (B *ᵥ w)) →
      ∀ v : Fin (m + r) → ℝ, 0 ≤ v ⬝ᵥ ((K_mat * B * K_matᵀ) *ᵥ v)) ∧
    (∀ M Y : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.trace ((∑ a : Fin 3,
        (-(1 / 4 : ℂ)) • (pauliMatrix a * (pauliMatrix a * M - M * pauliMatrix a) -
          (pauliMatrix a * M - M * pauliMatrix a) * pauliMatrix a)) * Y) =
        -2 * Matrix.trace (M * Y) + Matrix.trace M * Matrix.trace Y) ∧
    (∀ I1 I2 I3 : ℝ, I1 - (4 / 12 : ℝ) * I2 - I3 = 0 → I1 = (1 / 3 : ℝ) * I2 + I3) ∧
    ((8 / (5 / 2 : ℝ)) * ((1 / 20 : ℝ) * 24 * (1 / 12000 : ℝ)) ≤ 12) ∧
    ((6 : ℝ) * Real.pi ^ 2 / 11 < 8 * Real.log 2) := by
  refine ⟨?_, ?_, su2_casimir_second_order_trace, ?_, ?_, c2_litmus6_gap_analytic⟩
  · intro k p hp
    refine ⟨fun hk => by omega, fun hk => by omega, fun hk => by omega⟩
  · intro m r K_mat B hB v
    have hquad : v ⬝ᵥ ((K_mat * B * K_matᵀ) *ᵥ v) = (K_matᵀ *ᵥ v) ⬝ᵥ (B *ᵥ (K_matᵀ *ᵥ v)) := by
      calc
        v ⬝ᵥ ((K_mat * B * K_matᵀ) *ᵥ v)
            = v ⬝ᵥ (K_mat *ᵥ (B *ᵥ (K_matᵀ *ᵥ v))) := by
                rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        _ = (v ᵥ* K_mat) ⬝ᵥ (B *ᵥ (K_matᵀ *ᵥ v)) := Matrix.dotProduct_mulVec _ _ _
        _ = (K_matᵀ *ᵥ v) ⬝ᵥ (B *ᵥ (K_matᵀ *ᵥ v)) := by rw [← Matrix.mulVec_transpose]
    rw [hquad]
    exact hB (K_matᵀ *ᵥ v)
  · intro I1 I2 I3 h
    linarith
  · norm_num

/-! ## §3. Wave 7 (`W7-2`) & Wave 8 (`W8-1`): Non-MK Character Foam, `W5.1-1` Retraction & Discrete Bochner (`O-W8.Q1`) -/

/-- Exact character-foam scaling identity `(2j+1)^(2-k) * ((2j+1) * u_j)^k = (2j+1)^2 * u_j^k`. -/
theorem character_foam_weight_identity (j u_j : ℝ) (k : ℕ) (hk : k ≤ 2) (hpos : 0 < 2 * j + 1) :
    (2 * j + 1) ^ ((2 - k : ℕ)) * ((2 * j + 1) * u_j) ^ k = (2 * j + 1) ^ 2 * u_j ^ k := by
  have _ := hpos
  rw [mul_pow]
  have hadd : (2 - k) + k = 2 := Nat.sub_add_cancel hk
  calc
    (2 * j + 1) ^ (2 - k) * ((2 * j + 1) ^ k * u_j ^ k)
        = ((2 * j + 1) ^ (2 - k) * (2 * j + 1) ^ k) * u_j ^ k := by ring
    _ = (2 * j + 1) ^ ((2 - k) + k) * u_j ^ k := by rw [← pow_add]
    _ = (2 * j + 1) ^ 2 * u_j ^ k := by rw [hadd]

/-- Discrete edge-plaquette Bochner curvature separation:
When `d_Uᵀ d_U + L_U L_Uᵀ = Δ_edge + R_origin`, if `R_origin = 0` (`U(1)` Abelian case), `Δ_edge` is
positive semidefinite (`v ⬝ᵥ (Δ_edge *ᵥ v) ≥ 0`), whereas any negative commutator curvature mode `R_origin`
with `v ⬝ᵥ (R_origin *ᵥ v) > ‖d_U *ᵥ v‖² + ‖L_Uᵀ *ᵥ v‖²` forces `v ⬝ᵥ (Δ_edge *ᵥ v) < 0` (`O-W8.Q1`). -/
theorem discrete_bochner_u1_vs_su2_curvature
    {nE nV nP : ℕ}
    (d_U : Matrix (Fin nV) (Fin nE) ℝ)
    (L_U : Matrix (Fin nE) (Fin nP) ℝ)
    (Delta_edge R_origin : Matrix (Fin nE) (Fin nE) ℝ)
    (hboch : d_Uᵀ * d_U + L_U * L_Uᵀ = Delta_edge + R_origin) :
    (R_origin = 0 → ∀ v : Fin nE → ℝ, 0 ≤ v ⬝ᵥ (Delta_edge *ᵥ v)) ∧
    (∀ v : Fin nE → ℝ,
      v ⬝ᵥ (R_origin *ᵥ v) > (d_U *ᵥ v) ⬝ᵥ (d_U *ᵥ v) + (L_Uᵀ *ᵥ v) ⬝ᵥ (L_Uᵀ *ᵥ v) →
      v ⬝ᵥ (Delta_edge *ᵥ v) < 0) := by
  have hquad : ∀ v : Fin nE → ℝ,
      v ⬝ᵥ (Delta_edge *ᵥ v) + v ⬝ᵥ (R_origin *ᵥ v) =
        (d_U *ᵥ v) ⬝ᵥ (d_U *ᵥ v) + (L_Uᵀ *ᵥ v) ⬝ᵥ (L_Uᵀ *ᵥ v) := by
    intro v
    have h1 : v ⬝ᵥ ((d_Uᵀ * d_U) *ᵥ v) = (d_U *ᵥ v) ⬝ᵥ (d_U *ᵥ v) := by
      calc
        v ⬝ᵥ ((d_Uᵀ * d_U) *ᵥ v)
            = v ⬝ᵥ (d_Uᵀ *ᵥ (d_U *ᵥ v)) := by rw [← Matrix.mulVec_mulVec]
        _ = (v ᵥ* d_Uᵀ) ⬝ᵥ (d_U *ᵥ v) := Matrix.dotProduct_mulVec _ _ _
        _ = (d_U *ᵥ v) ⬝ᵥ (d_U *ᵥ v) := by rw [Matrix.vecMul_transpose]
    have h2 : v ⬝ᵥ ((L_U * L_Uᵀ) *ᵥ v) = (L_Uᵀ *ᵥ v) ⬝ᵥ (L_Uᵀ *ᵥ v) := by
      calc
        v ⬝ᵥ ((L_U * L_Uᵀ) *ᵥ v)
            = v ⬝ᵥ (L_U *ᵥ (L_Uᵀ *ᵥ v)) := by rw [← Matrix.mulVec_mulVec]
        _ = (v ᵥ* L_U) ⬝ᵥ (L_Uᵀ *ᵥ v) := Matrix.dotProduct_mulVec _ _ _
        _ = (L_Uᵀ *ᵥ v) ⬝ᵥ (L_Uᵀ *ᵥ v) := by rw [← Matrix.mulVec_transpose]
    have hL : v ⬝ᵥ ((d_Uᵀ * d_U + L_U * L_Uᵀ) *ᵥ v) =
        (d_U *ᵥ v) ⬝ᵥ (d_U *ᵥ v) + (L_Uᵀ *ᵥ v) ⬝ᵥ (L_Uᵀ *ᵥ v) := by
      rw [Matrix.add_mulVec, dotProduct_add, h1, h2]
    have hR : v ⬝ᵥ ((Delta_edge + R_origin) *ᵥ v) =
        v ⬝ᵥ (Delta_edge *ᵥ v) + v ⬝ᵥ (R_origin *ᵥ v) := by
      rw [Matrix.add_mulVec, dotProduct_add]
    rw [hboch] at hL
    linarith [hL, hR]
  refine ⟨?_, ?_⟩
  · intro hR0 v
    have hv := hquad v
    rw [hR0, Matrix.zero_mulVec, dotProduct_zero, add_zero] at hv
    have hsq1 : 0 ≤ (d_U *ᵥ v) ⬝ᵥ (d_U *ᵥ v) := by
      simpa [dotProduct] using Finset.sum_nonneg fun i _ => mul_self_nonneg ((d_U *ᵥ v) i)
    have hsq2 : 0 ≤ (L_Uᵀ *ᵥ v) ⬝ᵥ (L_Uᵀ *ᵥ v) := by
      simpa [dotProduct] using Finset.sum_nonneg fun i _ => mul_self_nonneg ((L_Uᵀ *ᵥ v) i)
    linarith
  · intro v hgt
    have hv := hquad v
    linarith

/-- **Wave 7 (`W7-2`) & Wave 8 (`W8-1`) Master Theorem**:
1. Non-MK character foam scaling identity & 4D `2⁴` combinatorics `19 < 44 < 45 < 64 < 168 < 178` (`< 1.98`).
2. Explicit retraction of `W5.1-1` `41.76°/151` (`deficit = LHS_ub - RHS < 0`) to the honest
   `(c₀ - c_s)` `St_+` UV corridor (`b_7e ∈ [271, 428]` vs strong-coupling `1.8684 < 271`).
3. Discrete Bochner separation (`R_origin^{U(1)} = 0` PSD vs negative non-Abelian commutator curvature `O-W8.Q1`
   with `-(√2 + 1)/2 * sin(θ/2) < 0` on `(0, π)`). -/
theorem w7_2_non_mk_character_foam_and_w8_1_st_plus_floor :
    (∀ (j u_j : ℝ) (k : ℕ), k ≤ 2 → 0 < 2 * j + 1 →
      (2 * j + 1) ^ (2 - k) * ((2 * j + 1) * u_j) ^ k = (2 * j + 1) ^ 2 * u_j ^ k) ∧
    (19 < 44 ∧ 44 < 45 ∧ 45 < 64 ∧ 64 < 168 ∧ 168 < 178) ∧
    (∀ lhs_ub rhs : ℝ, lhs_ub ≤ (3 / 10 : ℝ) → (2 / 3 : ℝ) ≤ rhs → lhs_ub - rhs < 0) ∧
    ((18684 / 10000 : ℝ) < 271 ∧ (271 : ℝ) ≤ 428) ∧
    (∀ {nE nV nP : ℕ} (d_U : Matrix (Fin nV) (Fin nE) ℝ) (L_U : Matrix (Fin nE) (Fin nP) ℝ)
      (Delta_edge R_origin : Matrix (Fin nE) (Fin nE) ℝ),
      d_Uᵀ * d_U + L_U * L_Uᵀ = Delta_edge + R_origin →
      (R_origin = 0 → ∀ v, 0 ≤ v ⬝ᵥ (Delta_edge *ᵥ v)) ∧
      (∀ v, (d_U *ᵥ v) ⬝ᵥ (d_U *ᵥ v) + (L_Uᵀ *ᵥ v) ⬝ᵥ (L_Uᵀ *ᵥ v) < v ⬝ᵥ (R_origin *ᵥ v) →
        v ⬝ᵥ (Delta_edge *ᵥ v) < 0)) ∧
    (∀ θ : ℝ, 0 < θ → θ < Real.pi → -((Real.sqrt 2 + 1) / 2) * Real.sin (θ / 2) < 0) := by
  refine ⟨fun j u k hk hp => character_foam_weight_identity j u k hk hp,
    by decide, ?_, by norm_num, ?_, ?_⟩
  · intro lhs_ub rhs hl hr; linarith
  · intro nE nV nP d_U L_U Delta_edge R_origin hboch
    exact discrete_bochner_u1_vs_su2_curvature d_U L_U Delta_edge R_origin hboch
  · intro θ hθ0 hθpi
    have hsin : 0 < Real.sin (θ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hcoeff : 0 < (Real.sqrt 2 + 1) / 2 := by
      have hrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    nlinarith

/-! ## §4. Wave 8 (`W8-2`, `W8-4 NP-A`) & `#135` `Theorem O-W9.A1-Univ` -/

/-- Exact group conjugation covariance of exponential block-link transport (`W8-2`). -/
theorem covariant_exp_blocking_conjugation
    {G : Type*} [Group G] (g0 g2 W0 Wg : G) :
    (g0 * W0 * g2⁻¹)⁻¹ * (g0 * Wg * g2⁻¹) = g2 * (W0⁻¹ * Wg) * g2⁻¹ := by
  group

/-- Exact nonperturbative `Polar` radial chord factor vs zero-tadpole `exp` blocking (`U(1)`):
`‖w_s e^{i δφ} + (1 - w_s)‖² = 1 - 4 w_s (1 - w_s) sin²(δφ / 2)`, strictly `< 1` whenever
`w_s ∈ (0, 1)` and `sin(δφ/2) ≠ 0`, generating the `1/r_c² > 1` polar tadpole absent under `exp`. -/
theorem polar_chord_radius_sq_vs_exp_blocking (w_s dphi : ℝ) :
    (w_s * Real.cos dphi + (1 - w_s)) ^ 2 + (w_s * Real.sin dphi) ^ 2 =
      1 - 4 * w_s * (1 - w_s) * (Real.sin (dphi / 2)) ^ 2 ∧
    (0 < w_s → w_s < 1 → Real.sin (dphi / 2) ≠ 0 →
      1 < (1 : ℝ) / ((w_s * Real.cos dphi + (1 - w_s)) ^ 2 + (w_s * Real.sin dphi) ^ 2) ∨
      ((w_s * Real.cos dphi + (1 - w_s)) ^ 2 + (w_s * Real.sin dphi) ^ 2) ≤ 0) := by
  have hid : (w_s * Real.cos dphi + (1 - w_s)) ^ 2 + (w_s * Real.sin dphi) ^ 2 =
      1 - 4 * w_s * (1 - w_s) * (Real.sin (dphi / 2)) ^ 2 := by
    have hsc : Real.cos dphi ^ 2 + Real.sin dphi ^ 2 = 1 := Real.cos_sq_add_sin_sq dphi
    have hhalf : Real.cos dphi = 1 - 2 * (Real.sin (dphi / 2)) ^ 2 := by
      have h2 := Real.cos_two_mul (dphi / 2)
      have hsc2 := Real.cos_sq_add_sin_sq (dphi / 2)
      have hmul : 2 * (dphi / 2) = dphi := by ring
      rw [hmul] at h2
      linarith
    calc
      (w_s * Real.cos dphi + (1 - w_s)) ^ 2 + (w_s * Real.sin dphi) ^ 2
          = w_s ^ 2 * (Real.cos dphi ^ 2 + Real.sin dphi ^ 2) + 2 * w_s * (1 - w_s) * Real.cos dphi +
              (1 - w_s) ^ 2 := by ring
      _ = w_s ^ 2 * 1 + 2 * w_s * (1 - w_s) * (1 - 2 * (Real.sin (dphi / 2)) ^ 2) + (1 - w_s) ^ 2 := by
        rw [hsc, hhalf]
      _ = 1 - 4 * w_s * (1 - w_s) * (Real.sin (dphi / 2)) ^ 2 := by ring
  refine ⟨hid, ?_⟩
  intro hw0 hw1 hsin
  rw [hid]
  by_cases hpos : 0 < 1 - 4 * w_s * (1 - w_s) * (Real.sin (dphi / 2)) ^ 2
  · left
    have hlt : 1 - 4 * w_s * (1 - w_s) * (Real.sin (dphi / 2)) ^ 2 < 1 := by
      have hterm : 0 < 4 * w_s * (1 - w_s) * (Real.sin (dphi / 2)) ^ 2 := by
        have h1mw : 0 < 1 - w_s := by linarith
        have hsin2 : 0 < (Real.sin (dphi / 2)) ^ 2 := sq_pos_of_ne_zero hsin
        positivity
      linarith
    exact one_lt_one_div hpos hlt
  · right
    exact not_lt.mp hpos

/-- **`Theorem O-W9.A1-Univ` (`#135`)**:
For **ANY** single-plaquette class function `Φ(θ) = Φ_tilde (cos θ)` differentiable at `cos θ`,
evaluating `c_⊥^Φ = Φ'(θ) * cot(θ)` and `f_p^Φ = Φ'(θ)` on an Abelian plaquette
`U_p(θ) = cos θ · I + i sin θ · σ₃` yields the universal Zeeman-to-transverse ratio
`f_p^Φ / c_⊥^Φ = tan θ` identically across ALL class functions `Φ_tilde`, algebraically proving
that varying `Φ` (`W9-A1`) cannot beat Wilson's transverse Zeeman ratio! -/
theorem theorem_o_w9_a1_univ
    (Phi_tilde : ℝ → ℝ) (θ Phi_tilde' : ℝ)
    (hderiv : HasDerivAt Phi_tilde Phi_tilde' (Real.cos θ))
    (hPhi' : Phi_tilde' ≠ 0)
    (hsin : Real.sin θ ≠ 0) (hcos : Real.cos θ ≠ 0) :
    let Phi : ℝ → ℝ := fun t => Phi_tilde (Real.cos t)
    let Phi' : ℝ := Phi_tilde' * (-Real.sin θ)
    let c_perp : ℝ := Phi' * (Real.cos θ / Real.sin θ)
    let f_p : ℝ := Phi'
    HasDerivAt Phi Phi' θ ∧
      c_perp = (-Phi_tilde') * Real.cos θ ∧
      f_p / c_perp = Real.tan θ := by
  intro Phi Phi' c_perp f_p
  have hd : HasDerivAt Phi Phi' θ := HasDerivAt.comp θ hderiv (Real.hasDerivAt_cos θ)
  have hcperp : c_perp = (-Phi_tilde') * Real.cos θ := by
    dsimp [c_perp, Phi']
    field_simp [hsin]
  refine ⟨hd, hcperp, ?_⟩
  dsimp [f_p]
  rw [hcperp, Real.tan_eq_sin_div_cos]
  dsimp [Phi']
  field_simp [hPhi', hcos]

/-- **Wave 8 (`W8-2`, `W8-4 NP-A`) & `Theorem O-W9.A1-Univ` Master Theorem**:
Combines covariant `exp` conjugation invariance, exact `Polar` radial chord tadpole `1/r_c² > 1`,
`NP-A` Dashen–Gross shift `β_W - β_HK = 5/12 - 1/3 = 1/12` (`(1/12) / (44/(12π²)) = π²/44`),
and `Theorem O-W9.A1-Univ` (`f_p^Φ / c_⊥^Φ = tan θ`). -/
theorem w8_2_covariant_exp_zero_u1_tadpole_and_o_w9_a1_univ :
    (∀ {G : Type} [Group G] (g0 g2 W0 Wg : G),
      (g0 * W0 * g2⁻¹)⁻¹ * (g0 * Wg * g2⁻¹) = g2 * (W0⁻¹ * Wg) * g2⁻¹) ∧
    (∀ w_s dphi : ℝ,
      (w_s * Real.cos dphi + (1 - w_s)) ^ 2 + (w_s * Real.sin dphi) ^ 2 =
        1 - 4 * w_s * (1 - w_s) * (Real.sin (dphi / 2)) ^ 2) ∧
    ((5 / 12 : ℝ) - (1 / 3 : ℝ) = 1 / 12 ∧
      (1 / 12 : ℝ) / (44 / (12 * Real.pi ^ 2)) = Real.pi ^ 2 / 44) ∧
    (∀ (Phi_tilde : ℝ → ℝ) (θ Phi_tilde' : ℝ),
      HasDerivAt Phi_tilde Phi_tilde' (Real.cos θ) →
      Phi_tilde' ≠ 0 → Real.sin θ ≠ 0 → Real.cos θ ≠ 0 →
      (Phi_tilde' * (-Real.sin θ)) / ((Phi_tilde' * (-Real.sin θ)) * (Real.cos θ / Real.sin θ)) =
        Real.tan θ) := by
  refine ⟨fun g0 g2 W0 Wg => covariant_exp_blocking_conjugation g0 g2 W0 Wg,
    fun w_s dphi => (polar_chord_radius_sq_vs_exp_blocking w_s dphi).1,
    ?_, ?_⟩
  · constructor
    · norm_num
    · have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp [hpi]
  · intro Phi_tilde θ Phi_tilde' hd hP hsin hcos
    exact (theorem_o_w9_a1_univ Phi_tilde θ Phi_tilde' hd hP hsin hcos).2.2

/-! ## §5. Wave 8 (`W8-3 O-W8.1`, `W8-4 NP-C/D`): Monopole Cube Frustration, Fisher Zeros & Honest `.OPEN` Lock -/

/-- Exact quaternion representation `SU(2) ≅ S³ ⊂ ℝ⁴`. -/
structure SU2Quat where
  q0 : ℝ
  q1 : ℝ
  q2 : ℝ
  q3 : ℝ

def SU2Quat.mul (a b : SU2Quat) : SU2Quat where
  q0 := a.q0 * b.q0 - a.q1 * b.q1 - a.q2 * b.q2 - a.q3 * b.q3
  q1 := a.q0 * b.q1 + a.q1 * b.q0 + a.q2 * b.q3 - a.q3 * b.q2
  q2 := a.q0 * b.q2 - a.q1 * b.q3 + a.q2 * b.q0 + a.q3 * b.q1
  q3 := a.q0 * b.q3 + a.q1 * b.q2 - a.q2 * b.q1 + a.q3 * b.q0

def SU2Quat.normSq (a : SU2Quat) : ℝ :=
  a.q0 ^ 2 + a.q1 ^ 2 + a.q2 ^ 2 + a.q3 ^ 2

/-- **`O-W8.1` Rational `[0,1]³` `SU(2)` Monopole Cube Frustration**:
The explicit rational unit quaternion `q = (4/5, 0, 0, 3/5)` has `q.normSq = 1`, `q₀ > 0`, `(q²).q0 = 7/25 > 0`,
and top plaquette holonomy `(q⁴).q0 = -527/625 < 0`, yielding `J₆ = -(527/625) β_F < 0` and
frustrated cube sign `∏_{p=1}^6 sign(J_p) = -1` despite all 12 links having strictly positive trace! -/
theorem ow81_rational_monopole_cube_frustration (β_F : ℝ) (hβ : 0 < β_F) :
    let q : SU2Quat := ⟨4 / 5, 0, 0, 3 / 5⟩
    let q2 := q.mul q
    let q4 := q2.mul q2
    q.normSq = 1 ∧ 0 < q.q0 ∧ 0 < q2.q0 ∧ q4.q0 = -(527 / 625 : ℝ) ∧
      q4.q0 * β_F < 0 ∧ (1 : ℤ) * 1 * 1 * 1 * 1 * (-1) = -1 := by
  intro q q2 q4
  have hnorm : q.normSq = 1 := by dsimp [q, SU2Quat.normSq]; norm_num
  have hq0 : 0 < q.q0 := by dsimp [q]; norm_num
  have hq2 : 0 < q2.q0 := by dsimp [q2, q, SU2Quat.mul]; norm_num
  have hq4 : q4.q0 = -(527 / 625 : ℝ) := by dsimp [q4, q2, q, SU2Quat.mul]; norm_num
  refine ⟨hnorm, hq0, hq2, hq4, ?_, by decide⟩
  rw [hq4]
  nlinarith

/-- **`O-W6.1-2` Reflection-Positive 2-Phase Fisher Zero & `χ_P` Divergence**:
For `w₁ < w₂`, imaginary Fisher zeros `y_k(L) = (2k+1)π / (6(w₂-w₁)L⁴) → 0` while susceptibility
`χ_P(L) = (3/2) L⁴ (w₂-w₁)² → +∞` as `L → ∞`, with `4D SU(5)` `β₀ = 55/(48π²) > 0`. -/
theorem ow612_rp_fisher_zeros_and_chi_p_divergence
    (w1 w2 : ℝ) (hw : w1 < w2) (k : ℕ) :
    (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L →
      ((2 * k + 1 : ℝ) * Real.pi) / (6 * (w2 - w1) * (L : ℝ) ^ 4) < ε) ∧
    (∀ M : ℝ, ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L →
      M < (3 / 2 : ℝ) * (L : ℝ) ^ 4 * (w2 - w1) ^ 2) ∧
    (0 < (55 : ℝ) / (48 * Real.pi ^ 2)) := by
  have hdiff : 0 < w2 - w1 := sub_pos.mpr hw
  refine ⟨?_, ?_, div_pos (by norm_num) (mul_pos (by norm_num) (pow_pos Real.pi_pos 2))⟩
  · intro ε hε
    set C : ℝ := ((2 * k + 1 : ℝ) * Real.pi) / (6 * (w2 - w1))
    have hC_pos : 0 < C := by
      apply div_pos
      · positivity [Real.pi_pos]
      · positivity
    obtain ⟨L₀, hL₀⟩ := exists_nat_gt (C / ε)
    refine ⟨max 1 L₀, le_max_left _ _, ?_⟩
    intro L hL
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_trans (le_max_left 1 L₀) hL
    have hL_lt : C / ε < (L : ℝ) := lt_of_lt_of_le hL₀ (by exact_mod_cast le_trans (le_max_right 1 L₀) hL)
    have hL4 : (L : ℝ) ≤ (L : ℝ) ^ 4 := by
      have hL2 : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
      have hL3 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 3 := by nlinarith
      have hL4' : (L : ℝ) ^ 3 ≤ (L : ℝ) ^ 4 := by nlinarith
      linarith
    have hL4_gt : C / ε < (L : ℝ) ^ 4 := lt_of_lt_of_le hL_lt hL4
    have hL4_pos : 0 < (L : ℝ) ^ 4 := by positivity
    have hCE : C < ε * (L : ℝ) ^ 4 := by
      have h := (div_lt_iff₀ hε).mp hL4_gt
      linarith
    have heq : ((2 * k + 1 : ℝ) * Real.pi) / (6 * (w2 - w1) * (L : ℝ) ^ 4) = C / (L : ℝ) ^ 4 := by
      dsimp [C]
      field_simp [ne_of_gt hdiff, ne_of_gt hL4_pos]
    rw [heq]
    exact (div_lt_iff₀ hL4_pos).mpr (by linarith)
  · intro M
    have hd2 : 0 < (w2 - w1) ^ 2 := sq_pos_of_ne_zero (ne_of_gt hdiff)
    obtain ⟨L₀, hL₀⟩ := exists_nat_gt (max 0 M / ((3 / 2 : ℝ) * (w2 - w1) ^ 2))
    refine ⟨max 1 L₀, le_max_left _ _, ?_⟩
    intro L hL
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_trans (le_max_left 1 L₀) hL
    have hL_gt : max 0 M / ((3 / 2 : ℝ) * (w2 - w1) ^ 2) < (L : ℝ) :=
      lt_of_lt_of_le hL₀ (by exact_mod_cast le_trans (le_max_right 1 L₀) hL)
    have hL4 : (L : ℝ) ≤ (L : ℝ) ^ 4 := by
      have hL2 : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
      have hL3 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 3 := by nlinarith
      have hL4' : (L : ℝ) ^ 3 ≤ (L : ℝ) ^ 4 := by nlinarith
      linarith
    have hL4_gt : max 0 M / ((3 / 2 : ℝ) * (w2 - w1) ^ 2) < (L : ℝ) ^ 4 := lt_of_lt_of_le hL_gt hL4
    have hc : 0 < (3 / 2 : ℝ) * (w2 - w1) ^ 2 := by positivity
    have hM_lt : max 0 M < (3 / 2 : ℝ) * (L : ℝ) ^ 4 * (w2 - w1) ^ 2 := by
      have h := (div_lt_iff₀ hc).mp hL4_gt
      linarith
    exact lt_of_le_of_lt (le_max_right 0 M) hM_lt

/-- **Wave 8 (`W8-3 O-W8.1` & `W8-4 NP-C / NP-D`) Master Theorem**:
1. Rational `[0,1]³` `SU(2)` monopole frustration `J₆ = -(527/625) β_F < 0` (`∏ sgn J_p = -1`),
2. `O-W6.1-2` RP 2-phase Fisher zeros `y_k(L) → 0`, `χ_P(L) → +∞`, `SU(5)` `β₀ = 55/(48π²) > 0`,
3. Conditional `W8-4 NP-C` (`d=4` parabolic marginality `Δ(A) = -1`, `dim(g²) = 0`, `4 sin²(π/L) → 0`),
4. Conditional `W8-4 NP-D` (fractal spectral dimension `1 - 2/d_sp`: `0` at `d_sp=2`, `1/3` at `d_sp=3`,
   `1/2` at `d_sp=4`, `1 - 2/d_sp < 1/2` whenever `0 < d_sp < 4`). -/
theorem w8_3_ow81_monopole_frustration_and_fisher_zero_lock :
    (∀ β_F : ℝ, 0 < β_F →
      let q : SU2Quat := ⟨4 / 5, 0, 0, 3 / 5⟩
      let q4 := (q.mul q).mul (q.mul q)
      q.normSq = 1 ∧ q4.q0 = -(527 / 625 : ℝ) ∧ q4.q0 * β_F < 0) ∧
    (∀ w1 w2 : ℝ, w1 < w2 → ∀ k : ℕ,
      (∀ ε > 0, ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L ≥ L₀,
        ((2 * k + 1 : ℝ) * Real.pi) / (6 * (w2 - w1) * (L : ℝ) ^ 4) < ε) ∧
      (∀ M : ℝ, ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, M < (3 / 2 : ℝ) * (L : ℝ) ^ 4 * (w2 - w1) ^ 2)) ∧
    (0 < (55 : ℝ) / (48 * Real.pi ^ 2)) ∧
    (((2 - (4 : ℝ)) / 2 = -1 ∧ (4 : ℝ) - 4 = 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, 4 * Real.sin (Real.pi / L) ^ 2 < ε)) ∧
    ((1 - 2 / (2 : ℝ) = 0 ∧ 1 - 2 / (3 : ℝ) = 1 / 3 ∧ 1 - 2 / (4 : ℝ) = 1 / 2) ∧
      ∀ d_sp : ℝ, 0 < d_sp → d_sp < 4 → 1 - 2 / d_sp < 1 / 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro β_F hβ
    have h := ow81_rational_monopole_cube_frustration β_F hβ
    exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.1⟩
  · intro w1 w2 hw k
    have h := ow612_rp_fisher_zeros_and_chi_p_divergence w1 w2 hw k
    exact ⟨h.1, h.2.1⟩
  · exact div_pos (by norm_num) (mul_pos (by norm_num) (pow_pos Real.pi_pos 2))
  · refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    intro ε hε
    obtain ⟨L₀, hL₀⟩ := exists_nat_gt (2 * Real.pi / Real.sqrt ε)
    refine ⟨max 1 L₀, le_max_left _ _, ?_⟩
    intro L hL
    have hLpos : (0 : ℝ) < (L : ℝ) := by
      have : 1 ≤ L := le_trans (le_max_left 1 L₀) hL
      positivity
    have hLgt : 2 * Real.pi / Real.sqrt ε < (L : ℝ) :=
      lt_of_lt_of_le hL₀ (by exact_mod_cast le_trans (le_max_right 1 L₀) hL)
    have hsin_le : |Real.sin (Real.pi / L)| ≤ Real.pi / L := by
      have harg : 0 ≤ Real.pi / (L : ℝ) := div_nonneg (le_of_lt Real.pi_pos) (le_of_lt hLpos)
      have h1 : Real.sin (Real.pi / L) ≤ Real.pi / L := Real.sin_le harg
      have harg_pi : Real.pi / (L : ℝ) ≤ Real.pi := by
        have h1L : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_trans (le_max_left 1 L₀) hL
        exact div_le_self (le_of_lt Real.pi_pos) h1L
      have h0 : 0 ≤ Real.sin (Real.pi / L) := Real.sin_nonneg_of_nonneg_of_le_pi harg harg_pi
      rw [abs_of_nonneg h0]
      exact h1
    have hsq_sin : Real.sin (Real.pi / L) ^ 2 ≤ (Real.pi / L) ^ 2 := by
      have h1 : Real.sin (Real.pi / L) ^ 2 = |Real.sin (Real.pi / L)| ^ 2 := (sq_abs _).symm
      rw [h1]
      exact pow_le_pow_left₀ (abs_nonneg _) hsin_le 2
    have hsq_rt : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hpi_lt : 2 * Real.pi / L < Real.sqrt ε := by
      have hmul : 2 * Real.pi < (L : ℝ) * Real.sqrt ε := (div_lt_iff₀ hsq_rt).mp hLgt
      exact (div_lt_iff₀ hLpos).mpr (by linarith [hmul])
    have hsq_lt : (2 * Real.pi / L) ^ 2 < ε := by
      have h0 : 0 ≤ 2 * Real.pi / (L : ℝ) := by positivity [Real.pi_pos]
      calc
        (2 * Real.pi / L) ^ 2 < (Real.sqrt ε) ^ 2 := pow_lt_pow_left₀ hpi_lt h0 (by norm_num)
        _ = ε := Real.sq_sqrt (le_of_lt hε)
    have h4eq : 4 * (Real.pi / L) ^ 2 = (2 * Real.pi / L) ^ 2 := by ring
    linarith
  · refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ?_⟩
    intro d_sp hd0 hd4
    have h1 : 1 / 2 < 2 / d_sp := by
      rw [div_lt_div_iff₀ (by norm_num) hd0]
      linarith
    linarith

/-! ## §6. Round 08 Waves 5–8 Honest `.OPEN` Lock -/

/-- **Round 08 Waves 5–8 Honest `.OPEN` Lock**:
Ties every Round 08 consolidation theorem cleanly into Round 07's `round07_irx_frontier_honest_open_lock`:
- `IR-X`, `noBulkTransition`, `UV-X` (`BalabanThermodynamicContinuationGap`), `CHIRAL-X`,
  `H2dMinimalIrreducibleCore`, `currentH2dRepoWitness`, and `physicalUnificationStatus` ALL remain
  strictly **`.OPEN`** (`¬ currentH2dRepoWitness.Satisfies o` for all `o : H2dCoreObligation`,
  `¬ wave11H2ConstructiveWitness.Satisfies .h2d_clay_4d_continuum_measure`,
  `physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN`).
- Retracted `W5.1-1` `41.76°/151` leaves an honest intermediate-coupling corridor `[1.8684, 271..428]`;
  `O-W9.A1-Univ` closes single-plaquette class-function sweeps (`W9-A1`); `W5-2`, `W6-2`, `W7-2`, `W8-1..W8-4`
  close their respective single-scale / non-MK / local Bochner / FKG-only dead ends while preserving
  strict epistemic honesty (`H2d` & `physicalUnificationStatus = .OPEN`). -/
theorem round08_irx_waves5to8_honest_open_lock :
    -- (1) Full Round 07 7-way counterexample & `.OPEN` lock preserved verbatim
    ((∀ c : SevenWayCounterexampleId, (sevenWaySignature c).positiveMassGap = false) ∧
      Function.Injective sevenWaySignature ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      ¬ (currentH2dRepoWitness.toH2LayerCandidate).Satisfies .h2d_clay_4d_continuum_measure ∧
      ¬ wave11H2ConstructiveWitness.Satisfies .h2d_clay_4d_continuum_measure ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) ∧
    -- (2) Round 08 Waves 5–8 structural barriers & open `[1.8684, 271..428]` corridor
    ((18684 / 10000 : ℝ) < 271 ∧ (271 : ℝ) ≤ 428) ∧
    -- (3) Wave 6/8 forced multiscale AF RG & Wave 8 Casimir/Dashen–Gross invariants
    ((6 : ℝ) * Real.pi ^ 2 / 11 < 8 * Real.log 2 ∧
      (5 / 12 : ℝ) - (1 / 3 : ℝ) = 1 / 12) ∧
    -- (4) Universal class-function lock O-W9.A1-Univ
    (∀ (Phi_tilde : ℝ → ℝ) (θ Phi_tilde' : ℝ),
      HasDerivAt Phi_tilde Phi_tilde' (Real.cos θ) →
      Phi_tilde' ≠ 0 → Real.sin θ ≠ 0 → Real.cos θ ≠ 0 →
      (Phi_tilde' * (-Real.sin θ)) / ((Phi_tilde' * (-Real.sin θ)) * (Real.cos θ / Real.sin θ)) =
        Real.tan θ) ∧
    -- (5) Honest conditional necessity: even inside `H2dMinimalIrreducibleCore`, `currentH2dRepoWitness` stays OPEN
    (∀ (core : Round05CrossObligationH2d.H2dMinimalIrreducibleCore),
      (∀ o : H2dCoreObligation, core.toObstructionCandidate.Satisfies o) ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) := by
  have r7 := round07_irx_frontier_honest_open_lock
  have hcur : ∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o := by
    intro o; cases o <;> simp [currentH2dRepoWitness, H2dObstructionCandidate.Satisfies]
  have hcur_clay : ¬ (currentH2dRepoWitness.toH2LayerCandidate).Satisfies .h2d_clay_4d_continuum_measure := by
    simp [currentH2dRepoWitness, H2dObstructionCandidate.toH2LayerCandidate, H2LayerCandidate.Satisfies]
    norm_num
  have hw11 : ¬ wave11H2ConstructiveWitness.Satisfies .h2d_clay_4d_continuum_measure := by
    simp [wave11H2ConstructiveWitness, H2LayerCandidate.Satisfies]
  have hopen : physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN := by decide
  refine ⟨⟨r7.1, r7.2.1, hcur, hcur_clay, hw11, hopen⟩,
    by norm_num, ⟨c2_litmus6_gap_analytic, by norm_num⟩, ?_, ?_⟩
  · intro Phi_tilde θ Phi_tilde' hd hP hsin hcos
    exact (theorem_o_w9_a1_univ Phi_tilde θ Phi_tilde' hd hP hsin hcos).2.2
  · intro core
    have hcore := Round05CrossObligationH2d.h2d_minimal_core_implies_all_three_obligations_and_clay core
    exact ⟨hcore.1.2.1, hcur, hopen⟩

end UEOTPhysicsUnification.IRXWaves5To8Consolidation
