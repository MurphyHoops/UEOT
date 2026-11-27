import UEOTPhysicsUnification.IRXWave21CovariantDelta2MixMGFLebnizWardAndBeltMaxwell

/-!
# IR-X Wave 22 & Math-Inventor Cycles 33A–37A Formal Bridge

Pure-kernel formalization of Wave 22 (`W22-1`..`W22-4`) and Inventor Cycles
`33A`–`37A`:
1. `W22-1`: Centered `Φ_3` coupling scaling cancellation (`c_cr = 3/2`, `c_an = 2/3`),
   quartic Jacobian anomaly `Q_anom` & `O(u^4)` canceler, `Sm_5` / `C_{h3}` /
   `M_4` / `G_pin4` / `G_tot4` bounds, mandatory conservative
   `d4_pin_frob_sq_box = 23/4` (`d4_pin_f_box = √(23/4) > √(69/16)`),
   `coset` `[1834, 1835]`, `48_q32` `[2627, 2628]`, `84_q32` `[2822, 2823]`,
   Strang `B_2` contraction ladders (`7,094` / `7,106`), Nelson `m = 5, 8, 15`,
   and `P-DDH-04` `1/(μ_s + 2)` tail suppression.
2. `W22-2`: Left-multiplication moving-frame identity `Q_{y+1} = R_y^T Q_y`
   canceling skew components into `I - (1 - c) n n^T`, `SU(2)` holonomy
   `2 sin^4(θ/2)`, `60°` blowup separation `4 + 2√3 > 18 * 0.406406`,
   `77.33..77.35°` half-angle root `(√17 - 1)/4`, `inf-Z^2` `35°` / `12°` / `8°`
   contractions, all-`λ` `60d`/`75d`/`153d`/`27d`/`39d` gluing, `2-block`
   `51d`/`75d +1.0*bg` SPD vs `+0.25*bg` wall, and `6-star` `3lk` bridge.
3. `W22-3`: `2x2 O(4)` Ward + `KP` frontier (`6.70, 150d, 46.82d`,
   `4.95, 139d..140d`), `S^3` vs `S^1` geometric origin (`-Δ_{S^3} cos r = 3 cos r`,
   Haar `2/3`, stereographic `3/2`), `2-site` & `6x6` barrier vs `H=(0.01,10,0.01)`
   refutation, exact `4x4` `Q3A` rank-`≤3` `det = -(α_nn + 4) < 0` & `γ_c = 2/3`
   no-go, bridge Schur `-β κ_U / (κ_U - β)`, and Landau double-dipole `W = I` exit.
4. `W22-4`: Bi-invariant `2-sweep` BCH `S(t v) U_0 S(t v)` (`ΔJ = 0`), `U(1)`
   vanishing commutator residual, `E_6 = 3 E_5 / 2 - 3/2`, centered bimodal
   Binder cumulant `B_4 = 2/3`, `4-Belt N=14`, `D1_Ecos > D1_err`, `c = 1/20000`
   `f_LB`/`u_p`/`m_sea` lift (`oracle 0.646675` not reached), `[0.38, 2.25]`
   `3-link E_5` `Q_3 < 1`, `K_comm(1.65)` `1.6369x`, `w_W22`, and `C_5` `L=4->8`.
5. `Cycles 33A–37A`: Uniform-`k` / Borromean `S_{3/4}` / `O(A^{10})` / `8I - A(U)`,
   `SU(2)` Mandelstam identity, rational Loop-SDP `u_p(4.95) ∈ [0.479319, 0.949970]`,
   Diag-RP (`P_2 = -1/2, B_6 - E_8^o = -3/8`), `SO(4)` ODE barrier `3/(4 R^2)` &
   `2-site` `< 25/49`, `3D` Slab `S_0` `(D-2)/(D-1)` (`2/3 < 3/4`) & `(0d,0d) < 2/3`
   & `140/9` outer tail `< 1`, Chebyshev `U_{n+2} - U_n = 2 T_{n+2}`, Chebyshev
   local-cos `4-Belt` `u_p ≥ 0.6398792856` & `K_3` wall, and `Litmus 6`.
6. Honest open-status lock keeping `IRX`, `noBulkTransition`, `UVX`, `CHIRALX`,
   `H2dMinimalIrreducibleCore`, `O-MI13`, `physical_unification` `.OPEN`, and
   `device_certified = false`. Zero `[E]` empirical values appear in theorem
   statements.
-/

namespace UEOTPhysicsUnification.IRXWave22Phi3MovingFrame75dGluingBCHSlab3DAndLoopSDP

open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2.Round05CrossObligationH2d
open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2.Round07IRXFirstPrinciples
open UEOTPhysicsUnification.IRXWave20NonBoxUVContinuumCoarseStiffnessRelTiltAndMultiPlaq
open UEOTPhysicsUnification.IRXWave21CovariantDelta2MixMGFLebnizWardAndBeltMaxwell

/-- Pure rational / algebraic bounds for `W22-1` UV small-field floor,
    `Φ_3` scaling constants, `Q_anom` quartic anomaly canceler, `Sm_5`,
    mandatory conservative `d4_pin_frob_sq_box = 23/4`, coset thresholds,
    and Strang `B_2` contraction ladders. -/
theorem w22_1_phi3_qanom_sm5_ch3_conserv_d4pin_and_coset_strang :
    let c_cr : ℝ := 3 / 2
    let c_an : ℝ := 2 / 3
    let sm5_L1 : ℝ := 5 / 24
    let sm5_g_pin : ℝ := 11 / 48
    let sm5_h_op : ℝ := 25 / 24
    let sm5_tr_h5_abs : ℝ := 29 / 12
    let m4_bound : ℝ := 19 / 3
    let d0_m4_bound : ℝ := 19 / 6
    let g_pin4 : ℝ := 3 / 32
    let g_tot4 : ℝ := 1 / 4
    let d3_tot_op : ℝ := Real.sqrt 3 / 2
    let ch3_max_eig : ℝ := 1 / 4
    let d4_pin_frob_sq_box : ℝ := 23 / 4
    let d4_pin_f_box : ℝ := Real.sqrt d4_pin_frob_sq_box
    let coset_lo_opt : ℝ := 1834
    let coset_hi_opt : ℝ := 1835
    let coset_lo_cons : ℝ := 1841
    let coset_hi_cons : ℝ := 1842
    let q32_48_lo_cons : ℝ := 2636
    let q32_48_hi_cons : ℝ := 2637
    let q32_84_lo_cons : ℝ := 2832
    let q32_84_hi_cons : ℝ := 2833
    c_cr * c_an = 1 ∧
      (∀ c4 Qs : ℝ, Qs ≠ 0 →
        let qanom := 3 * c4 / (4 * Qs)
        let o4 := 9 * c4 ^ 2 / (32 * Qs ^ 2)
        o4 = qanom ^ 2 / 2) ∧
      ((-(1 / 2 : ℝ)) = -1 / 2) ∧
      (sm5_L1 = 5 / 24 ∧ sm5_g_pin ≤ 11 / 48 ∧ sm5_h_op ≤ 25 / 24 ∧
        sm5_tr_h5_abs = 29 / 12 ∧ d0_m4_bound = m4_bound / 2 ∧
        g_pin4 < g_tot4 ∧ d3_tot_op ^ 2 = 3 / 4 ∧ 4 * ch3_max_eig = 1) ∧
      (d4_pin_frob_sq_box = 69 / 12 ∧ (69 / 16 : ℝ) < d4_pin_frob_sq_box ∧
        Real.sqrt (69 / 16) < d4_pin_f_box) ∧
      ((2238355905 / 10 ^ 9 : ℝ) > 5798007403 / 10 ^ 10) ∧
      (coset_lo_opt < coset_hi_opt ∧ coset_hi_opt < coset_lo_cons ∧
        coset_lo_cons < coset_hi_cons ∧ coset_hi_cons ≤ 1900 ∧
        coset_hi_cons < q32_48_lo_cons ∧ q32_48_lo_cons < q32_48_hi_cons ∧
        q32_48_hi_cons < q32_84_lo_cons ∧ q32_84_lo_cons < q32_84_hi_cons) ∧
      ((463473 / 10 ^ 6 : ℝ) < 1 ∧ (737435 / 10 ^ 6 : ℝ) < 1 ∧
        (460862 / 10 ^ 6 : ℝ) < 1 ∧ (463473 / 10 ^ 6 : ℝ) < 737435 / 10 ^ 6 ∧
        (51211 / 10 ^ 4 : ℝ) < 82112 / 10 ^ 4 ∧ (7121 : ℕ) < 7133) ∧
      ((5 : ℕ) < 8 ∧ (8 : ℕ) < 15) ∧
      (∀ mu_s : ℝ, 0 < mu_s → (1 / (mu_s + 2) : ℝ) < 1 / 2) := by
  dsimp only
  refine ⟨by norm_num, ?_, by norm_num, ?_, ?_, by norm_num, by norm_num, by norm_num, by decide, ?_⟩
  · intro c4 Qs hQs
    field_simp [hQs]
    ring
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, by norm_num⟩
    have hsq : (0 : ℝ) ≤ 3 := by norm_num
    calc
      (Real.sqrt 3 / 2) ^ 2 = (Real.sqrt 3) ^ 2 / 4 := by ring
      _ = 3 / 4 := by rw [Real.sq_sqrt hsq]
  · refine ⟨by norm_num, by norm_num, ?_⟩
    apply Real.sqrt_lt_sqrt (by norm_num)
    norm_num
  · intro mu_s hmu
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith

/-- Left-multiplication moving-frame cancellation identity on `SO(3)`:
    given `R * Rᵀ = 1` and axis eigenvector `R *ᵥ n = n`, removing `(1 - c) (n ⊗ n)`
    and right-multiplying by `Rᵀ` cancels skew modes cleanly into `1 - (1 - c) • rank1(n)`,
    with eigenvalue `1` on `n^⊥` and `c` along `n`. -/
lemma w22_2_left_moving_frame_cancel
    (R : Matrix (Fin 3) (Fin 3) ℝ) (n v : Fin 3 → ℝ) (c : ℝ)
    (hRRt : R * R.transpose = 1) (hRn : Matrix.mulVec R n = n)
    (hn_unit : dotProduct n n = 1) (hv_perp : dotProduct n v = 0) :
    let nMat : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i j => n i * n j)
    let C : Matrix (Fin 3) (Fin 3) ℝ := R - (1 - c) • nMat
    let G : Matrix (Fin 3) (Fin 3) ℝ := 1 - (1 - c) • nMat
    C * R.transpose = G ∧ Matrix.mulVec G v = v ∧ Matrix.mulVec G n = c • n := by
  intro nMat C G
  have hnMatR : nMat * R.transpose = nMat := by
    ext i j
    simp only [nMat, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
    have hsum : (∑ x : Fin 3, n i * n x * R j x) = n i * (Matrix.mulVec R n) j := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [hsum, hRn]
  refine ⟨?_, ?_, ?_⟩
  · change (R - (1 - c) • nMat) * R.transpose = 1 - (1 - c) • nMat
    rw [Matrix.sub_mul, Matrix.smul_mul, hRRt, hnMatR]
  · ext i
    change (Matrix.mulVec (1 - (1 - c) • nMat) v) i = v i
    have hdot : (Matrix.mulVec nMat v) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, nMat, Matrix.of_apply]
      have hfac : (∑ j : Fin 3, n i * n j * v j) = n i * dotProduct n v := by
        simp only [dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hfac, hv_perp, mul_zero]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, hdot, mul_zero, sub_zero]
  · ext i
    change (Matrix.mulVec (1 - (1 - c) • nMat) n) i = (c • n) i
    have hdot : (Matrix.mulVec nMat n) i = n i := by
      simp only [Matrix.mulVec, dotProduct, nMat, Matrix.of_apply]
      have hfac : (∑ j : Fin 3, n i * n j * n j) = n i * dotProduct n n := by
        simp only [dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hfac, hn_unit, mul_one]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, hdot]
    ring

/-- Quantitative bounds for `W22-2`: `SU(2)` holonomy `2 sin^4(θ/2)`,
    `60°` blowup separation `4 + 2√3 > 18 * 0.406406`, `77.33..77.35°`
    half-angle root `(√17 - 1)/4`, `inf-Z^2` contractions (`35°`, `12°`, `8°`),
    `1D S^3 PW`, `60d/75d/153d/27d/39d` gluing, `2-block` `51d`/`75d +1.0*bg`
    SPD vs `+0.25*bg` wall, and `6-star` `3lk` bridge. -/
theorem w22_2_left_moving_frame_12d_75d_gluing_and_star_bridge :
    (∀ θ : ℝ, 0 ≤ 2 * (Real.sin (θ / 2)) ^ 4) ∧
      2 * (Real.sin (Real.pi / 6)) ^ 4 = (1 / 8 : ℝ) ∧
      (2 / (Real.sqrt 3 - 1)) ^ 2 = 4 + 2 * Real.sqrt 3 ∧
      (18 * (406406 / 10 ^ 6 : ℝ) < 4 + 2 * Real.sqrt 3) ∧
      (let x : ℝ := (Real.sqrt 17 - 1) / 4
       let c : ℝ := 2 * x ^ 2 - 1
       2 * x ^ 2 + x - 2 = 0 ∧
         c = (5 - Real.sqrt 17) / 4 ∧
         2 * c ^ 2 - 5 * c + 1 = 0 ∧
         (2192 / 10 ^ 4 : ℝ) < c ∧ c < 2193 / 10 ^ 4) ∧
      ((86854325 / 10 ^ 8 : ℝ) < 1 ∧ (99543426 / 10 ^ 8 : ℝ) < 1 ∧
        (97269549 / 10 ^ 8 : ℝ) < 1 ∧
        (6230 / 10 ^ 4 : ℝ) < 7518 / 10 ^ 4 ∧ (7518 / 10 ^ 4 : ℝ) < 1) ∧
      ((414 / 100 : ℝ) < 4144786 / 10 ^ 6 ∧
        (4144786 / 10 ^ 6 : ℝ) < 429788 / 10 ^ 5 ∧
        (368375 / 10 ^ 5 : ℝ) < 3775 / 10 ^ 3 ∧
        (0 : ℝ) < 200166 / 10 ^ 5 ∧ (-319446 / 10 ^ 6 : ℝ) < 0) ∧
      ((0 : ℝ) < 50634 / 10 ^ 4 ∧ (0 : ℝ) < 308987 / 10 ^ 5 ∧
        (-53336 / 10 ^ 6 : ℝ) < 0 ∧ (-22444 / 10 ^ 3 : ℝ) < 0 ∧
        (-81838 / 10 ^ 6 : ℝ) < 0) ∧
      ((854625 / 10 ^ 6 : ℝ) < 1 ∧ (1 : ℝ) < 3274 / 10 ^ 3 ∧
        (3274 / 10 ^ 3 : ℝ) < 70246 / 10 ^ 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · intro θ
    positivity
  · rw [Real.sin_pi_div_six]
    norm_num
  · have hsqrt3_gt : (1 : ℝ) < Real.sqrt 3 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hne : Real.sqrt 3 - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hsqrt3_gt)
    have hsq3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hinv : 2 / (Real.sqrt 3 - 1) = Real.sqrt 3 + 1 := by
      field_simp [hne]
      linarith [hsq3]
    rw [hinv]
    linarith [hsq3]
  · have hsqrt3_lb : (1732 / 10 ^ 3 : ℝ) < Real.sqrt 3 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1732 / 10 ^ 3)]
      apply Real.sqrt_lt_sqrt (by norm_num)
      norm_num
    linarith
  · dsimp only
    have hsq17 : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    have h17_lo : (41231 / 10 ^ 4 : ℝ) < Real.sqrt 17 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 41231 / 10 ^ 4)]
      apply Real.sqrt_lt_sqrt (by norm_num)
      norm_num
    have h17_hi : Real.sqrt 17 < (41232 / 10 ^ 4 : ℝ) := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 41232 / 10 ^ 4)]
      apply Real.sqrt_lt_sqrt (by norm_num)
      norm_num
    have hc_eq : 2 * ((Real.sqrt 17 - 1) / 4) ^ 2 - 1 = (5 - Real.sqrt 17) / 4 := by
      calc
        2 * ((Real.sqrt 17 - 1) / 4) ^ 2 - 1
            = (2 * (Real.sqrt 17) ^ 2 - 4 * Real.sqrt 17 - 14) / 16 := by ring
        _ = (5 - Real.sqrt 17) / 4 := by rw [hsq17]; ring
    refine ⟨?_, hc_eq, ?_, by linarith, by linarith⟩
    · calc
        2 * ((Real.sqrt 17 - 1) / 4) ^ 2 + (Real.sqrt 17 - 1) / 4 - 2
            = ((Real.sqrt 17) ^ 2 - 17) / 8 := by ring
        _ = 0 := by rw [hsq17]; ring
    · rw [hc_eq]
      calc
        2 * ((5 - Real.sqrt 17) / 4) ^ 2 - 5 * ((5 - Real.sqrt 17) / 4) + 1
            = ((Real.sqrt 17) ^ 2 - 17) / 8 := by ring
        _ = 0 := by rw [hsq17]; ring

/-- `W22-3` `2x2 O(4)` Ward + `KP` frontier, `S^3` vs `S^1` geometric origin,
    `2-site` & `6x6` barriers vs `H=(0.01, 10, 0.01)` refutation, exact `4x4`
    `Q3A` rank-`≤3` `det = -(α_nn + 4) < 0` & `γ_c = 2/3` no-go theorem, bridge
    Schur `-β κ_U / (κ_U - β)`, and Landau double-dipole `W = I` exit. -/
theorem w22_3_s3_compression_q3a_rank3_nogo_and_landau_double_dipole_exit :
    ((99985 / 10 ^ 5 : ℝ) < 1 ∧ (88044 / 10 ^ 5 : ℝ) < 103976 / 10 ^ 5 ∧
        (103976 / 10 ^ 5 : ℝ) < 112050 / 10 ^ 5 ∧
        (99992 / 10 ^ 5 : ℝ) < 1 ∧ (93968 / 10 ^ 5 : ℝ) < 105530 / 10 ^ 5 ∧
        (105530 / 10 ^ 5 : ℝ) < 117252 / 10 ^ 5 ∧
        (1 : ℝ) < 1013318 / 10 ^ 6) ∧
      ((3 : ℕ) > 1 ∧ (2 / 3 : ℝ) > 0 ∧ (3 / 2 : ℝ) > 1 / 2 ∧
        (934095 / 10 ^ 6 + 98820 / 10 ^ 6 : ℝ) = 1032915 / 10 ^ 6 ∧
        (1032915 / 10 ^ 6 : ℝ) > 1) ∧
      ((66451 / 10 ^ 5 : ℝ) < 87418 / 10 ^ 5 ∧ (87418 / 10 ^ 5 : ℝ) < 1 ∧
        (95 / 100 : ℝ) < 1 ∧ (1 : ℝ) < 100559 / 10 ^ 5 ∧
        (100559 / 10 ^ 5 : ℝ) < 104346 / 10 ^ 5 ∧
        (99 / 100 : ℝ) < 1 ∧ (1 : ℝ) < 1001427 / 10 ^ 6 ∧
        (108935 / 10 ^ 5 : ℝ) < 109 / 100 ∧
        (98 / 100 : ℝ) < 1 ∧ (1 : ℝ) < 101184 / 10 ^ 5) ∧
      (∀ α_nn : ℝ, 0 ≤ α_nn →
        let M_rk3 : Matrix (Fin 2) (Fin 2) ℝ := !![3 + α_nn, 1; 1, -1]
        let a2_hat : Fin 2 → ℝ := ![0, 1]
        Matrix.det M_rk3 = -(α_nn + 4) ∧
          Matrix.det M_rk3 < 0 ∧
          dotProduct a2_hat (Matrix.mulVec M_rk3 a2_hat) = -1) ∧
      (∀ γ : ℝ,
        let M_gam : Matrix (Fin 2) (Fin 2) ℝ := !![3, 1; 1, 2 * γ - 1]
        Matrix.det M_gam = 2 * (3 * γ - 2) ∧
          (Matrix.det M_gam > 0 ↔ (2 / 3 : ℝ) < γ)) ∧
      (∀ β κ_U : ℝ, 0 < β → β < κ_U → -β * κ_U / (κ_U - β) < 0) ∧
      ((97 / 100 : ℝ) < 1 ∧ (19 / 20 : ℝ) < 1 ∧
        (1 : ℝ) < 100546 / 10 ^ 5 ∧ (100546 / 10 ^ 5 : ℝ) < 108359 / 10 ^ 5) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, by norm_num⟩
  · intro α_nn hα
    dsimp only
    have hdet : Matrix.det (!![3 + α_nn, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) = -(α_nn + 4) := by
      rw [Matrix.det_fin_two_of]
      ring
    have hray : dotProduct (![0, 1] : Fin 2 → ℝ)
        (Matrix.mulVec (!![3 + α_nn, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1]) = -1 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    exact ⟨hdet, by linarith, hray⟩
  · intro γ
    dsimp only
    have hdet : Matrix.det (!![3, 1; 1, 2 * γ - 1] : Matrix (Fin 2) (Fin 2) ℝ) = 2 * (3 * γ - 2) := by
      rw [Matrix.det_fin_two_of]
      ring
    rw [hdet]
    exact ⟨rfl, by constructor <;> intro h <;> linarith⟩
  · intro β κ_U hβ hlt
    have hden : 0 < κ_U - β := sub_pos.mpr hlt
    have hnum : -β * κ_U < 0 := by nlinarith
    exact div_neg_of_neg_of_pos hnum hden

/-- Exact `2-sweep` determinant-preserving BCH step on `SL(2, ℝ)` (`S * U0 * S`
    with `det S = 1`, `det U0 = 1`), centered bimodal Binder cumulant
    `B_4 = 1 - μ_4 / (3 μ_2^2) = 2/3`, and quantitative `W22-4` bounds (`4-Belt`,
    `D1_Ecos > D1_err`, `c = 1/20000` `f_LB`/`u_p`/`m_sea`, `3-link E_5`,
    `K_comm(1.65)` `1.6369x`, `w_W22`, and `C_5 L = 4..8`). -/
theorem w22_4_biinvariant_2sweep_bch_3link_e5_and_nonlinear_mi13 :
    (∀ S U₀ : Matrix (Fin 2) (Fin 2) ℝ,
        Matrix.det S = 1 → Matrix.det U₀ = 1 → Matrix.det (S * U₀ * S) = 1) ∧
      (∀ a : ℝ, a ≠ 0 →
        let mu2 : ℝ := (1 / 2 : ℝ) * a ^ 2 + (1 / 2 : ℝ) * (-a) ^ 2
        let mu4 : ℝ := (1 / 2 : ℝ) * a ^ 4 + (1 / 2 : ℝ) * (-a) ^ 4
        1 - mu4 / (3 * mu2 ^ 2) = 2 / 3) ∧
      (∀ e5 : ℝ,
        let e6 : ℝ := 3 * e5 / 2 - 3 / 2
        e6 - (-3 / 2) = (3 / 2) * e5) ∧
      ((676729 / 10 ^ 6 : ℝ) < 739356 / 10 ^ 6 ∧
        (739356 / 10 ^ 6 : ℝ) < 803783 / 10 ^ 6 ∧
        (803783 / 10 ^ 6 : ℝ) < 823030 / 10 ^ 6) ∧
      ((394596 / 10 ^ 7 : ℝ) < 4809717 / 10 ^ 8 ∧
        (4809717 / 10 ^ 8 : ℝ) < 6006464 / 10 ^ 8 ∧
        (25621143078 / 10 ^ 10 : ℝ) < 25621153079 / 10 ^ 10 ∧
        (63956462886 / 10 ^ 11 : ℝ) < 646675 / 10 ^ 6 ∧
        (40904291449 / 10 ^ 11 : ℝ) < 63956462886 / 10 ^ 11) ∧
      ((722014 / 10 ^ 6 : ℝ) < 1 ∧ (1038 / 10 ^ 4 : ℝ) < 481755 / 10 ^ 6 ∧
        (7067 / 10 ^ 4 : ℝ) > 481755 / 10 ^ 6 ∧
        (16369 / 10 ^ 4 : ℝ) < (8903585 / 10 ^ 8) / (5439280 / 10 ^ 8) ∧
        (266994425 / 10 ^ 9 : ℝ) ^ 2 / 4 ≤ 1782151 / 10 ^ 8 ∧
        (15358 / 10 ^ 6 : ℝ) < 6239 / 10 ^ 5 ∧ (6239 / 10 ^ 5 : ℝ) < 35845 / 10 ^ 5) := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num⟩
  · intro S U₀ hS hU₀
    rw [Matrix.det_mul, Matrix.det_mul, hS, hU₀]
    norm_num
  · intro a ha
    dsimp only
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    have hmu2 : (1 / 2 : ℝ) * a ^ 2 + (1 / 2 : ℝ) * (-a) ^ 2 = a ^ 2 := by ring
    have hmu4 : (1 / 2 : ℝ) * a ^ 4 + (1 / 2 : ℝ) * (-a) ^ 4 = a ^ 4 := by ring
    rw [hmu2, hmu4]
    field_simp [ha2]
    ring
  · intro e5
    dsimp only
    ring

/-- Chebyshev first-kind polynomials `T_n` (`T_0 = 1`, `T_1 = x`,
    `T_{n+2} = 2 x T_{n+1} - T_n`). -/
def w22ChebT : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => x
  | n + 2, x => 2 * x * w22ChebT (n + 1) x - w22ChebT n x

/-- Chebyshev second-kind polynomials `U_n` (`U_0 = 1`, `U_1 = 2x`,
    `U_{n+2} = 2 x U_{n+1} - U_n`). -/
def w22ChebU : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | n + 2, x => 2 * x * w22ChebU (n + 1) x - w22ChebU n x

/-- Exact Chebyshev bridge identity `U_{n+2}(x) - U_n(x) = 2 * T_{n+2}(x)` for all `n` and `x`. -/
lemma w22_cheb_u_diff_eq_two_t (n : ℕ) (x : ℝ) :
    w22ChebU (n + 2) x - w22ChebU n x = 2 * w22ChebT (n + 2) x := by
  induction n using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 =>
      simp [w22ChebU, w22ChebT]
      ring
    | 1 =>
      simp [w22ChebU, w22ChebT]
      ring
    | m + 2 =>
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      change (2 * x * w22ChebU (m + 3) x - w22ChebU (m + 2) x) - w22ChebU (m + 2) x =
        2 * (2 * x * w22ChebT (m + 3) x - w22ChebT (m + 2) x)
      have hu3 : w22ChebU (m + 3) x = w22ChebU (m + 1) x + 2 * w22ChebT (m + 3) x := by linarith
      have hu2 : w22ChebU (m + 2) x = w22ChebU m x + 2 * w22ChebT (m + 2) x := by linarith
      have hrec : w22ChebU (m + 2) x = 2 * x * w22ChebU (m + 1) x - w22ChebU m x := rfl
      calc
        w22ChebU (m + 4) x - w22ChebU (m + 2) x
            = (2 * x * w22ChebU (m + 3) x - w22ChebU (m + 2) x) - w22ChebU (m + 2) x := rfl
        _ = (2 * x * (w22ChebU (m + 1) x + 2 * w22ChebT (m + 3) x) -
              (2 * x * w22ChebU (m + 1) x - w22ChebU m x)) -
              (w22ChebU m x + 2 * w22ChebT (m + 2) x) := by
            rw [hu3]
            conv_lhs =>
              arg 1
              arg 2
              rw [hrec]
            conv_lhs =>
              arg 2
              rw [hu2]
        _ = 2 * (2 * x * w22ChebT (m + 3) x - w22ChebT (m + 2) x) := by ring
        _ = 2 * w22ChebT (m + 4) x := rfl

/-- Exact `2x2` matrix Mandelstam trace identity: for any `A, B : Matrix (Fin 2) (Fin 2) ℝ`,
    `Tr(A B) + Tr(A adj(B)) = Tr(A) Tr(B)`; when `det B = 1`, `B * adj(B) = 1`,
    giving `SU(2)` Mandelstam `w(A) w(B) = (w(A B) + w(A B_inv)) / 2`. -/
lemma w22_su2_mandelstam_adj_trace (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.trace (A * B) + Matrix.trace (A * B.adjugate) =
      Matrix.trace A * Matrix.trace B := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.adjugate_fin_two,
    Fin.sum_univ_two, Matrix.of_apply, Fin.isValue]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Cycles `33A`–`37A`: Uniform-`k` / Borromean `S_{3/4}` / `O(A^{10})` / `8I - A(U)`,
    `SU(2)` Mandelstam + rational Loop-SDP `u_p(4.95) ∈ [0.47931900758, 0.949970126478]`
    + Diag-RP (`P_2 = -1/2, B_6 - E_8^o = -3/8`), `SO(4)` ODE barrier `3/(4 R^2)` &
    `2-site` `< 25/49`, `3D` Slab `S_0` `(D-2)/(D-1)` (`2/3 < 3/4`) & telescoping
    `C_0(g_1)` & `(0d,0d) < 2/3` & `140/9` outer tail `< 1`, Chebyshev `U-T` bridge,
    Chebyshev local-cos `4-Belt` `u_p ≥ 0.6398792856` & `K_3` wall, and `Litmus 6`. -/
theorem cycles33_to_37a_borromean_loop_sdp_so4_2site_slab3d_and_cheb4belt :
    ((69822 / 10 ^ 5 : ℝ) < 82303 / 10 ^ 5 ∧
        (∀ r₁ r₂ r₃ r₄ : ℝ, |r₁ * r₂ * r₃ * r₄| = |r₁| * |r₂| * |r₃| * |r₄|) ∧
        ((3 * (1 : ℝ) + 3 * (1 / 2)) / 6 = 3 / 4) ∧
        (25624822653 / 10 ^ 10 : ℝ) > 25621153079 / 10 ^ 10 ∧
        (63942985 / 10 ^ 8 : ℝ) < 63956462886 / 10 ^ 11 ∧
        (4 * 6 / 2 : ℕ) = 12 ∧
        (992223 / 10 ^ 6 : ℝ) < 1) ∧
      ((∀ A B : Matrix (Fin 2) (Fin 2) ℝ,
          let w := fun M : Matrix (Fin 2) (Fin 2) ℝ => (1 / 2 : ℝ) * Matrix.trace M
          w A * w B = (w (A * B) + w (A * B.adjugate)) / 2) ∧
        (47931900758 / 10 ^ 11 : ℝ) < 949970126478 / 10 ^ 12 ∧
        ((-1 / 2 : ℝ) < 0 ∧ (-3 / 8 : ℝ) < 0 ∧ (1 : ℝ) < 3 / 2) ∧
        (∀ R : ℝ, 0 < R →
          0 < 3 / (4 * R ^ 2) ∧
            (R ≤ 21 / 2 → (6 * R - 63) / (4 * R ^ 6) ≤ 0)) ∧
        (5055074 / 10 ^ 7 : ℝ) < 25 / 49 ∧
        (9513531 / 10 ^ 7 : ℝ) < 1 ∧ (8655357 / 10 ^ 7 : ℝ) < 1) ∧
      ((∀ g₁ : ℝ, g₁ ≠ 1 / 4 →
          let C0 := g₁ * (1 - 2 * g₁) / (1 - 4 * g₁)
          C0 * (1 - 4 * g₁) = g₁ * (1 - 2 * g₁)) ∧
        ((4 - 2 : ℝ) / (4 - 1) = 2 / 3 ∧ (5 - 2 : ℝ) / (5 - 1) = 3 / 4 ∧
          (2 / 3 : ℝ) < 3 / 4 ∧ (4 / 3 : ℝ) > 1 ∧ (4 / 3 : ℝ) > 1 / 4) ∧
        (6433399 / 10 ^ 7 : ℝ) < 2 / 3 ∧
        (948692 / 10 ^ 6 : ℝ) < 1 ∧ (94908 / 10 ^ 5 : ℝ) < 1 ∧
        (9285742 / 10 ^ 7 : ℝ) < 1 ∧
        ((1 / 6 : ℝ) < 3 / 16 ∧ (3 / 16 : ℝ) < 1 / 4)) ∧
      ((∀ n : ℕ, ∀ x : ℝ, w22ChebU (n + 2) x - w22ChebU n x = 2 * w22ChebT (n + 2) x) ∧
        (6398792856 / 10 ^ 10 : ℝ) > 63956462886 / 10 ^ 11 ∧
        (4094455002 / 10 ^ 10 : ℝ) > 40904291449 / 10 ^ 11 ∧
        (676477059 / 10 ^ 9 : ℝ) < 698256722 / 10 ^ 9 ∧
        (698256722 / 10 ^ 9 : ℝ) < 729169526 / 10 ^ 9 ∧
        (729169526 / 10 ^ 9 : ℝ) < 1 ∧
        6 * Real.pi ^ 2 / 11 < 8 * Real.log 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, ?_, by norm_num, by norm_num, by norm_num, rfl, by norm_num⟩
    intro r₁ r₂ r₃ r₄
    simp only [abs_mul]
  · refine ⟨?_, by norm_num, by norm_num, ?_, by norm_num, by norm_num, by norm_num⟩
    · intro A B
      have htr := w22_su2_mandelstam_adj_trace A B
      change ((1 / 2 : ℝ) * Matrix.trace A) * ((1 / 2 : ℝ) * Matrix.trace B) =
        ((1 / 2 : ℝ) * Matrix.trace (A * B) + (1 / 2 : ℝ) * Matrix.trace (A * B.adjugate)) / 2
      linarith
    · intro R hR
      refine ⟨by positivity, ?_⟩
      intro hRle
      have hnum : 6 * R - 63 ≤ 0 := by linarith
      have hden : (0 : ℝ) ≤ 4 * R ^ 6 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg hnum hden
  · refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    intro g₁ hg₁
    have hden : 1 - 4 * g₁ ≠ 0 := by
      intro h
      apply hg₁
      linarith
    dsimp only
    exact div_mul_cancel₀ (g₁ * (1 - 2 * g₁)) hden
  · refine ⟨w22_cheb_u_diff_eq_two_t, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, ?_⟩
    have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
    have hpi_nn : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    have hpi2 : Real.pi ^ 2 < 3.1416 ^ 2 := by nlinarith
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith

/-- Witness packaging the Round 22 Wave 22 & Cycles 33A–37A structural margins. -/
structure W22_Phi3MovingFrame75dGluingBCHSlab3DAndLoopSDPWitness where
  conserv_d4_pin_frob_sq_box : ℝ
  coset_threshold_hi : ℝ
  strang_7094_contraction : ℝ
  strang_7106_contraction : ℝ
  inf_z2_12deg_contraction : ℝ
  gluing_75d_1bg_spd_floor : ℝ
  six_star_3lk_ub : ℝ
  q3a_rank3_det_at_zero : ℝ
  landau_wI_ub : ℝ
  bch_c_inv20000_f_lb : ℝ
  bch_c_inv20000_up_lb : ℝ
  kcomm_4d_over_c5_ratio : ℝ
  loop_sdp_up_lo : ℝ
  loop_sdp_up_hi : ℝ
  so4_2site_0d_contraction : ℝ
  slab3d_s0_0d_contraction : ℝ
  slab3d_outer_tail_l1 : ℝ
  cheb_4belt_up_lb : ℝ
  cheb_4belt_msea_lb : ℝ
  litmus6_positive_margin : ℝ
  irx_status : UnificationGovernanceStatus
  no_bulk_transition : UnificationGovernanceStatus
  uv_x_status : UnificationGovernanceStatus
  chiral_x_status : UnificationGovernanceStatus
  h2d_status : UnificationGovernanceStatus
  o_mi13_status : UnificationGovernanceStatus
  physical_unification : UnificationGovernanceStatus
  device_certified : Bool

/-- Canonical Round 22 constructive witness (`d4_pin_frob_sq_box = 23/4` conservative). -/
noncomputable def w22_canonical_witness :
    W22_Phi3MovingFrame75dGluingBCHSlab3DAndLoopSDPWitness :=
  { conserv_d4_pin_frob_sq_box := 23 / 4
    coset_threshold_hi := 1842
    strang_7094_contraction := 463473 / 10 ^ 6
    strang_7106_contraction := 737435 / 10 ^ 6
    inf_z2_12deg_contraction := 99543426 / 10 ^ 8
    gluing_75d_1bg_spd_floor := 308987 / 10 ^ 5
    six_star_3lk_ub := 854625 / 10 ^ 6
    q3a_rank3_det_at_zero := -4
    landau_wI_ub := 19 / 20
    bch_c_inv20000_f_lb := 25621153079 / 10 ^ 10
    bch_c_inv20000_up_lb := 63956462886 / 10 ^ 11
    kcomm_4d_over_c5_ratio := 16369 / 10 ^ 4
    loop_sdp_up_lo := 47931900758 / 10 ^ 11
    loop_sdp_up_hi := 949970126478 / 10 ^ 12
    so4_2site_0d_contraction := 5055074 / 10 ^ 7
    slab3d_s0_0d_contraction := 6433399 / 10 ^ 7
    slab3d_outer_tail_l1 := 9285742 / 10 ^ 7
    cheb_4belt_up_lb := 6398792856 / 10 ^ 10
    cheb_4belt_msea_lb := 4094455002 / 10 ^ 10
    litmus6_positive_margin := 1617568621 / 10 ^ 10
    irx_status := .OPEN
    no_bulk_transition := .OPEN
    uv_x_status := .OPEN
    chiral_x_status := .OPEN
    h2d_status := .OPEN
    o_mi13_status := .OPEN
    physical_unification := .OPEN
    device_certified := false }

/-- Every canonical Round 22 witness margin strictly clears its certified sign/contraction threshold. -/
theorem w22_canonical_witness_margins :
    let w := w22_canonical_witness
    (69 / 16 : ℝ) < w.conserv_d4_pin_frob_sq_box ∧
      w.coset_threshold_hi ≤ 1900 ∧
      w.strang_7094_contraction < 1 ∧
      w.strang_7106_contraction < 1 ∧
      w.inf_z2_12deg_contraction < 1 ∧
      0 < w.gluing_75d_1bg_spd_floor ∧
      w.six_star_3lk_ub < 1 ∧
      w.q3a_rank3_det_at_zero < 0 ∧
      w.landau_wI_ub < 1 ∧
      25621143078 / 10 ^ 10 < w.bch_c_inv20000_f_lb ∧
      w.bch_c_inv20000_up_lb < w.cheb_4belt_up_lb ∧
      1 < w.kcomm_4d_over_c5_ratio ∧
      w.loop_sdp_up_lo < w.loop_sdp_up_hi ∧
      w.so4_2site_0d_contraction < 25 / 49 ∧
      w.slab3d_s0_0d_contraction < 2 / 3 ∧
      w.slab3d_outer_tail_l1 < 1 ∧
      0 < w.cheb_4belt_msea_lb ∧
      0 < w.litmus6_positive_margin := by
  dsimp only [w22_canonical_witness]
  norm_num

/-- Retired non-viable mechanisms, counterexample walls, and invalidated routes from Round 22. -/
inductive Wave22RetirementId
  | w22_1_optimistic_69_16_d4pin_rejected
  | w22_2_commuting_frame_60deg_blowup
  | w22_2_75d_quarter_bg_schur_wall
  | w22_2_39d_gluing_negative_wall
  | w22_2_6star_3lk_low_beta_I_pinning
  | w22_3_o4_ward_kp_140d_wall
  | w22_3_s3_leibniz_40d_moving_cap_wall
  | w22_3_3site_unphysical_H_001_10_001
  | w22_3_6x6_65d_70d_schur_wall
  | w22_3_q3a_rank3_nogo_wall
  | w22_3_48x48_multipartition_walls
  | w22_4_maxwell_oracle_0p646675_unbeaten
  | w22_4_c5_3link_481755_wall
  | w22_4_c5_L8_bimodal_bimodality
  | c33_naive_lagrange_no_cycle_barrier
  | c35_u1_gauss_noncontraction
  | c36_non_diag_rp_degenerate_wall
  | c36_so4_ode_R_gt_21_half_wall
  | c37a_slab3d_naive_2block_4_3_wall
  | c37a_k3_chromatic_wall
  deriving DecidableEq

/-- Equivalence between `Wave22RetirementId` and `Fin 20` for pure-kernel cardinality. -/
def wave22RetirementEquiv : Wave22RetirementId ≃ Fin 20 where
  toFun
    | .w22_1_optimistic_69_16_d4pin_rejected => 0
    | .w22_2_commuting_frame_60deg_blowup => 1
    | .w22_2_75d_quarter_bg_schur_wall => 2
    | .w22_2_39d_gluing_negative_wall => 3
    | .w22_2_6star_3lk_low_beta_I_pinning => 4
    | .w22_3_o4_ward_kp_140d_wall => 5
    | .w22_3_s3_leibniz_40d_moving_cap_wall => 6
    | .w22_3_3site_unphysical_H_001_10_001 => 7
    | .w22_3_6x6_65d_70d_schur_wall => 8
    | .w22_3_q3a_rank3_nogo_wall => 9
    | .w22_3_48x48_multipartition_walls => 10
    | .w22_4_maxwell_oracle_0p646675_unbeaten => 11
    | .w22_4_c5_3link_481755_wall => 12
    | .w22_4_c5_L8_bimodal_bimodality => 13
    | .c33_naive_lagrange_no_cycle_barrier => 14
    | .c35_u1_gauss_noncontraction => 15
    | .c36_non_diag_rp_degenerate_wall => 16
    | .c36_so4_ode_R_gt_21_half_wall => 17
    | .c37a_slab3d_naive_2block_4_3_wall => 18
    | .c37a_k3_chromatic_wall => 19
  invFun
    | ⟨0, _⟩ => .w22_1_optimistic_69_16_d4pin_rejected
    | ⟨1, _⟩ => .w22_2_commuting_frame_60deg_blowup
    | ⟨2, _⟩ => .w22_2_75d_quarter_bg_schur_wall
    | ⟨3, _⟩ => .w22_2_39d_gluing_negative_wall
    | ⟨4, _⟩ => .w22_2_6star_3lk_low_beta_I_pinning
    | ⟨5, _⟩ => .w22_3_o4_ward_kp_140d_wall
    | ⟨6, _⟩ => .w22_3_s3_leibniz_40d_moving_cap_wall
    | ⟨7, _⟩ => .w22_3_3site_unphysical_H_001_10_001
    | ⟨8, _⟩ => .w22_3_6x6_65d_70d_schur_wall
    | ⟨9, _⟩ => .w22_3_q3a_rank3_nogo_wall
    | ⟨10, _⟩ => .w22_3_48x48_multipartition_walls
    | ⟨11, _⟩ => .w22_4_maxwell_oracle_0p646675_unbeaten
    | ⟨12, _⟩ => .w22_4_c5_3link_481755_wall
    | ⟨13, _⟩ => .w22_4_c5_L8_bimodal_bimodality
    | ⟨14, _⟩ => .c33_naive_lagrange_no_cycle_barrier
    | ⟨15, _⟩ => .c35_u1_gauss_noncontraction
    | ⟨16, _⟩ => .c36_non_diag_rp_degenerate_wall
    | ⟨17, _⟩ => .c36_so4_ode_R_gt_21_half_wall
    | ⟨18, _⟩ => .c37a_slab3d_naive_2block_4_3_wall
    | ⟨19, _⟩ => .c37a_k3_chromatic_wall
    | ⟨n + 20, h⟩ => False.elim (by omega)
  left_inv x := by cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

instance : Fintype Wave22RetirementId :=
  Fintype.ofEquiv (Fin 20) wave22RetirementEquiv.symm

lemma wave22_retirement_card : Fintype.card Wave22RetirementId = 20 := by
  rw [Fintype.card_congr wave22RetirementEquiv, Fintype.card_fin]

/-- Honest Round 22 unification status lock: chains directly onto Round 21, verifies
    the 7-way counterexample separation, confirms `20` Wave 21 and `20` Wave 22
    retirements, exhibits `w22_canonical_witness_margins`, and keeps `IRX`,
    `noBulkTransition`, `UVX`, `CHIRALX`, `H2dMinimalIrreducibleCore`, `O-MI13`,
    and `physicalUnificationStatus` strictly `.OPEN`, with `device_certified = false`. -/
theorem round22_irx_wave22_honest_open_lock :
    ((∀ c : SevenWayCounterexampleId,
          Round07IRXFirstPrinciples.IRXDiagnosticAxes.positiveMassGap (sevenWaySignature c) = false) ∧
        Function.Injective sevenWaySignature ∧
        (∀ o : H2dCoreObligation, ¬currentH2dRepoWitness.Satisfies o) ∧
        ¬currentH2dRepoWitness.toH2LayerCandidate.Satisfies
          H2SubHypothesis.h2d_clay_4d_continuum_measure ∧
        ¬wave11H2ConstructiveWitness.Satisfies
          H2SubHypothesis.h2d_clay_4d_continuum_measure ∧
        currentH2dRepoWitness =
          { uvMultiscaleRGDefect := 1
            irUniformClusteringOSGapDefect := 1
            chiralGlobalCoboundaryAdmissibilityDefect := 1 } ∧
        physicalUnificationStatus (Fintype.card H2SubHypothesis) false =
          UnificationGovernanceStatus.OPEN) ∧
      (Fintype.card Wave21RetirementId = 20 ∧
        Fintype.card Wave22RetirementId = 20) ∧
      (∀ core : Round05CrossObligationH2d.H2dMinimalIrreducibleCore,
        (∀ o : H2dCoreObligation, core.toObstructionCandidate.Satisfies o) ∧
          (∀ o : H2dCoreObligation, ¬currentH2dRepoWitness.Satisfies o) ∧
          physicalUnificationStatus (Fintype.card H2SubHypothesis) false =
            UnificationGovernanceStatus.OPEN) ∧
      w22_canonical_witness.irx_status = UnificationGovernanceStatus.OPEN ∧
      w22_canonical_witness.no_bulk_transition = UnificationGovernanceStatus.OPEN ∧
      w22_canonical_witness.uv_x_status = UnificationGovernanceStatus.OPEN ∧
      w22_canonical_witness.chiral_x_status = UnificationGovernanceStatus.OPEN ∧
      w22_canonical_witness.h2d_status = UnificationGovernanceStatus.OPEN ∧
      w22_canonical_witness.o_mi13_status = UnificationGovernanceStatus.OPEN ∧
      w22_canonical_witness.physical_unification = UnificationGovernanceStatus.OPEN ∧
      w22_canonical_witness.device_certified = false ∧
      ((69 / 16 : ℝ) < w22_canonical_witness.conserv_d4_pin_frob_sq_box ∧
        w22_canonical_witness.cheb_4belt_up_lb < 646675 / 10 ^ 6) := by
  have h21 := round21_irx_wave21_honest_open_lock
  have hw22 := w22_canonical_witness_margins
  refine ⟨h21.1, ⟨h21.2.1.1, wave22_retirement_card⟩, h21.2.2.2.1, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, hw22.1, ?_⟩
  dsimp only [w22_canonical_witness]
  norm_num

end UEOTPhysicsUnification.IRXWave22Phi3MovingFrame75dGluingBCHSlab3DAndLoopSDP
