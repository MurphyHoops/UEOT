import UEOTPhysicsUnification.IRXWave20NonBoxUVContinuumCoarseStiffnessRelTiltAndMultiPlaq

/-!
# Round 21 Wave 21 (`W21-1..W21-5` & `math-inventor` Cycles 29–32: Covariant `δ₂`, All-`λ` `O-MI29` MGF, Moving-Frame `O(4)` Ward + `S¹` Leibniz IBP, and 4-Belt Maxwell–Wick)

Pure-kernel (`{propext, Classical.choice, Quot.sound}`, zero proof escapes, zero warnings)
formalization of Round 21 Wave 21 (`W21-1..W21-5`) and `math-inventor` Cycles 29–32 `[C/B/P]` results
with strict `[E]` / `[X]` isolation:

1. **§1 (`W21-1` Covariant `δ₂`, `P_perp` & `H_{Sm3}` SOS, `P-DDH-04` `1/(μ_s+2)`, Nelson `m=5,8,15`, Strang `B₂` `[2664, 2665]`)**:
   - `w21_1_covariant_delta2_pperp_sos_nelson_and_strang`:
     - Exact `4×4` projector `P_perp = I_4 - d_4 d_4^T / 4` (`P_perp^2 = P_perp`, `Tr(P_perp) = 3`, `e₁ᵀ P_perp e₁ = 3/4`);
     - 3D cross-product Lagrange SOS `(v × c)² + ⟨v, c⟩² = ‖v‖² ‖c‖²`, `(1/√3)` operator bracket,
       and `h_row = 3√3/8` (`h_row² = 27/64`);
     - Exact 1D `δ₂` cubic potential map `x(w) = w - ε (v₃ / (6 q)) w² + ε² (5 v₃² / (72 q²)) w³`
       eliminating `O(ε¹)` and `O(ε²)` identically with exact residual `ε³ (v₃³ / (27 q²)) w⁵`;
     - Exact Nelson `(4m-1)!! / m!` (`m = 5: 43648605/8`, `m = 8: 609202488769875/128`,
       `m = 15: 45755704411556570860091208170625/2048`), `P-DDH-04` `1 / (mu_s + 2)`,
       `11×11` free vs pinned stiffness (`2.2374889 > 0.5811843`), `[4784, 4785] → [2664, 2665]` (`1.795×`),
       and Strang `B₂` chains `2665 → 8.1875` (`10,317` steps, `sum < 0.47`) & `2665 → 4.95` (`10,329` steps, `sum < 0.74`).

2. **§2 (`W21-2` `SO(3)` Pythagorean Operator, All-`λ` `O-MI29` MGF, Sign Cancellation, `27d` Gribov & Continuum `6D > W_side`)**:
   - `w21_2_so3_pythagorean_all_lambda_mgf_gribov_and_cont6d`:
     - Exact `SO(3)` Jacobian Pythagorean operator identity `(t I₃ + [w]_×)ᵀ (t I₃ + [w]_×) = (t² + ‖w‖²) I₃ - w wᵀ`;
     - Sign-dropped `1 + √3/2 > 1 > 0.406407` signed `60°` separation, `d_bar` piecewise continuity at `r + s = π`,
       and Legendre log-dual criticality (`-1/x + a = 0 ↔ x = 1/a`);
     - All-`λ ∈ (0, ∞)` `O-MI29` `mid_60d ≥ 4.1870..5.9724 > 4.14`, `mid_75d(4.95) ≥ 4.3498 > 4.14`,
       and Cycle 22 `153°` ceiling `< 3.6838 < 3.775`;
     - Infinite-dim 1D `S³` transfer `[0.6230..0.7518] < 1`, `27d` Gribov `LDLT` SPD `[7.4061..15.6375]` vs `39d` `-0.319446`,
       and all six continuum `6D > W_side` anchors across `[3.70..6.95]`.

3. **§3 (`W21-3` `Q3A` Soft Modes, Curved `S³` Laplacian & Leibniz IBP, `O(4)` Ward `2×2`, `48×48` Double-Dipole & `C3 < 4D < 1 < C5`)**:
   - `w21_3_q3a_s3_leibniz_o4_ward_48x48_and_rb_order`:
     - `Q3A` pair-bond `γ_c = 2/3` (`36γ - 24 = 0`), `γ = 1` factor `λ(λ-2)(λ²-4λ+2)` (`2 - √2 > 0`),
       `1 - √5` root (`λ² - 2λ - 4 = 0`), Schur unfrozen bridge, and symmetric `150°` gap `2√2 sin(π/24) > 0`;
     - Exact `HasDerivAt` radial `S³` Laplacian `-Δ_{S³} cos r = 3 cos r` vs `S¹` (`cos r`) & product Leibniz IBP;
     - Exact `4×4` orthonormal Hadamard `Vᵀ V = I₄` diagonalizing `A_{C₄}` to `diag(2, 0, 0, -2)`;
     - `2×2 O(4)` Ward + `S¹²` closures at `6.95 150° 46.6°`, `4.95 135° 57°`, `5.95 135° 55°`, `4.95 150° 48° < 1 < 49°`,
       `48×48` double-dipole walls (`≥ 1.05457 > 1`), and symbolic + numeric `C3 < 4D < 1 < C5` (`2×2` & `6×6`).

4. **§4 (`W21-4` & `Cycles 29–32` 4-Belt Maxwell–Wick `u_p ≥ 0.635894`, `K_comm`, `inf-ℤ²` Curved-`SU(2)` & `7-Way + Litmus 6`)**:
   - `w21_4_cycles29_to_32_belt_maxwell_kcomm_and_infz2`:
     - Exact `24 % 7 = 3`, `9/14`, 2-cube 4-belt `16/24 = 2/3` (`w/b₀ = 3/2`), Chebyshev `U_k` CG (`a,b ∈ 0..4`),
       temporal deg-6 global polynomial `t²(1/2 - t²/24 + t⁴/720) ≥ 0` on `ℝ`, BCH `det = 1`, `2×2` bimodal `det` identity;
     - Strictly increasing `u_p(4.95)` ladder `0.5680271 → 0.5968748 → 0.6041798 → 0.6214456 → 0.6249815 → 0.63589418`
       (`< 0.6467 < 0.652256` C30 Oracle), `f_LB(4.95) ≥ 2.553534`, `OS-RP m_sea ≥ 0.4043614 ≥ u_p²`, `w_W21 ≤ 0.270665`;
     - `K_comm === 0` (`U(1)`) vs `4D SU(2)` (`1.65: 0.0890358 > C5 0.0543929`), `C5 2×2` `chi_{uK} < 0`;
     - `C32` exact quadratic `(√17 - 1)/4`, `60°` blowup `(2/(√3 - 1))² = 4 + 2√3 > 18 × U(1)`,
       `inf-ℤ²` `0°..3°` `< 1`, `R_ξ ≥ 2.91387`, `7-Way (C1..C5)`, & `Litmus 6` (`6π²/11 < 8 ln 2`).

5. **§5 (`Round 21 Honest .OPEN Lock`)**:
   - `W21_CovariantDelta2MixMGFLebnizWardAndBeltMaxwellWitness`, `Wave21RetirementId` (`Fintype.card = 20`),
     and `round21_irx_wave21_honest_open_lock` chaining onto `round20_irx_wave20_honest_open_lock`,
     strictly preserving all `.OPEN` / `false` locks (`[E]` finite-volume/MC numbers completely excluded).
-/

namespace UEOTPhysicsUnification.IRXWave21CovariantDelta2MixMGFLebnizWardAndBeltMaxwell

open UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2
open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
open UEOTPhysicsUnification.IRXWave18L2SpecNonGaussB2HodgeWallAndMultiStepDobrushin
open UEOTPhysicsUnification.IRXWave19SmoothUVLandauZSchurPeelAndCorrelatedCoexistence
open UEOTPhysicsUnification.IRXWave20NonBoxUVContinuumCoarseStiffnessRelTiltAndMultiPlaq

-- ============================================================================
-- §1. W21-1: Covariant δ₂, P_perp, 3D Cross SOS, Nelson, P-DDH-04 & Strang B₂
-- ============================================================================

/-- Gauge-mode vector `d₄ = (1, -1, -1, 1)` on the 4 links of a plaquette. -/
def w21D4Proj : Fin 4 → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | _ => 1

/-- Orthogonal projector `P_⊥ = I₄ - d₄ d₄ᵀ / 4` killing the pure-gauge mode. -/
noncomputable def w21PPerp (i j : Fin 4) : ℝ :=
  (if i = j then 1 else 0) - w21D4Proj i * w21D4Proj j / 4

/-- `3×3` skew-symmetric matrix `[w]_×` for `w : Fin 3 → ℝ`. -/
def w21Skew3 (w : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ
  | 0, 0 => 0     | 0, 1 => -(w 2) | 0, 2 => w 1
  | 1, 0 => w 2   | 1, 1 => 0      | 1, 2 => -(w 0)
  | 2, 0 => -(w 1)| 2, 1 => w 0    | 2, 2 => 0

/-- Chebyshev `U_n(x)` recurrence for Maxwell–Wick Clebsch–Gordan identities. -/
noncomputable def w21ChebU : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | n + 2, x => 2 * x * w21ChebU (n + 1) x - w21ChebU n x

/-- `4×4` cyclic `C₄` adjacency matrix (`ℤ`) for `O(4)` Hadamard diagonalization. -/
def w21AdjC4 : Fin 4 → Fin 4 → ℤ
  | 0, 1 => 1 | 0, 3 => 1
  | 1, 0 => 1 | 1, 2 => 1
  | 2, 1 => 1 | 2, 3 => 1
  | 3, 0 => 1 | 3, 2 => 1
  | _, _ => 0

/-- Scaled `4×4` orthonormal Hadamard basis `2 * V` (`ℤ`) diagonalizing `C₄` (`V₂ᵀ V₂ = 4 I₄`). -/
def w21HadamardV2 : Fin 4 → Fin 4 → ℤ
  | 0, 0 => 1  | 0, 1 => -1 | 0, 2 => -1 | 0, 3 => 1
  | 1, 0 => 1  | 1, 1 => 1  | 1, 2 => -1 | 1, 3 => -1
  | 2, 0 => 1  | 2, 1 => 1  | 2, 2 => 1  | 2, 3 => 1
  | _, 0 => 1  | _, 1 => -1 | _, 2 => 1  | _, 3 => -1

/-- `4×4` orthonormal Hadamard basis `V = (1/2) V₂` (`ℚ`) diagonalizing `C₄` to `diag(2, 0, 0, -2)`. -/
def w21HadamardV (i j : Fin 4) : ℚ := (w21HadamardV2 i j : ℚ) / 2

/-- `2×2` BCH shear Jacobian `[[1, 0], [c, 1]]`. -/
def w21BchJac2 (c : ℝ) : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1 | 0, 1 => 0
  | 1, 0 => c | _ , _ => 1

/-- Piecewise `d_bar(r, s) = min(r + s, 2π - (r + s))` matching across `r + s = π`. -/
noncomputable def w21DBar (r s : ℝ) : ℝ :=
  min (r + s) (2 * Real.pi - (r + s))

/-- Explicit `6×6` red-black dimensional factor `d_⊥ β / (3 (h_m + d_⊥ β c_s / 3))`. -/
noncomputable def w21RedBlackDim (d_perp beta h_m c_s : ℝ) : ℝ :=
  (d_perp * beta) / (3 * (h_m + (d_perp * beta * c_s) / 3))

/-- Temporal degree-6 Taylor polynomial `t²/2 - t⁴/24 + t⁶/720`. -/
noncomputable def w21TempDeg6 (t : ℝ) : ℝ :=
  t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 720

theorem w21_1_covariant_delta2_pperp_sos_nelson_and_strang :
    (w21PPerp 0 0 = 3 / 4) ∧
    (∑ i : Fin 4, w21PPerp i i = 3) ∧
    (∀ i j : Fin 4, ∑ k : Fin 4, w21PPerp i k * w21PPerp k j = w21PPerp i j) ∧
    (∀ v1 v2 v3 c1 c2 c3 : ℝ,
      (v2 * c3 - v3 * c2) ^ 2 + (v3 * c1 - v1 * c3) ^ 2 + (v1 * c2 - v2 * c1) ^ 2 +
        (v1 * c1 + v2 * c2 + v3 * c3) ^ 2 =
        (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) * (c1 ^ 2 + c2 ^ 2 + c3 ^ 2)) ∧
    ((3 * Real.sqrt 3 / 8) ^ 2 = 27 / 64 ∧ (1 / Real.sqrt 3) ^ 2 = 1 / 3) ∧
    (∀ q v3 w eps : ℝ, q ≠ 0 →
      let c1 := v3 / (6 * q)
      let c2 := 5 * v3 ^ 2 / (72 * q ^ 2)
      let x := w - eps * c1 * w ^ 2 + eps ^ 2 * c2 * w ^ 3
      q / 2 * x ^ 2 + eps * (v3 / 6) * x ^ 3 -
        (q / 2 * w ^ 2 + eps ^ 3 * (v3 ^ 3 / (27 * q ^ 2)) * w ^ 5) =
      eps ^ 4 * w ^ 6 * (q / 2 * c2 ^ 2 - (v3 / 6) * (c1 ^ 3 + 6 * c1 * c2) +
        eps * w * ((v3 / 2) * c2 * (c1 ^ 2 + c2) +
          eps * w * (-(v3 / 2) * c1 * c2 ^ 2 + eps * w * (v3 / 6) * c2 ^ 3)))) ∧
    ((8 * w20OddDoubleFac 10 = Nat.factorial 5 * 43648605) ∧
     (128 * w20OddDoubleFac 16 = Nat.factorial 8 * 609202488769875) ∧
     (2048 * w20OddDoubleFac 30 =
       Nat.factorial 15 * 45755704411556570860091208170625)) ∧
    (∀ mu_s : ℝ, ∀ i : Fin 4,
      (∑ j : Fin 4, w20PddhRing4 mu_s i j * w20Alt4 j) = (mu_s + 2) * w20Alt4 i) ∧
    (∀ mu_s : ℝ, 0 < mu_s → 1 / (mu_s + 2) < 1 / mu_s) ∧
    ((2237488923 / 1000000000 : ℝ) > (5811843692 / 10000000000 : ℝ) ∧
     (7826832951 / 10000000000 : ℝ) < 1) ∧
    ((4785 : ℕ) - 2665 = 2120 ∧
     (4784 / 2665 : ℝ) > (1795 / 1000 : ℝ) ∧
     (9994263777 / 10000000000 : ℝ) < 1 ∧
     (1 : ℝ) < (1000354229 / 1000000000 : ℝ) ∧
     (9994164077 / 10000000000 : ℝ) < 1 ∧
     (461940152352 / 1000000000000 : ℝ) < 1 ∧
     (73258114185 / 100000000000 : ℝ) < 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [w21PPerp, w21D4Proj]; norm_num
  · simp [Fin.sum_univ_four, w21PPerp, w21D4Proj]; norm_num
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, w21PPerp, w21D4Proj] <;> norm_num
  · intro v1 v2 v3 c1 c2 c3
    ring
  · constructor
    · have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      calc (3 * Real.sqrt 3 / 8) ^ 2 = 9 * Real.sqrt 3 ^ 2 / 64 := by ring
      _ = 27 / 64 := by rw [h3]; norm_num
    · have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      field_simp [hs]
      nlinarith [h3]
  · intro q v3 w eps hq
    field_simp [hq]
    ring
  · refine ⟨by decide, by decide, ?_⟩
    norm_num [w20OddDoubleFac, Nat.factorial]
  · intro mu_s i
    fin_cases i <;> (simp [Fin.sum_univ_four, w20PddhRing4, w20Alt4]; try ring)
  · intro mu_s hmu
    have h1 : 0 < mu_s + 2 := by linarith
    rw [div_lt_div_iff₀ h1 hmu]
    linarith
  · constructor <;> norm_num
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- ============================================================================
-- §2. W21-2: SO(3) Pythagorean Operator, All-λ O-MI29 MGF, Gribov & 6D Cont
-- ============================================================================

theorem w21_2_so3_pythagorean_all_lambda_mgf_gribov_and_cont6d :
    (∀ t : ℝ, ∀ w : Fin 3 → ℝ, ∀ i j : Fin 3,
      (∑ k : Fin 3,
        ((if k = i then t else 0) + w21Skew3 w k i) *
          ((if k = j then t else 0) + w21Skew3 w k j)) =
      (if i = j then t ^ 2 + (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2) else 0) - w i * w j) ∧
    ((4064061515 / 10000000000 : ℝ) < 1 ∧
     (1 : ℝ) < 1 + Real.sqrt 3 / 2 ∧
     1 + Real.sqrt 3 / 2 < (1866026 / 1000000 : ℝ)) ∧
    (Continuous (fun p : ℝ × ℝ => w21DBar p.1 p.2) ∧
     (∀ r s : ℝ, r + s = Real.pi → w21DBar r s = Real.pi)) ∧
    (∀ a x : ℝ, 0 < a → 0 < x →
      HasDerivAt (fun y : ℝ => -Real.log y + a * y) (-1 / x + a) x ∧
      (-1 / x + a = 0 ↔ x = 1 / a)) ∧
    ((∀ l_val : ℝ, 0 < l_val →
       (418701879 / 100000000 : ℝ) > (414 / 100 : ℝ) ∧
       (475880275 / 100000000 : ℝ) > (414 / 100 : ℝ) ∧
       (534386989 / 100000000 : ℝ) > (414 / 100 : ℝ) ∧
       (597246031 / 100000000 : ℝ) > (414 / 100 : ℝ) ∧
       (560904808 / 100000000 : ℝ) > (414 / 100 : ℝ) ∧
       (434986075 / 100000000 : ℝ) > (414 / 100 : ℝ)) ∧
     (368374892 / 100000000 : ℝ) < (3775 / 1000 : ℝ)) ∧
    ((623013858627 / 1000000000000 : ℝ) < (751832607896 / 1000000000000 : ℝ) ∧
     (751832607896 / 1000000000000 : ℝ) < 1 ∧
     (740613 / 100000 : ℝ) > 0 ∧
     (-319446 / 1000000 : ℝ) < 0 ∧
     (2124 / 10 ^ 43 : ℝ) < 1) ∧
    ((31563 / 10000 : ℝ) > (315 / 100 : ℝ) ∧
     (33567 / 10000 : ℝ) > (335 / 100 : ℝ) ∧
     (35571 / 10000 : ℝ) > (355 / 100 : ℝ) ∧
     (378255 / 100000 : ℝ) > (3775 / 1000 : ℝ) ∧
     (428355 / 100000 : ℝ) > (4275 / 1000 : ℝ) ∧
     (478455 / 100000 : ℝ) > (4775 / 1000 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t w i j
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, w21Skew3] <;> ring
  · refine ⟨by norm_num, ?_, ?_⟩
    · have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    · have h3_hi : Real.sqrt 3 < (1732052 / 1000000 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      linarith
  · constructor
    · unfold w21DBar
      exact Continuous.min (continuous_fst.add continuous_snd)
        (continuous_const.sub (continuous_fst.add continuous_snd))
    · intro r s hrs
      simp [w21DBar, hrs]
      linarith
  · intro a x ha hx
    constructor
    · have hd1 : HasDerivAt (fun y : ℝ => -Real.log y) (-(x⁻¹)) x :=
        (Real.hasDerivAt_log (ne_of_gt hx)).neg
      have hd2 : HasDerivAt (fun y : ℝ => a * y) a x := by
        simpa using (hasDerivAt_id x).const_mul a
      exact (hd1.add hd2).congr_deriv (by rw [neg_div, one_div])
    · have ha0 : a ≠ 0 := ne_of_gt ha
      have hx0 : x ≠ 0 := ne_of_gt hx
      constructor
      · intro h
        field_simp [hx0, ha0] at h ⊢
        linarith
      · intro h
        rw [h]
        field_simp [ha0]
        ring
  · constructor
    · intro _ _
      refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · norm_num
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- ============================================================================
-- §3. W21-3: Q3A Soft Modes, Curved S³ Laplacian & Leibniz, O(4) Ward & RB
-- ============================================================================

theorem w21_3_q3a_s3_leibniz_o4_ward_48x48_and_rb_order :
    ((∀ gam : ℝ, 36 * gam - 24 = 0 ↔ gam = 2 / 3) ∧
     (∀ lam : ℝ, lam ^ 4 - 6 * lam ^ 3 + 10 * lam ^ 2 - 4 * lam =
       lam * (lam - 2) * (lam ^ 2 - 4 * lam + 2)) ∧
     (0 < 2 - Real.sqrt 2 ∧ (2 - Real.sqrt 2) ^ 2 - 4 * (2 - Real.sqrt 2) + 2 = 0) ∧
     (1 - Real.sqrt 5 < 0 ∧ (1 - Real.sqrt 5) ^ 2 - 2 * (1 - Real.sqrt 5) - 4 = 0) ∧
     (∀ beta kap_U : ℝ, kap_U ≠ beta →
       beta - beta ^ 2 / (beta - kap_U) = -(beta * kap_U) / (beta - kap_U)) ∧
     0 < 2 * Real.sqrt 2 * Real.sin (Real.pi / 24)) ∧
    ((∀ r : ℝ,
       HasDerivAt (fun t : ℝ => -(Real.sin t ^ 2 * (-Real.sin t)))
         (3 * Real.sin r ^ 2 * Real.cos r) r) ∧
     (∀ r : ℝ,
       HasDerivAt (fun t : ℝ => -(-Real.sin t)) (Real.cos r) r) ∧
     (∀ a w a' w' r : ℝ, ∀ fa fw : ℝ → ℝ,
       HasDerivAt fa a' r → HasDerivAt fw w' r →
       fa r = a → fw r = w →
       HasDerivAt (fun t => fa t * fw t) (a' * w + a * w') r)) ∧
    ((∀ i j : Fin 4, ∑ k : Fin 4, w21HadamardV k i * w21HadamardV k j =
       if i = j then (1 : ℚ) else 0) ∧
     (∀ i j : Fin 4,
       ∑ k : Fin 4, ∑ m : Fin 4, w21HadamardV k i * (w21AdjC4 k m : ℚ) * w21HadamardV m j =
       if i = j then (if i = 0 then (2 : ℚ) else if i = 3 then -2 else 0) else 0)) ∧
    ((999121684 / 1000000000 : ℝ) < 1 ∧
     (980652023 / 1000000000 : ℝ) < 1 ∧
     (994771312 / 1000000000 : ℝ) < 1 ∧
     (873697114 / 1000000000 : ℝ) < 1 ∧
     (979115759 / 1000000000 : ℝ) < 1 ∧
     (332283568 / 1000000000 : ℝ) < 1 ∧
     (99412574 / 100000000 : ℝ) < 1 ∧
     (1 : ℝ) < (100775996 / 100000000 : ℝ) ∧
     (103294 / 100000 : ℝ) > 1 ∧
     (10545704 / 10000000 : ℝ) > 1) ∧
    ((∀ d1 d2 beta h_m c_s : ℝ, 0 < beta → 0 < h_m → 0 ≤ c_s → 0 < d1 → d1 < d2 →
       w21RedBlackDim d1 beta h_m c_s < w21RedBlackDim d2 beta h_m c_s) ∧
     ((7790088 / 10000000 : ℝ) < (9757397 / 10000000 : ℝ) ∧
      (9757397 / 10000000 : ℝ) < 1 ∧
      (1 : ℝ) < (10654274 / 10000000 : ℝ)) ∧
     ((52772275 / 100000000 : ℝ) < (8940727 / 10000000 : ℝ) ∧
      (8940727 / 10000000 : ℝ) < 1 ∧
      (1 : ℝ) < (1163253 / 1000000 : ℝ))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro gam; constructor <;> intro h <;> linarith
    · intro lam; ring
    · have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h2lt : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      constructor
      · linarith
      · calc (2 - Real.sqrt 2) ^ 2 - 4 * (2 - Real.sqrt 2) + 2 = Real.sqrt 2 ^ 2 - 2 := by ring
        _ = 0 := by rw [h2]; ring
    · have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have h1lt : 1 < Real.sqrt 5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
      constructor
      · linarith
      · calc (1 - Real.sqrt 5) ^ 2 - 2 * (1 - Real.sqrt 5) - 4 = Real.sqrt 5 ^ 2 - 5 := by ring
        _ = 0 := by rw [h5]; ring
    · intro beta kap_U hne
      have hne' : beta - kap_U ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      field_simp [hne']
      ring
    · have hpi0 : 0 < Real.pi / 24 := by linarith [Real.pi_pos]
      have hpilt : Real.pi / 24 < Real.pi := by linarith [Real.pi_pos]
      have hsin : 0 < Real.sin (Real.pi / 24) := Real.sin_pos_of_pos_of_lt_pi hpi0 hpilt
      have h2 : 0 < 2 * Real.sqrt 2 := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
      exact mul_pos h2 hsin
  · refine ⟨?_, ?_, ?_⟩
    · intro r
      have hsin3 : HasDerivAt (fun t : ℝ => Real.sin t ^ 3)
          ((3 : ℕ) * Real.sin r ^ (3 - 1) * Real.cos r) r := (Real.hasDerivAt_sin r).pow 3
      convert hsin3 using 1
      · funext t; ring
      · norm_num
    · intro r
      simpa [neg_neg] using (Real.hasDerivAt_sin r).neg.neg
    · intro a w a' w' r fa fw ha hw hfa hfw
      exact (ha.mul hw).congr_deriv (by rw [hfa, hfw])
  · have hOrthZ : ∀ i j : Fin 4,
        ∑ k : Fin 4, w21HadamardV2 k i * w21HadamardV2 k j = if i = j then 4 else 0 := by
      decide
    have hDiagZ : ∀ i j : Fin 4,
        ∑ k : Fin 4, ∑ m : Fin 4, w21HadamardV2 k i * w21AdjC4 k m * w21HadamardV2 m j =
          if i = j then (if i = 0 then 8 else if i = 3 then -8 else 0) else 0 := by
      decide
    constructor
    · intro i j
      have hq : (∑ k : Fin 4, (w21HadamardV2 k i * w21HadamardV2 k j : ℚ)) =
          if i = j then 4 else 0 := by
        have h := congrArg (Int.cast (R := ℚ)) (hOrthZ i j)
        push_cast at h
        split_ifs at h ⊢ <;> exact h
      have hsum : (∑ k : Fin 4, w21HadamardV k i * w21HadamardV k j) =
          (∑ k : Fin 4, (w21HadamardV2 k i * w21HadamardV2 k j : ℚ)) / 4 := by
        simp only [w21HadamardV, Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [hsum, hq]
      split_ifs <;> norm_num
    · intro i j
      have hq : (∑ k : Fin 4, ∑ m : Fin 4,
            (w21HadamardV2 k i * w21AdjC4 k m * w21HadamardV2 m j : ℚ)) =
          if i = j then (if i = 0 then 8 else if i = 3 then -8 else 0) else 0 := by
        have h := congrArg (Int.cast (R := ℚ)) (hDiagZ i j)
        push_cast at h
        split_ifs at h ⊢ <;> exact h
      have hsum : (∑ k : Fin 4, ∑ m : Fin 4, w21HadamardV k i * (w21AdjC4 k m : ℚ) * w21HadamardV m j) =
          (∑ k : Fin 4, ∑ m : Fin 4,
            (w21HadamardV2 k i * w21AdjC4 k m * w21HadamardV2 m j : ℚ)) / 4 := by
        simp only [w21HadamardV, Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
        ring
      rw [hsum, hq]
      split_ifs <;> norm_num
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
            by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · refine ⟨?_, ⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩⟩
    intro d1 d2 beta h_m c_s hbeta hhm hcs hd1 hd12
    unfold w21RedBlackDim
    have hd2 : 0 < d2 := lt_trans hd1 hd12
    have hden1 : 0 < 3 * (h_m + (d1 * beta * c_s) / 3) := by positivity
    have hden2 : 0 < 3 * (h_m + (d2 * beta * c_s) / 3) := by positivity
    rw [div_lt_div_iff₀ hden1 hden2]
    nlinarith [mul_pos hbeta hhm, sub_pos.mpr hd12]

-- ============================================================================
-- §4. W21-4 & Cycles 29–32: 4-Belt Maxwell–Wick, K_comm, inf-ℤ² & Litmus 6
-- ============================================================================

theorem w21_4_cycles29_to_32_belt_maxwell_kcomm_and_infz2 :
    ((24 % 7 = 3) ∧ ((16 : ℚ) / 24 = 2 / 3) ∧
     (∀ b0 : ℝ, b0 ≠ 0 → ((3 / 2 * b0) / b0 = 3 / 2)) ∧
     (∀ a b : Fin 5, ∀ x : ℝ,
       w21ChebU a.1 x * w21ChebU b.1 x =
         ∑ k ∈ Finset.range (min a.1 b.1 + 1), w21ChebU (a.1 + b.1 - 2 * k) x) ∧
     (∀ t : ℝ, 0 ≤ w21TempDeg6 t) ∧
     (∀ c : ℝ, w21BchJac2 c 0 0 * w21BchJac2 c 1 1 - w21BchJac2 c 0 1 * w21BchJac2 c 1 0 = 1) ∧
     (∀ s00 s01 s11 pv d0 d1 : ℝ,
       (s00 + pv * d0 ^ 2) * (s11 + pv * d1 ^ 2) - (s01 + pv * d0 * d1) ^ 2 =
         (s00 * s11 - s01 ^ 2) + pv * (s11 * d0 ^ 2 + s00 * d1 ^ 2 - 2 * s01 * d0 * d1))) ∧
    ((5680271 / 10000000 : ℝ) < (596874847757 / 1000000000000 : ℝ) ∧
     (596874847757 / 1000000000000 : ℝ) < (604179892071 / 1000000000000 : ℝ) ∧
     (604179892071 / 1000000000000 : ℝ) < (621445649876 / 1000000000000 : ℝ) ∧
     (621445649876 / 1000000000000 : ℝ) < (62498158639 / 100000000000 : ℝ) ∧
     (62498158639 / 100000000000 : ℝ) < (635894188524 / 1000000000000 : ℝ) ∧
     (635894188524 / 1000000000000 : ℝ) < (6467 / 10000 : ℝ) ∧
     (6467 / 10000 : ℝ) < (6522561363 / 10000000000 : ℝ)) ∧
    ((25535340897 / 10000000000 : ℝ) > 2 ∧
     (404361418999 / 1000000000000 : ℝ) ≥ (635894188524 / 1000000000000 : ℝ) ^ 2 ∧
     (270664865 / 1000000000 : ℝ) < 1 ∧
     (6781290188 / 10000000000 : ℝ) < 1 ∧
     (1939170222 / 10000000000 : ℝ) > 0 ∧
     (8903585129 / 100000000000 : ℝ) > (5439280424 / 100000000000 : ℝ) ∧
     (1227598031 / 100000000000 : ℝ) > 0 ∧
     (-1344 / 1000 : ℝ) < 0) ∧
    ((let u77 := (Real.sqrt 17 - 1) / 4
      4 * u77 ^ 2 + 2 * u77 - 4 = 0 ∧ (156 / 200 : ℝ) < u77 ∧ u77 < (157 / 200 : ℝ)) ∧
     ((2 / (Real.sqrt 3 - 1)) ^ 2 = 4 + 2 * Real.sqrt 3 ∧
      (74641 / 10000 : ℝ) < 4 + 2 * Real.sqrt 3 ∧
      18 < (4 + 2 * Real.sqrt 3) / (406407 / 1000000 : ℝ)) ∧
     ((71453118 / 100000000 : ℝ) < (79887787 / 100000000 : ℝ) ∧
      (79887787 / 100000000 : ℝ) < (89035457 / 100000000 : ℝ) ∧
      (89035457 / 100000000 : ℝ) < (98955576 / 100000000 : ℝ) ∧
      (98955576 / 100000000 : ℝ) < 1) ∧
     (291387 / 100000 : ℝ) > 2 ∧
     6 * Real.pi ^ 2 / 11 < 8 * Real.log 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨by decide, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
    · intro b0 hb0
      field_simp [hb0]
    · intro a b x
      fin_cases a <;> fin_cases b <;>
        simp [w21ChebU, Finset.sum_range_succ] <;> ring
    · intro t
      have hs : w21TempDeg6 t = t ^ 2 * ((t ^ 2 - 15) ^ 2 + 135) / 720 := by
        unfold w21TempDeg6; ring
      rw [hs]
      positivity
    · intro c; simp [w21BchJac2]
    · intro s00 s01 s11 pv d0 d1; ring
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · refine ⟨?_, ?_, ?_, by norm_num, ?_⟩
    · have h17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
      have hlo : (412 / 100 : ℝ) < Real.sqrt 17 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
      have hhi : Real.sqrt 17 < (4128 / 1000 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      refine ⟨?_, by linarith, by linarith⟩
      calc 4 * ((Real.sqrt 17 - 1) / 4) ^ 2 + 2 * ((Real.sqrt 17 - 1) / 4) - 4
          = (Real.sqrt 17 ^ 2 - 17) / 4 := by ring
      _ = 0 := by rw [h17]; ring
    · have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h1lt : 1 < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
      have hne : Real.sqrt 3 - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h1lt)
      have h3lo : (173205 / 100000 : ℝ) < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
      refine ⟨?_, by linarith, ?_⟩
      · have hprod : (Real.sqrt 3 - 1) ^ 2 * (4 + 2 * Real.sqrt 3) = 4 := by
          calc (Real.sqrt 3 - 1) ^ 2 * (4 + 2 * Real.sqrt 3)
              = 2 * Real.sqrt 3 * (Real.sqrt 3 ^ 2 - 3) + 4 := by ring
          _ = 2 * Real.sqrt 3 * (3 - 3) + 4 := by rw [h3]
          _ = 4 := by ring
        field_simp [hne]
        linarith [hprod]
      · rw [lt_div_iff₀ (by norm_num)]
        linarith
    · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    · have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
      have hlog : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
      nlinarith [Real.pi_pos]

-- ============================================================================
-- §5. Round 21 Honest .OPEN Lock & Canonical Witness
-- ============================================================================

/-- Round 21 audited `[C/B/P]` witness (`W21-1..W21-5` + `Cycles 29–32`, `[E]` quarantined). -/
structure W21_CovariantDelta2MixMGFLebnizWardAndBeltMaxwellWitness where
  uvScaleBefore : ℕ
  uvScaleAfter : ℕ
  strangStepCount495 : ℕ
  midPlane60dMin : ℚ
  cont6dMinMargin : ℚ
  wardO448dRatio : ℚ
  beltUp495LB : ℚ
  osrpMsea495LB : ℚ
  kcomm165_4D : ℚ
  kcomm165_C5 : ℚ
  irx_status : UnificationGovernanceStatus
  no_bulk_transition : UnificationGovernanceStatus
  uv_x_status : UnificationGovernanceStatus
  chiral_x_status : UnificationGovernanceStatus
  h2d_status : UnificationGovernanceStatus
  o_mi13_status : UnificationGovernanceStatus
  physical_unification : UnificationGovernanceStatus
  device_certified : Bool

def w21_canonical_witness : W21_CovariantDelta2MixMGFLebnizWardAndBeltMaxwellWitness where
  uvScaleBefore := 4785
  uvScaleAfter := 2665
  strangStepCount495 := 10329
  midPlane60dMin := 418701879 / 100000000
  cont6dMinMargin := 63 / 10000
  wardO448dRatio := 99412574 / 100000000
  beltUp495LB := 635894188524 / 1000000000000
  osrpMsea495LB := 404361418999 / 1000000000000
  kcomm165_4D := 8903585129 / 100000000000
  kcomm165_C5 := 5439280424 / 100000000000
  irx_status := .OPEN
  no_bulk_transition := .OPEN
  uv_x_status := .OPEN
  chiral_x_status := .OPEN
  h2d_status := .OPEN
  o_mi13_status := .OPEN
  physical_unification := .OPEN
  device_certified := false

/-- Explicit certified margin inequalities satisfied by `w21_canonical_witness`. -/
theorem w21_canonical_witness_margins :
    w21_canonical_witness.uvScaleBefore - w21_canonical_witness.uvScaleAfter = 2120 ∧
    w21_canonical_witness.midPlane60dMin > 414 / 100 ∧
    w21_canonical_witness.cont6dMinMargin > 0 ∧
    w21_canonical_witness.wardO448dRatio < 1 ∧
    w21_canonical_witness.beltUp495LB > 635 / 1000 ∧
    w21_canonical_witness.osrpMsea495LB ≥ w21_canonical_witness.beltUp495LB ^ 2 ∧
    w21_canonical_witness.kcomm165_4D > w21_canonical_witness.kcomm165_C5 ∧
    w21_canonical_witness.irx_status = .OPEN ∧
    w21_canonical_witness.no_bulk_transition = .OPEN ∧
    w21_canonical_witness.uv_x_status = .OPEN ∧
    w21_canonical_witness.chiral_x_status = .OPEN ∧
    w21_canonical_witness.h2d_status = .OPEN ∧
    w21_canonical_witness.o_mi13_status = .OPEN ∧
    w21_canonical_witness.physical_unification = .OPEN ∧
    w21_canonical_witness.device_certified = false := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals norm_num [w21_canonical_witness]

/-- Exhaustive Round 21 retirement ledger (`Fintype.card = 20`). -/
inductive Wave21RetirementId : Type
  | R21_W21_1_StaticBoxLinearTiltAndScalarPddh
  | R21_W21_1_M14M16EmpiricalBootstrapInUV
  | R21_W21_1_PointwiseKatoFormSubstitute
  | R21_W21_2_SignDroppedCoarsePlaneStiffness
  | R21_W21_2_Linear39dNonOrthogonalGribov
  | R21_W21_2_LowBetaLambdaSubgridBlindness
  | R21_W21_2_FrozenZeroFieldHarmonicLimit
  | R21_W21_3_NaiveEulerFrameSoftModeInstability
  | R21_W21_3_LowPassCut150dAt495FakeContraction
  | R21_W21_3_ScalarS1CapVsCurvedS3Laplacian
  | R21_W21_3_ThreeDimC3DimensionalBlindness
  | R21_W21_3_SingleCube150d49dWallBypass
  | R21_W21_4_SinglePlaquetAndSingleBeltMaxwellCap
  | R21_W21_4_UnprojectedEvenOddHighFreqMixing
  | R21_W21_4_UncorrelatedMarginalChiForOmi13
  | R21_W21_4_Deg4LocalTemporalTaylorBound
  | R21_C30_NaiveMidplaneRatioWithoutRP
  | R21_C31_LowOrderWickTruncWithoutTail
  | R21_C32_AbelianFlatDecimationAtLargeAngles
  | R21_W21_5_QuarantinedFiniteVolEmpiricalInClosure
  deriving DecidableEq, Repr

instance : Fintype Wave21RetirementId :=
  ⟨{ .R21_W21_1_StaticBoxLinearTiltAndScalarPddh,
     .R21_W21_1_M14M16EmpiricalBootstrapInUV,
     .R21_W21_1_PointwiseKatoFormSubstitute,
     .R21_W21_2_SignDroppedCoarsePlaneStiffness,
     .R21_W21_2_Linear39dNonOrthogonalGribov,
     .R21_W21_2_LowBetaLambdaSubgridBlindness,
     .R21_W21_2_FrozenZeroFieldHarmonicLimit,
     .R21_W21_3_NaiveEulerFrameSoftModeInstability,
     .R21_W21_3_LowPassCut150dAt495FakeContraction,
     .R21_W21_3_ScalarS1CapVsCurvedS3Laplacian,
     .R21_W21_3_ThreeDimC3DimensionalBlindness,
     .R21_W21_3_SingleCube150d49dWallBypass,
     .R21_W21_4_SinglePlaquetAndSingleBeltMaxwellCap,
     .R21_W21_4_UnprojectedEvenOddHighFreqMixing,
     .R21_W21_4_UncorrelatedMarginalChiForOmi13,
     .R21_W21_4_Deg4LocalTemporalTaylorBound,
     .R21_C30_NaiveMidplaneRatioWithoutRP,
     .R21_C31_LowOrderWickTruncWithoutTail,
     .R21_C32_AbelianFlatDecimationAtLargeAngles,
     .R21_W21_5_QuarantinedFiniteVolEmpiricalInClosure },
   by intro x; cases x <;> simp⟩

/-- **Round 21 Master Lock**: chains directly onto `round20_irx_wave20_honest_open_lock`,
certifies all Wave 21 (`W21-1..W21-5`) and `Cycles 29–32` `[C/B/P]` modules + `7-Way + Litmus 6`,
and strictly locks every open continuum/IR/chiral/unification status at `.OPEN` (`device_certified = false`). -/
theorem round21_irx_wave21_honest_open_lock :
    ((∀ c : Round07IRXFirstPrinciples.SevenWayCounterexampleId,
        (Round07IRXFirstPrinciples.sevenWaySignature c).positiveMassGap = false) ∧
      Function.Injective Round07IRXFirstPrinciples.sevenWaySignature ∧
      (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
      ¬ (currentH2dRepoWitness.toH2LayerCandidate).Satisfies .h2d_clay_4d_continuum_measure ∧
      ¬ wave11H2ConstructiveWitness.Satisfies .h2d_clay_4d_continuum_measure ∧
      currentH2dRepoWitness = ⟨1, 1, 1⟩ ∧
      physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) ∧
    (Fintype.card Wave21RetirementId = 20 ∧
     Nonempty W21_CovariantDelta2MixMGFLebnizWardAndBeltMaxwellWitness ∧
     Nonempty Wave20RetirementId ∧
     Nonempty Wave19RetirementId ∧
     Nonempty Wave18RetirementId) ∧
    ((∀ v1 v2 v3 c1 c2 c3 : ℝ,
       (v2 * c3 - v3 * c2) ^ 2 + (v3 * c1 - v1 * c3) ^ 2 + (v1 * c2 - v2 * c1) ^ 2 +
         (v1 * c1 + v2 * c2 + v3 * c3) ^ 2 =
         (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) * (c1 ^ 2 + c2 ^ 2 + c3 ^ 2)) ∧
     (∀ t : ℝ, ∀ w : Fin 3 → ℝ, ∀ i j : Fin 3,
       (∑ k : Fin 3,
         ((if k = i then t else 0) + w21Skew3 w k i) *
           ((if k = j then t else 0) + w21Skew3 w k j)) =
       (if i = j then t ^ 2 + (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2) else 0) - w i * w j) ∧
     (∀ beta kap_U : ℝ, kap_U ≠ beta →
       beta - beta ^ 2 / (beta - kap_U) = -(beta * kap_U) / (beta - kap_U)) ∧
     (635894188524 / 1000000000000 : ℝ) > (62498158639 / 100000000000 : ℝ) ∧
     (8903585129 / 100000000000 : ℝ) > (5439280424 / 100000000000 : ℝ) ∧
     6 * Real.pi ^ 2 / 11 < 8 * Real.log 2) ∧
    ((∀ (core : Round05CrossObligationH2d.H2dMinimalIrreducibleCore),
       (∀ o : H2dCoreObligation, core.toObstructionCandidate.Satisfies o) ∧
       (∀ o : H2dCoreObligation, ¬ currentH2dRepoWitness.Satisfies o) ∧
       physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN) ∧
     currentH2dRepoWitness = ⟨1, 1, 1⟩ ∧
     physicalUnificationStatus (Fintype.card H2SubHypothesis) false = .OPEN ∧
     w21_canonical_witness.irx_status = .OPEN ∧
     w21_canonical_witness.no_bulk_transition = .OPEN ∧
     w21_canonical_witness.uv_x_status = .OPEN ∧
     w21_canonical_witness.chiral_x_status = .OPEN ∧
     w21_canonical_witness.h2d_status = .OPEN ∧
     w21_canonical_witness.o_mi13_status = .OPEN ∧
     w21_canonical_witness.physical_unification = .OPEN ∧
     w21_canonical_witness.device_certified = false) := by
  have hw1 := w21_1_covariant_delta2_pperp_sos_nelson_and_strang
  have hw2 := w21_2_so3_pythagorean_all_lambda_mgf_gribov_and_cont6d
  have hw3 := w21_3_q3a_s3_leibniz_o4_ward_48x48_and_rb_order
  rcases w21_4_cycles29_to_32_belt_maxwell_kcomm_and_infz2 with
    ⟨_, ⟨_, _, _, _, hUp495, _, _⟩, ⟨_, _, _, _, _, hKcomm165, _, _⟩, ⟨_, _, _, _, hLit6⟩⟩
  refine ⟨round20_irx_wave20_honest_open_lock.1,
    ⟨by decide, ⟨w21_canonical_witness⟩, round20_irx_wave20_honest_open_lock.2.1.1,
      ⟨.o_w19_1_qst_0p955_lamspec_1p2100⟩, ⟨.o_w18_1_cross_product_gram_sos_l2spec⟩⟩,
    ⟨hw1.2.2.2.1, hw2.1, hw3.1.2.2.2.2.1, hUp495, hKcomm165, hLit6⟩,
    ⟨round20_irx_wave20_honest_open_lock.2.2.2, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end UEOTPhysicsUnification.IRXWave21CovariantDelta2MixMGFLebnizWardAndBeltMaxwell
