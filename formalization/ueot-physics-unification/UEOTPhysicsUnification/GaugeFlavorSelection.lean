import UEOTQM.Selector
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Gauge-Parent Diophantine Classification, Efficiency-Free `R_τ` Exclusion & Rank-One Flavor Closure

Closes the open gauge/flavor selection questions of Chapter 71 and `cross_domain/matter`:

1. **Complete `ℕ³` Classification of `SU(n_c)_C × SU(3)_L × U(1)_X` Parent Spectra**:
   Under `n_c ≥ 3`, `n_f ≥ 1`, `k ≤ n_f`, cubic `SU(3)_L³` anomaly cancellation
   `2 n_c k + n_f = n_c n_f`, color `SU(n_c)` asymptotic freedom `6 n_f < 11 n_c`, and
   `SU(3)_L` asymptotic freedom `2 n_f (n_c + 1) < 63`, the *entire* solution set in `ℕ³`
   is **exhausted** by `(3, 3, 1)` and `(5, 5, 2)` (`uv_331_complete_classification`).
2. **Multiscale `SU(3)_L → SU(2)_L` Uniqueness of `(3, 3, 1)`**:
   Imposing infrared chiral `SU(2)_L` one-loop asymptotic freedom below the `3-3-1` breaking
   scale (`2 n_f (n_c + 1) + 1 < 44`, i.e., `b_2(SU(2)_L) = 22/3 - n_f(n_c+1)/3 - 1/6 > 0`)
   eliminates `(5, 5, 2)` (`b_2 = -17/6 < 0`) and **uniquely selects `(3, 3, 1)`** across all `ℕ³`.
3. **ABJ Pion-to-Diphoton Degeneracy & Efficiency-Free `R_τ` Exclusion of Light 5-Color Quarks**:
   Proves that `N (Q_u^2 - Q_d^2) = 1` for ALL `N ≠ 0` under `Q_u = (N+1)/(2N), Q_d = -(N-1)/(2N)`,
   while lepton-only unitarity `R_τ = (1 - B_e - B_μ)/B_e` strictly excludes unbroken `N = 5`
   light `(u, d, s)` quarks without any hadronic detector efficiency parameter `E_5`.
4. **Rank-One `ΔF = 2` Complex Wilson Coefficient Closure Identity**:
   Proves `|C_bd| + |C_bs| = η |u_b|^2 (1 - |u_b|^2) ≤ η / 4`, real nonnegativity of the cyclic
   triple `C_bd * C_sb * C_ds`, and the exact cross-sector phase/magnitude lock
   `C_ds = ((1 / |u_b|^2) - 1) * conj(C_bd) * C_bs / (|C_bd| + |C_bs|)`.
-/

namespace UEOTPhysicsUnification.GaugeFlavorSelection

/-! ## 1. Complete `ℕ³` Classification of `(3,3,1)` and `(5,5,2)` & Multiscale `SU(2)_L` Uniqueness -/

theorem uv_331_finite_bounds
    (nc nf : ℕ)
    (hcolor : 3 ≤ nc)
    (hfamilies : 0 < nf)
    (huvL : 2 * (nf * (nc + 1)) < 63) :
    nc ≤ 30 ∧ nf ≤ 7 := by
  have hnf1 : 1 ≤ nf := by omega
  have h1 : nc + 1 ≤ nf * (nc + 1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (nc + 1) hnf1
  have h4 : 4 ≤ nc + 1 := by omega
  have h2 : nf * 4 ≤ nf * (nc + 1) := Nat.mul_le_mul_left nf h4
  constructor <;> omega

set_option maxHeartbeats 1600000 in
/-- **Complete UV `SU(n_c)_C × SU(3)_L` Classification Theorem**:
Across ALL natural numbers `(nc, nf, k)`, cubic anomaly cancellation plus UV color and weak-triplet
asymptotic freedom admit **if and only if** `(nc, nf, k) = (3, 3, 1)` or `(nc, nf, k) = (5, 5, 2)`. -/
theorem uv_331_complete_classification
    (nc nf k : ℕ) :
    (3 ≤ nc ∧ 0 < nf ∧ k ≤ nf ∧
      2 * nc * k + nf = nc * nf ∧
      6 * nf < 11 * nc ∧
      2 * (nf * (nc + 1)) < 63) ↔
      ((nc = 3 ∧ nf = 3 ∧ k = 1) ∨ (nc = 5 ∧ nf = 5 ∧ k = 2)) := by
  constructor
  · rintro ⟨hcolor, hfam, hq, hanom, hcolAF, huvL⟩
    obtain ⟨hnc_ub, hnf_ub⟩ := uv_331_finite_bounds nc nf hcolor hfam huvL
    interval_cases nc <;> interval_cases nf <;> omega
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> omega

/-- **Multiscale `SU(3)_L → SU(2)_L` Uniqueness Theorem**:
Requiring that the chiral weak doublets `n_doublets = nf * (nc + 1)` also preserve `SU(2)_L`
asymptotic freedom below the `SU(3)_L` breaking scale (`2 * nf * (nc + 1) + 1 < 44`,
corresponding to `b_2 = 22/3 - nf*(nc+1)/3 - 1/6 > 0` with one Higgs doublet) uniquely
eliminates `(5, 5, 2)` and selects `(3, 3, 1)` over all `ℕ³`. -/
theorem multiscale_su3L_to_su2L_uniquely_selects_331
    (nc nf k : ℕ) :
    (3 ≤ nc ∧ 0 < nf ∧ k ≤ nf ∧
      2 * nc * k + nf = nc * nf ∧
      6 * nf < 11 * nc ∧
      2 * (nf * (nc + 1)) < 63 ∧
      2 * (nf * (nc + 1)) + 1 < 44) ↔
      (nc = 3 ∧ nf = 3 ∧ k = 1) := by
  constructor
  · rintro ⟨hcolor, hfam, hq, hanom, hcolAF, huvL, hir2⟩
    have hclass := (uv_331_complete_classification nc nf k).mp
      ⟨hcolor, hfam, hq, hanom, hcolAF, huvL⟩
    rcases hclass with h3 | ⟨rfl, rfl, rfl⟩
    · exact h3
    · omega
  · rintro ⟨rfl, rfl, rfl⟩
    omega

/-- Explicit Witten `SU(2)` global anomaly parity check: ANY solution of `2*nc*k + nf = nc*nf`
automatically has an even number of chiral weak doublets `nf * (nc + 1)`, proving algebraically
why Witten's global anomaly alone can never separate `(3,3,1)` from `(5,5,2)`. -/
theorem witten_doublet_count_always_even
    (nc nf k : ℕ) (hanom : 2 * nc * k + nf = nc * nf) :
    Even (nf * (nc + 1)) := by
  have hanomZ : 2 * (nc : ℤ) * (k : ℤ) + (nf : ℤ) = (nc : ℤ) * (nf : ℤ) := by
    exact_mod_cast hanom
  have hevenZ : ((nf * (nc + 1) : ℕ) : ℤ) = 2 * ((nc : ℤ) * (nf : ℤ) - (nc : ℤ) * (k : ℤ)) := by
    push_cast
    linarith
  have hnonneg : 0 ≤ (nc : ℤ) * (nf : ℤ) - (nc : ℤ) * (k : ℤ) := by
    have hck : (0 : ℤ) ≤ (nc : ℤ) * (k : ℤ) :=
      mul_nonneg (Nat.cast_nonneg nc) (Nat.cast_nonneg k)
    have hnf0 : (0 : ℤ) ≤ (nf : ℤ) := Nat.cast_nonneg nf
    linarith
  refine ⟨((nc : ℤ) * (nf : ℤ) - (nc : ℤ) * (k : ℤ)).toNat, ?_⟩
  have htoNat : (((nc : ℤ) * (nf : ℤ) - (nc : ℤ) * (k : ℤ)).toNat : ℤ) =
      (nc : ℤ) * (nf : ℤ) - (nc : ℤ) * (k : ℤ) := Int.toNat_of_nonneg hnonneg
  zify
  linarith

/-! ## 2. ABJ Anomaly `N`-Invariance Trap & Efficiency-Free `R_τ` Exclusion of `(5,5,2)` -/

/-- Exact rational theorem: under baryon-normalized quark charges `Q_u = (N+1)/(2N)` and
`Q_d = -(N-1)/(2N)`, the Adler–Bell–Jackiw `π⁰ → γγ` anomaly factor `N (Q_u^2 - Q_d^2)` is
identically `1` for EVERY nonzero color count `N`! -/
theorem abj_pion_diphoton_invariant (N : ℚ) (hN : N ≠ 0) :
    let Qu : ℚ := (N + 1) / (2 * N)
    let Qd : ℚ := -(N - 1) / (2 * N)
    Qu - Qd = 1 ∧ N * (Qu ^ 2 - Qd ^ 2) = 1 := by
  dsimp only
  constructor <;> field_simp [hN] <;> ring

/-- Contrast with the electromagnetic `e⁺e⁻ → hadrons` tree ratio `R_0(u,d,s) = N*(Q_u^2 + 2*Q_d^2)`:
`R_0 = 2` for `N = 3` vs `R_0 = 17/5` for `N = 5`. -/
theorem r_had_uds_three_vs_five :
    let R0 := fun N : ℚ =>
      let Qu := (N + 1) / (2 * N)
      let Qd := -(N - 1) / (2 * N)
      N * (Qu ^ 2 + 2 * Qd ^ 2)
    R0 3 = 2 ∧ R0 5 = 17 / 5 := by
  norm_num

/-- **Efficiency-Free Semileptonic `R_τ` Unitarity Exclusion of Light 5-Color `(u,d,s)`**:
Using 3σ experimental bounds `B_e ≥ 0.17817 - 3*0.00041 = 17694/100000`,
`B_μ ≥ 0.17393 - 3*0.00040 = 17273/100000`, nuclear/kaon tree bounds
`|V_ud| ≥ 97280/100000`, `|V_us| ≥ 2219/10000`, `S_EW ≥ 1019/1000`, and allowing up to `2%`
nonperturbative subtraction even after dropping the positive perturbative QCD correction,
the experimental upper bound `(1 - B_e - B_μ) / B_e` is strictly below `R_τ(N = 5)` by `> 1.29`. -/
theorem r_tau_unitarity_excludes_five_color :
    let Be_lo : ℚ := 17694 / 100000
    let Bmu_lo : ℚ := 17273 / 100000
    let R_tau_exp_hi : ℚ := (1 - Be_lo - Bmu_lo) / Be_lo
    let Vud_lo : ℚ := 97280 / 100000
    let Vus_lo : ℚ := 2219 / 10000
    let S_EW_lo : ℚ := 1019 / 1000
    let R_tau_N5_lo : ℚ := 5 * (Vud_lo ^ 2 + Vus_lo ^ 2) * S_EW_lo * (98 / 100)
    R_tau_exp_hi + 129 / 100 < R_tau_N5_lo := by
  norm_num

/-! ## 3. Rank-One `ΔF = 2` Neutral-Current Flavor Closure Identities -/

/-- Rank-one `ΔF = 2` Wilson coefficient `C_{ij} = η * (u_i * conj(u_j))^2`. -/
noncomputable def rankOneWilson (η : ℝ) (ui uj : ℂ) : ℂ :=
  (η : ℂ) * (ui * starRingEnd ℂ uj) ^ 2

theorem norm_rankOneWilson {η : ℝ} (hη : 0 ≤ η) (ui uj : ℂ) :
    ‖rankOneWilson η ui uj‖ = η * ‖ui‖ ^ 2 * ‖uj‖ ^ 2 := by
  unfold rankOneWilson
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_conj, Complex.norm_of_nonneg hη]
  ring

/-- Exact parabola identity and universal lower bound `η ≥ 4(|C_bd| + |C_bs|)` under unitarity
`‖u_d‖^2 + ‖u_s‖^2 + ‖u_b‖^2 = 1`. -/
theorem rank_one_bd_bs_sum_bound
    {η : ℝ} (hη : 0 ≤ η) {ud us ub : ℂ}
    (hunit : ‖ud‖ ^ 2 + ‖us‖ ^ 2 + ‖ub‖ ^ 2 = 1) :
    ‖rankOneWilson η ub ud‖ + ‖rankOneWilson η ub us‖ =
      η * ‖ub‖ ^ 2 * (1 - ‖ub‖ ^ 2) ∧
    4 * (‖rankOneWilson η ub ud‖ + ‖rankOneWilson η ub us‖) ≤ η := by
  rw [norm_rankOneWilson hη ub ud, norm_rankOneWilson hη ub us]
  have hsum : ‖ud‖ ^ 2 + ‖us‖ ^ 2 = 1 - ‖ub‖ ^ 2 := by linarith
  have h1 : η * ‖ub‖ ^ 2 * ‖ud‖ ^ 2 + η * ‖ub‖ ^ 2 * ‖us‖ ^ 2 =
      η * ‖ub‖ ^ 2 * (1 - ‖ub‖ ^ 2) := by
    calc
      η * ‖ub‖ ^ 2 * ‖ud‖ ^ 2 + η * ‖ub‖ ^ 2 * ‖us‖ ^ 2 =
          η * ‖ub‖ ^ 2 * (‖ud‖ ^ 2 + ‖us‖ ^ 2) := by ring
      _ = η * ‖ub‖ ^ 2 * (1 - ‖ub‖ ^ 2) := by rw [hsum]
  refine ⟨h1, ?_⟩
  rw [h1]
  have hsq : 0 ≤ η * (2 * ‖ub‖ ^ 2 - 1) ^ 2 := mul_nonneg hη (sq_nonneg _)
  linarith

/-- Cyclic rephasing-invariant product `C_ds * C_sb * C_bd` is purely real and nonnegative
whenever `η ≥ 0`. -/
theorem rank_one_cyclic_real_nonneg
    {η : ℝ} (hη : 0 ≤ η) (ud us ub : ℂ) :
    let cyc := rankOneWilson η ud us * rankOneWilson η us ub * rankOneWilson η ub ud
    cyc.im = 0 ∧ 0 ≤ cyc.re := by
  dsimp only
  unfold rankOneWilson
  have hnorm : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcalc :
      ((η : ℂ) * (ud * starRingEnd ℂ us) ^ 2) *
        ((η : ℂ) * (us * starRingEnd ℂ ub) ^ 2) *
        ((η : ℂ) * (ub * starRingEnd ℂ ud) ^ 2) =
      (((η ^ 3 * ‖ud‖ ^ 4 * ‖us‖ ^ 4 * ‖ub‖ ^ 4 : ℝ)) : ℂ) := by
    calc
      ((η : ℂ) * (ud * starRingEnd ℂ us) ^ 2) *
          ((η : ℂ) * (us * starRingEnd ℂ ub) ^ 2) *
          ((η : ℂ) * (ub * starRingEnd ℂ ud) ^ 2) =
        (η : ℂ) ^ 3 * (ud * starRingEnd ℂ ud) ^ 2 *
          (us * starRingEnd ℂ us) ^ 2 * (ub * starRingEnd ℂ ub) ^ 2 := by ring
      _ = (((η ^ 3 * ‖ud‖ ^ 4 * ‖us‖ ^ 4 * ‖ub‖ ^ 4 : ℝ)) : ℂ) := by
        rw [hnorm ud, hnorm us, hnorm ub]
        push_cast
        ring
  rw [hcalc, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, by positivity⟩

/-- **Exact Cross-Sector Complex Wilson Closure Theorem (`C_ds` from `C_bd` and `C_bs`)**:
Under `η > 0`, `‖u_d‖^2 + ‖u_s‖^2 + ‖u_b‖^2 = 1`, `u_b ≠ 0`, and `‖u_b‖^2 < 1`,
`C_ds` is uniquely locked in BOTH complex phase and magnitude-ratio to `C_bd` and `C_bs`:
`C_ds = ((1 / ‖u_b‖^2) - 1) * conj(C_bd) * C_bs / (‖C_bd‖ + ‖C_bs‖)`. -/
theorem rank_one_wilson_closure
    {η : ℝ} (hη : 0 < η) {ud us ub : ℂ}
    (hunit : ‖ud‖ ^ 2 + ‖us‖ ^ 2 + ‖ub‖ ^ 2 = 1)
    (hub_ne : ub ≠ 0) (hub_lt : ‖ub‖ ^ 2 < 1) :
    let Cbd := rankOneWilson η ub ud
    let Cbs := rankOneWilson η ub us
    let Cds := rankOneWilson η ud us
    Cds = (((1 / ‖ub‖ ^ 2 - 1) / (‖Cbd‖ + ‖Cbs‖) : ℝ) : ℂ) *
      (starRingEnd ℂ Cbd * Cbs) := by
  dsimp only
  have hη0 : 0 ≤ η := le_of_lt hη
  have hsum := (rank_one_bd_bs_sum_bound hη0 hunit).1
  rw [hsum]
  have hub_pos : 0 < ‖ub‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hub_ne)
  have h1sub_pos : 0 < 1 - ‖ub‖ ^ 2 := by linarith
  have hratio : (1 / ‖ub‖ ^ 2 - 1) / (η * ‖ub‖ ^ 2 * (1 - ‖ub‖ ^ 2)) =
      1 / (η * ‖ub‖ ^ 4) := by
    field_simp [ne_of_gt hub_pos, ne_of_gt h1sub_pos, ne_of_gt hη]
  rw [hratio]
  unfold rankOneWilson
  have hconj_ub : (starRingEnd ℂ ub * ub) ^ 2 = (((‖ub‖ ^ 4 : ℝ)) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  simp only [map_mul, map_pow, RingHomCompTriple.comp_apply, RingHom.id_apply,
    Complex.conj_ofReal]
  calc
    (η : ℂ) * (ud * starRingEnd ℂ us) ^ 2 =
        (((1 / (η * ‖ub‖ ^ 4) : ℝ)) : ℂ) *
          ((η : ℂ) ^ 2 * (starRingEnd ℂ ub * ub) ^ 2 * (ud * starRingEnd ℂ us) ^ 2) := by
      rw [hconj_ub]
      have hηC : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hη)
      have hubC1 : (‖ub‖ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (norm_pos_iff.mpr hub_ne))
      push_cast
      field_simp [hηC, hubC1]
    _ = (((1 / (η * ‖ub‖ ^ 4) : ℝ)) : ℂ) *
          (((η : ℂ) * (starRingEnd ℂ ub * ud) ^ 2) *
           ((η : ℂ) * (ub * starRingEnd ℂ us) ^ 2)) := by
      ring

end UEOTPhysicsUnification.GaugeFlavorSelection
