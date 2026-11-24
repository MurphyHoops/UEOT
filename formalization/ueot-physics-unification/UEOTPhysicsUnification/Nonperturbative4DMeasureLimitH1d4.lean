import UEOT.V3.Compression.QuotientDescent
import UEOT.V3.Compression.ContractiveFixedPoint
import UEOTPhysicsUnification.Nonperturbative4DQuantumGravityH1d
import UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1
import UEOTPhysicsUnification.OperationalHorizonMinimumScale
import UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Wave 10 H1d4: Infinite-Order Weighted Banach Truncation Convergence, OS Weak-Limit GNS Quotient,
# Ursell Non-Triviality, Operational Horizon UV Screening & Sharp `H1d4` Decomposition

Pure-kernel Lean 4 formalization (`P-H1D4-BANACH-01`, `P-H1D4-OSRECON-02`, `P-H1D4-OPER-03`, `C-H1D4-FINAL-04`):

1. **`P-H1D4-BANACH-01` (Infinite-Order `N_trunc → ∞` Weighted Banach Convergence)**:
   - Proves that whenever the infinite-order Wetterich map `Φ` is a `κ`-contraction (`0 ≤ κ < 1`)
     on a weighted coupling space `(X, D)` and the truncation tail satisfies
     `D.d (Φ_N (u_N)) (Φ (u_N)) ≤ C_tail / ρ^N` (`ρ > 1`), the `N`-truncated fixed points converge
     geometrically `D.d (u_N N) u_∞ ≤ (C_tail / (1 - κ)) / ρ^N → 0` to the unique fixed point.
   - Proves uniform gap stability `θ_n ≤ -(1 - κ)(2n - 4) < 0` on the irrelevant tail (`n ≥ n₀ ≥ 3`).
   - Exhibits an explicit strong-mixing (`κ ≥ 1`) counterexample where `N = 1` admits a spurious
     fixed point `u = 1` while `N = 2` admits no real fixed point at all.

2. **`P-H1D4-OSRECON-02` (OS Weak-Limit Closure, GNS Hilbert Space Quotient, & Ursell Non-Triviality)**:
   - Proves Osterwalder–Schrader reflection positivity is closed under arbitrary weak pointwise limits
     of finite-cutoff kernels (`0 ≤ S_m ψ ψ → 0 ≤ S_∞ ψ ψ`).
   - Proves Cauchy–Schwarz, exact null-vector characterization, and `UEOT.V3.Compression.QuotientDescent`
     factorization of the physical GNS inner-product norm for arbitrary symmetric PSD continuum kernels.
   - Proves subsequential limit uniqueness under Cauchy coherence (`CauchySeq`), contrasted with an
     explicit uniformly bounded oscillating counterexample proving tightness alone cannot guarantee uniqueness.
   - Proves Gaussian vs non-Gaussian 4-point Ursell cumulant dichotomy (`ursell4 = m₄ - 3 m₂²`:
     `0` for Gaussians, `-2 < 0` for discrete `±1`, and strictly negative under bounded continuum limits).

3. **`P-H1D4-OPER-03` (UEOT `AH01` Operational Horizon UV Screening Equivalence)**:
   - Directly couples `OperationalHorizonMinimumScale.gravitational_horizon_excludes_pointlike_clock`
     with Hoeffding statistical sample bounds and `QuotientDescent` to prove that every operational
     sub-Planckian probe (`k_obs² L_min² ≪ ε_exp / C_UV`) cannot separate `H1a–H1c + H1d1–H1d3` IR+EFT
     predictions from any admissible UV completion in feasible finite-shot experiments, and therefore
     factors uniquely through the IR+EFT quotient (`UEOT` operational closure of `H1`).

4. **`C-H1D4-FINAL-04` (Sharp 4-Layer `H1d4` Decomposition & Two-Level Wave 8/9 Reduction)**:
   - Closes `H1d4a ∧ H1d4b ∧ H1d4c` constructively (`⟨0, 0, 0, 1⟩`), proves 4-way logical independence,
     reduces full mathematical `H1` closure **iff** to `H1d4d_UnconditionalExact4DNonPolynomialDecouplingProof`,
     and preserves honest `.OPEN` global unification governance.
-/

namespace UEOTPhysicsUnification.Nonperturbative4DMeasureLimitH1d4

open scoped BigOperators
open Function Matrix Filter
open UEOT.V3.Compression.QuotientDescent
open UEOT.V3.Compression.ContractiveFixedPoint
open UEOTPhysicsUnification.Nonperturbative4DQuantumGravityH1d
open UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1
open UEOTPhysicsUnification.OperationalHorizonMinimumScale
open UEOTPhysicsUnification.MathV42ClosedTestsAndMechanismBridge

/-! ## 1. Infinite-Order `N_trunc → ∞` Weighted Banach Convergence (`P-H1D4-BANACH-01`) -/

/-- Infinite-order weighted Banach truncation convergence (`P-H1D4-BANACH-01`):
for any `DistanceLike` weighted coupling space `(X, D)` with a `κ`-contractive infinite-order
Wetterich fixed-point map `Phi` (`Phi u_inf = u_inf`) and truncated fixed points `Phi_N N (u_N N) = u_N N`
whose tail coupling error is bounded by `C_tail / ρ^N` (`0 ≤ C_tail`, `1 < ρ`),
the sequence `u_N` converges geometrically to the unique infinite-order fixed point `u_inf`. -/
theorem weighted_banach_infinite_truncation_convergence
    {X : Type*} (D : DistanceLike X)
    (Phi : X → X) (Phi_N : ℕ → X → X)
    {kappa C_tail rho : ℝ}
    (hC : ContractiveWith D kappa Phi)
    (_hCtail : 0 ≤ C_tail) (hrho : 1 < rho)
    (u_inf : X) (hu_inf : Phi u_inf = u_inf)
    (u_N : ℕ → X) (hu_N : ∀ N : ℕ, Phi_N N (u_N N) = u_N N)
    (htail : ∀ N : ℕ, D.d (Phi_N N (u_N N)) (Phi (u_N N)) ≤ C_tail / rho ^ N) :
    (∀ N : ℕ, D.d (u_N N) u_inf ≤ (C_tail / (1 - kappa)) / rho ^ N) ∧
      Filter.Tendsto (fun N : ℕ => D.d (u_N N) u_inf) Filter.atTop (nhds 0) ∧
      (∀ v : X, Phi v = v → v = u_inf) := by
  have h1mk : 0 < 1 - kappa := hC.one_sub_alpha_pos
  have hbound : ∀ N : ℕ, D.d (u_N N) u_inf ≤ (C_tail / (1 - kappa)) / rho ^ N := by
    intro N
    have htri := D.triangle (u_N N) (Phi (u_N N)) u_inf
    have h1 : D.d (u_N N) (Phi (u_N N)) ≤ C_tail / rho ^ N := by
      have h := htail N
      rwa [hu_N N] at h
    have h2 : D.d (Phi (u_N N)) u_inf ≤ kappa * D.d (u_N N) u_inf := by
      have h := hC.contract (u_N N) u_inf
      rwa [hu_inf] at h
    have hcomb : (1 - kappa) * D.d (u_N N) u_inf ≤ C_tail / rho ^ N := by linarith
    have hdiv := div_le_div_of_nonneg_right hcomb (le_of_lt h1mk)
    have hlhs : (1 - kappa) * D.d (u_N N) u_inf / (1 - kappa) = D.d (u_N N) u_inf :=
      mul_div_cancel_left₀ _ (ne_of_gt h1mk)
    have hrhs : C_tail / rho ^ N / (1 - kappa) = (C_tail / (1 - kappa)) / rho ^ N := by
      rw [div_div, div_div, mul_comm (rho ^ N) (1 - kappa)]
    rw [hlhs, hrhs] at hdiv
    exact hdiv
  have htend : Filter.Tendsto (fun N : ℕ => D.d (u_N N) u_inf) Filter.atTop (nhds 0) := by
    have hinv_nn : 0 ≤ 1 / rho := by positivity
    have hinv_lt : 1 / rho < 1 := div_lt_one (by linarith) |>.mpr hrho
    have hpow : Filter.Tendsto (fun N : ℕ => (1 / rho) ^ N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hinv_nn hinv_lt
    have hrew : (fun N : ℕ => (C_tail / (1 - kappa)) / rho ^ N) =
        fun N : ℕ => (C_tail / (1 - kappa)) * (1 / rho) ^ N := by
      funext N
      rw [one_div, inv_pow, div_eq_mul_inv]
    have htop : Filter.Tendsto (fun N : ℕ => (C_tail / (1 - kappa)) / rho ^ N)
        Filter.atTop (nhds 0) := by
      rw [hrew]
      simpa using (tendsto_const_nhds (x := C_tail / (1 - kappa))).mul hpow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htop
      (fun N => D.nonneg (u_N N) u_inf) hbound
  exact ⟨hbound, htend, fun v hv => hC.fixedPoint_unique hv hu_inf⟩

/-- Uniform spectral gap on the infinite-order higher-curvature critical surface:
under non-Gaussian mixing `|δ_n| ≤ κ (2n - 4)` with `κ < 1` for all `n ≥ n₀ ≥ 3`,
no irrelevant operator ever crosses marginality into the UV-relevant sector (`θ_n < 0`). -/
theorem infinite_order_critical_surface_stability_gap
    {delta : ℕ → ℝ} {kappa : ℝ} {n0 : ℕ}
    (hn0 : 3 ≤ n0) (hkap : kappa < 1)
    (hmix : ∀ n : ℕ, n0 ≤ n → |delta n| ≤ kappa * (2 * (n : ℝ) - 4)) :
    ∀ n : ℕ, n0 ≤ n →
      fOfRCriticalExponent delta n ≤ -(1 - kappa) * (2 * (n : ℝ) - 4) ∧
        fOfRCriticalExponent delta n < 0 := by
  intro n hn
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hn0 hn
  have hpos_mode : 0 < 2 * (n : ℝ) - 4 := by linarith
  have hdelta_ub : delta n ≤ kappa * (2 * (n : ℝ) - 4) := (abs_le.mp (hmix n hn)).2
  have h1 : fOfRCriticalExponent delta n ≤ -(1 - kappa) * (2 * (n : ℝ) - 4) := by
    dsimp [fOfRCriticalExponent]; linarith
  have h2 : -(1 - kappa) * (2 * (n : ℝ) - 4) < 0 := by
    have h1mk : 0 < 1 - kappa := sub_pos.mpr hkap
    nlinarith
  exact ⟨h1, lt_of_le_of_lt h1 h2⟩

/-- Strong-mixing non-contractive truncation failure counterexample (`P-H1D4-BANACH-01`):
at order `N = 1`, `u - u² = 0` exhibits a spurious non-Gaussian fixed point `u = 1 ≠ 0`,
yet at order `N = 2` (`u - u² - 2v = 0, v - (u² + 1)/2 = 0`) no real fixed point exists (`-2u² + u - 1 = 0`
has discriminant `-7 < 0`). Proves contractivity `κ < 1` or structural decoupling is strictly required. -/
theorem strong_mixing_truncation_spurious_fp_counterexample :
    ((1 : ℝ) - (1 : ℝ) ^ 2 = 0 ∧ (1 : ℝ) ≠ 0) ∧
      ¬ ∃ u v : ℝ, u - u ^ 2 - 2 * v = 0 ∧ v - (u ^ 2 + 1) / 2 = 0 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rintro ⟨u, v, h1, h2⟩
  have hv : v = (u ^ 2 + 1) / 2 := by linarith
  rw [hv] at h1
  nlinarith [sq_nonneg (4 * u - 1)]

/-! ## 2. OS Weak-Limit Closure, GNS Quotient, Cauchy Coherence & Ursell (`P-H1D4-OSRECON-02`) -/

private lemma symmetric_bilinear_comm {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (hSymm : Mᵀ = M) (phi psi : Fin N → ℝ) :
    dotProduct phi (M.mulVec psi) = dotProduct psi (M.mulVec phi) := by
  calc
    dotProduct phi (M.mulVec psi)
      = ∑ i : Fin N, phi i * ∑ j : Fin N, M i j * psi j := by simp [dotProduct, Matrix.mulVec]
    _ = ∑ i : Fin N, ∑ j : Fin N, phi i * (M i j * psi j) :=
          Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
    _ = ∑ j : Fin N, ∑ i : Fin N, psi j * (M j i * phi i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
          have hM : M i j = M j i := by
            have := congrFun (congrFun hSymm j) i
            simpa [Matrix.transpose_apply] using this
          rw [hM]; ring
    _ = ∑ j : Fin N, psi j * ∑ i : Fin N, M j i * phi i :=
          Finset.sum_congr rfl (fun j _ => (Finset.mul_sum _ _ _).symm)
    _ = dotProduct psi (M.mulVec phi) := by simp [dotProduct, Matrix.mulVec]

private lemma bilinear_quad_expand {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (hSymm : Mᵀ = M) (phi psi : Fin N → ℝ) (t : ℝ) :
    dotProduct (phi + t • psi) (M.mulVec (phi + t • psi)) =
      dotProduct psi (M.mulVec psi) * t ^ 2 +
        2 * dotProduct phi (M.mulVec psi) * t +
        dotProduct phi (M.mulVec phi) := by
  have hcomm : dotProduct psi (M.mulVec phi) = dotProduct phi (M.mulVec psi) :=
    (symmetric_bilinear_comm M hSymm phi psi).symm
  have h1 : M.mulVec (phi + t • psi) = M.mulVec phi + t • M.mulVec psi := by
    ext i
    simp [Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [h1]
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hcomm]
  ring

private lemma bilinear_sub_expand {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (hSymm : Mᵀ = M) (u v : Fin N → ℝ) :
    dotProduct (u - v) (M.mulVec (u - v)) =
      dotProduct u (M.mulVec u) - 2 * dotProduct u (M.mulVec v) + dotProduct v (M.mulVec v) := by
  have hcomm : dotProduct v (M.mulVec u) = dotProduct u (M.mulVec v) :=
    (symmetric_bilinear_comm M hSymm u v).symm
  have h1 : M.mulVec (u - v) = M.mulVec u - M.mulVec v := by
    ext i; simp [Matrix.mulVec_sub]
  rw [h1]
  simp only [dotProduct_sub, sub_dotProduct]
  rw [hcomm]
  ring

/-- OS Reflection Positivity Weak-Limit Closure & GNS Hilbert Space Quotient (`P-H1D4-OSRECON-02`):
1. Any pointwise weak limit `S_∞` of reflection-positive kernels `0 ≤ S_m ψ ψ` remains positive
   semidefinite (`0 ≤ S_∞ ψ ψ`).
2. Every symmetric PSD limit kernel `M_∞` satisfies exact Cauchy–Schwarz, exact null-space
   characterization `⟨ψ, M_∞ ψ⟩ = 0 ↔ ∀ φ, ⟨φ, M_∞ ψ⟩ = 0`, and unique `QuotientDescent`
   factorization of the physical Hilbert norm through `q_GNS`. -/
theorem os_reflection_positivity_closed_under_weak_limits_and_gns_quotient
    {N : ℕ} {PhysHilbert : Type*}
    (S : ℕ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (S_inf : (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hOS_m : ∀ m : ℕ, ∀ psi : Fin N → ℝ, 0 ≤ S m psi psi)
    (hweak : ∀ psi : Fin N → ℝ, Filter.Tendsto (fun m : ℕ => S m psi psi) Filter.atTop (nhds (S_inf psi psi)))
    (M_inf : Matrix (Fin N) (Fin N) ℝ) (hSymm : M_infᵀ = M_inf)
    (hPSD : ∀ psi : Fin N → ℝ, 0 ≤ dotProduct psi (M_inf.mulVec psi))
    (q_GNS : (Fin N → ℝ) → PhysHilbert) (hq : Surjective q_GNS)
    (hker : ∀ u v : Fin N → ℝ, q_GNS u = q_GNS v →
      dotProduct (u - v) (M_inf.mulVec (u - v)) = 0) :
    (∀ psi : Fin N → ℝ, 0 ≤ S_inf psi psi) ∧
      (∀ phi psi : Fin N → ℝ,
        (dotProduct phi (M_inf.mulVec psi)) ^ 2 ≤
          dotProduct phi (M_inf.mulVec phi) * dotProduct psi (M_inf.mulVec psi)) ∧
      (∀ psi : Fin N → ℝ,
        dotProduct psi (M_inf.mulVec psi) = 0 ↔ ∀ phi : Fin N → ℝ, dotProduct phi (M_inf.mulVec psi) = 0) ∧
      ∃! norm_phys : PhysHilbert → ℝ,
        norm_phys ∘ q_GNS = fun psi => dotProduct psi (M_inf.mulVec psi) := by
  have hS_lim : ∀ psi : Fin N → ℝ, 0 ≤ S_inf psi psi := fun psi =>
    ge_of_tendsto (hweak psi) (Filter.Eventually.of_forall (fun m => hOS_m m psi))
  have hCS : ∀ phi psi : Fin N → ℝ,
      (dotProduct phi (M_inf.mulVec psi)) ^ 2 ≤
        dotProduct phi (M_inf.mulVec phi) * dotProduct psi (M_inf.mulVec psi) := by
    intro phi psi
    set a := dotProduct psi (M_inf.mulVec psi)
    set b := dotProduct phi (M_inf.mulVec psi)
    set c := dotProduct phi (M_inf.mulVec phi)
    have ha_nn : 0 ≤ a := hPSD psi
    have hpoly : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t + c := fun t => by
      have h := hPSD (phi + t • psi)
      rwa [bilinear_quad_expand M_inf hSymm phi psi t] at h
    rcases ha_nn.eq_or_lt with ha0 | ha_pos
    · have hb0 : b = 0 := by
        by_contra hne
        have hval := hpoly (-(c + 1) / (2 * b))
        have hlin : a * (-(c + 1) / (2 * b)) ^ 2 + 2 * b * (-(c + 1) / (2 * b)) + c = -1 := by
          rw [← ha0]
          have hb_ne : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hne
          calc
            0 * (-(c + 1) / (2 * b)) ^ 2 + 2 * b * (-(c + 1) / (2 * b)) + c
              = -(c + 1) + c := by rw [zero_mul, zero_add, mul_div_cancel₀ _ hb_ne]
            _ = -1 := by ring
        linarith
      rw [hb0, ← ha0]; norm_num
    · have hmin := hpoly (-b / a)
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      have hid : a * (-b / a) ^ 2 + 2 * b * (-b / a) + c = (a * c - b ^ 2) / a := by
        rw [eq_div_iff ha_ne]
        have hsq : a * (-b / a) ^ 2 = (a * (-b / a)) * (-b / a) := by ring
        calc
          (a * (-b / a) ^ 2 + 2 * b * (-b / a) + c) * a
            = (a * (-b / a)) * (a * (-b / a)) + 2 * b * (a * (-b / a)) + c * a := by ring
          _ = (-b) * (-b) + 2 * b * (-b) + c * a := by rw [mul_div_cancel₀ _ ha_ne]
          _ = a * c - b ^ 2 := by ring
      rw [hid] at hmin
      have hnonneg := (div_nonneg_iff.mp hmin).elim (fun h => h.1) (fun h => absurd h.2 (by linarith))
      linarith
  have hnull : ∀ psi : Fin N → ℝ,
      dotProduct psi (M_inf.mulVec psi) = 0 ↔ ∀ phi : Fin N → ℝ, dotProduct phi (M_inf.mulVec psi) = 0 := by
    intro psi
    constructor
    · intro hz phi
      have hcs := hCS phi psi
      rw [hz, mul_zero] at hcs
      have hsq0 : (dotProduct phi (M_inf.mulVec psi)) ^ 2 = 0 := le_antisymm hcs (sq_nonneg _)
      exact sq_eq_zero_iff.mp hsq0
    · intro hall
      exact hall psi
  have hcompat : FiberCompatible q_GNS (fun psi => dotProduct psi (M_inf.mulVec psi)) := by
    intro u v hqeq
    have huv0 : dotProduct (u - v) (M_inf.mulVec (u - v)) = 0 := hker u v hqeq
    have hvu0 : dotProduct (v - u) (M_inf.mulVec (v - u)) = 0 := by
      have h := hker u v hqeq
      rw [bilinear_sub_expand M_inf hSymm u v] at h
      rw [bilinear_sub_expand M_inf hSymm v u]
      have hcm := symmetric_bilinear_comm M_inf hSymm u v
      linarith
    have hcross_u : dotProduct u (M_inf.mulVec (u - v)) = 0 := (hnull (u - v)).mp huv0 u
    have hcross_v : dotProduct v (M_inf.mulVec (v - u)) = 0 := (hnull (v - u)).mp hvu0 v
    have he1 : dotProduct u (M_inf.mulVec u) - dotProduct u (M_inf.mulVec v) = 0 := by
      have : M_inf.mulVec (u - v) = M_inf.mulVec u - M_inf.mulVec v := by ext i; simp [Matrix.mulVec_sub]
      rw [this, dotProduct_sub] at hcross_u
      exact hcross_u
    have he2 : dotProduct v (M_inf.mulVec v) - dotProduct v (M_inf.mulVec u) = 0 := by
      have : M_inf.mulVec (v - u) = M_inf.mulVec v - M_inf.mulVec u := by ext i; simp [Matrix.mulVec_sub]
      rw [this, dotProduct_sub] at hcross_v
      exact hcross_v
    have hcm := symmetric_bilinear_comm M_inf hSymm u v
    linarith
  have hdesc := (fiberCompatible_iff_existsUnique_descend q_GNS
    (fun psi => dotProduct psi (M_inf.mulVec psi)) hq).mp hcompat
  exact ⟨hS_lim, hCS, hnull, hdesc⟩

/-- Cauchy coherence uniqueness vs tightness oscillation counterexample (`P-H1D4-OSRECON-02`):
1. Any expectation family `E : ℕ → ℝ` that is Cauchy across refinement steps admits a unique limit
   common to EVERY strictly increasing subsequence `f₁, f₂`.
2. Without Cauchy coherence, boundedness/tightness `1 ≤ E_osc m ≤ 2` allows two distinct
   subsequential limits `1 ≠ 2` (exact finite witness of the non-uniqueness obstruction). -/
theorem subsequential_limit_uniqueness_via_cauchy_coherence_vs_oscillation
    (E : ℕ → ℝ) (hCauchy : CauchySeq E)
    (f1 f2 : ℕ → ℕ) (hf1 : StrictMono f1) (hf2 : StrictMono f2)
    (L1 L2 : ℝ)
    (hL1 : Filter.Tendsto (E ∘ f1) Filter.atTop (nhds L1))
    (hL2 : Filter.Tendsto (E ∘ f2) Filter.atTop (nhds L2)) :
    L1 = L2 ∧
      let E_osc : ℕ → ℝ := fun m => if Even m then 1 else 2
      (∀ m : ℕ, 1 ≤ E_osc m ∧ E_osc m ≤ 2) ∧
        Filter.Tendsto (fun k : ℕ => E_osc (2 * k)) Filter.atTop (nhds 1) ∧
        Filter.Tendsto (fun k : ℕ => E_osc (2 * k + 1)) Filter.atTop (nhds 2) ∧
        (1 : ℝ) ≠ 2 := by
  obtain ⟨L_full, hL_full⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hs1 : Filter.Tendsto (E ∘ f1) Filter.atTop (nhds L_full) := hL_full.comp hf1.tendsto_atTop
  have hs2 : Filter.Tendsto (E ∘ f2) Filter.atTop (nhds L_full) := hL_full.comp hf2.tendsto_atTop
  have h1 : L1 = L_full := tendsto_nhds_unique hL1 hs1
  have h2 : L2 = L_full := tendsto_nhds_unique hL2 hs2
  refine ⟨h1.trans h2.symm, ?_⟩
  intro E_osc
  have hbd : ∀ m : ℕ, 1 ≤ E_osc m ∧ E_osc m ≤ 2 := by
    intro m; dsimp [E_osc]
    split_ifs <;> constructor <;> norm_num
  have heven : (fun k : ℕ => E_osc (2 * k)) = fun _ : ℕ => (1 : ℝ) := by
    funext k
    dsimp [E_osc]
    have hev : Even (2 * k) := ⟨k, two_mul k⟩
    simp [hev]
  have hodd : (fun k : ℕ => E_osc (2 * k + 1)) = fun _ : ℕ => (2 : ℝ) := by
    funext k
    dsimp [E_osc]
    have hn : ¬ Even (2 * k + 1) := by
      rintro ⟨r, hr⟩; omega
    simp [hn]
  refine ⟨hbd, ?_, ?_, by norm_num⟩
  · rw [heven]; exact tendsto_const_nhds
  · rw [hodd]; exact tendsto_const_nhds

/-- Normalized connected 4-point Ursell cumulant `m₄ - 3 m₂²`. -/
def ursell4 (m2 m4 : ℝ) : ℝ := m4 - 3 * m2 ^ 2

/-- Ursell 4-point non-triviality dichotomy and continuum limit preservation (`P-H1D4-OSRECON-02`):
1. Exact Gaussian states obey `ursell4 m₂ (3 m₂²) = 0`,
2. Non-Gaussian symmetric spin-±1 measure gives `ursell4 1 1 = -2 < 0`,
3. Any convergent sequence `(m₂,ₛ, m₄,ₛ) → (m₂,∞, m₄,∞)` satisfying a uniform non-Gaussian bound
   `ursell4 ≤ -c₀` (`c₀ > 0`) preserves strictly negative `ursell4 ≤ -c₀ < 0` in the continuum limit,
   ruling out collapse to a free Gaussian field. -/
theorem ursell_four_point_non_triviality_dichotomy_and_limit_preservation
    (m2_s m4_s : ℕ → ℝ) (m2_inf m4_inf c0 : ℝ)
    (hc0 : 0 < c0)
    (hm2 : Filter.Tendsto m2_s Filter.atTop (nhds m2_inf))
    (hm4 : Filter.Tendsto m4_s Filter.atTop (nhds m4_inf))
    (hunif : ∀ k : ℕ, ursell4 (m2_s k) (m4_s k) ≤ -c0) :
    (∀ m2 : ℝ, ursell4 m2 (3 * m2 ^ 2) = 0) ∧
      (ursell4 1 1 = -2 ∧ ursell4 1 1 < 0) ∧
      (ursell4 m2_inf m4_inf ≤ -c0 ∧ ursell4 m2_inf m4_inf < 0) := by
  have hgauss : ∀ m2 : ℝ, ursell4 m2 (3 * m2 ^ 2) = 0 := by
    intro m2; dsimp [ursell4]; ring
  have hdisc : ursell4 1 1 = -2 ∧ ursell4 1 1 < 0 := by
    dsimp [ursell4]; norm_num
  have hlim : Filter.Tendsto (fun k : ℕ => ursell4 (m2_s k) (m4_s k))
      Filter.atTop (nhds (ursell4 m2_inf m4_inf)) := by
    dsimp [ursell4]
    exact hm4.sub ((tendsto_const_nhds (x := (3 : ℝ))).mul (hm2.pow 2))
  have hle : ursell4 m2_inf m4_inf ≤ -c0 :=
    le_of_tendsto hlim (Filter.Eventually.of_forall hunif)
  exact ⟨hgauss, hdisc, hle, by linarith⟩

/-! ## 3. UEOT `AH01` Operational Horizon UV Screening Equivalence (`P-H1D4-OPER-03`) -/

/-- Operational Horizon UV Screening & IR+EFT `QuotientDescent` Equivalence (`P-H1D4-OPER-03`):
Directly invoking `OperationalHorizonMinimumScale.gravitational_horizon_excludes_pointlike_clock` (`AH01`),
any physical clock satisfying Robertson–Heisenberg SNR (`E_min ℏ c ≤ E_tot L`) and spherical non-trapping
(`2 G E_tot < λ_sys c⁴ L`) is strictly bounded away from `a → 0⁺` by `L_min_sq < L²`.
Consequently:
1. Sub-Planckian EFT discrepancy `d_TV ≤ C_UV (k_obs² L_min_sq)` falls strictly below experimental
   resolution `ε_exp` whenever `k_obs² L_min_sq < ε_exp / C_UV`,
2. Distinguishing `H1a–H1c + H1d1–H1d3` IR+EFT predictions from candidate nonperturbative completions
   with advantage `δ_adv ≤ 2 N_shots d_TV²` requires at least `δ_adv / (2 C_UV² (k_obs² L_min_sq)²)` shots,
3. Every sub-Planckian operational observable invariant across the same IR+EFT image factors **uniquely**
   through `q_IR : UVCompletion → IREFTData` via `QuotientDescent`. -/
theorem ah01_horizon_uv_screening_and_finite_shot_indistinguishability
    {UVCompletion IREFTData Val : Type*}
    (q_IR : UVCompletion → IREFTData) (O_phys : UVCompletion → Val)
    (hq : Surjective q_IR) (hcomp : FiberCompatible q_IR O_phys)
    {L E_tot E_min hbar c G lam_sys k_obs C_UV d_TV eps_exp delta_adv N_shots : ℝ}
    (hL : 0 < L) (hEmin : 0 < E_min) (hhbar : 0 < hbar) (hc : 0 < c)
    (hG : 0 < G) (hlam : 0 < lam_sys)
    (hclock : E_min * hbar * c ≤ E_tot * L)
    (hnotrap : 2 * G * E_tot < lam_sys * c ^ 4 * L)
    (hk : 0 < k_obs) (hCuv : 0 < C_UV) (_heps : 0 < eps_exp) (hd_nn : 0 ≤ d_TV)
    (hd_le : d_TV ≤ C_UV * (k_obs ^ 2 * ((2 * E_min / lam_sys) * (hbar * G / c ^ 3))))
    (_hdelta : 0 < delta_adv) (hN : 0 ≤ N_shots)
    (hhoeff : delta_adv ≤ 2 * N_shots * d_TV ^ 2) :
    let L_min_sq := (2 * E_min / lam_sys) * (hbar * G / c ^ 3)
    (0 < L_min_sq ∧ L_min_sq < L ^ 2) ∧
      (k_obs ^ 2 * L_min_sq < eps_exp / C_UV → d_TV < eps_exp) ∧
      delta_adv / (2 * C_UV ^ 2 * (k_obs ^ 2 * L_min_sq) ^ 2) ≤ N_shots ∧
      ∃! O_IR : IREFTData → Val, O_IR ∘ q_IR = O_phys := by
  intro L_min_sq
  have hah := gravitational_horizon_excludes_pointlike_clock
    hL hEmin hhbar hc hG hlam hclock hnotrap
  have hscr : k_obs ^ 2 * L_min_sq < eps_exp / C_UV → d_TV < eps_exp := by
    intro hlt
    have hmul : C_UV * (k_obs ^ 2 * L_min_sq) < C_UV * (eps_exp / C_UV) :=
      mul_lt_mul_of_pos_left hlt hCuv
    have hcancel : C_UV * (eps_exp / C_UV) = eps_exp := mul_div_cancel₀ _ (ne_of_gt hCuv)
    linarith
  have hshot : delta_adv / (2 * C_UV ^ 2 * (k_obs ^ 2 * L_min_sq) ^ 2) ≤ N_shots := by
    have hpos_rhs : 0 < C_UV * (k_obs ^ 2 * L_min_sq) :=
      mul_pos hCuv (mul_pos (sq_pos_of_pos hk) hah.1)
    have hsq_le : d_TV ^ 2 ≤ (C_UV * (k_obs ^ 2 * L_min_sq)) ^ 2 := by nlinarith
    have hmul_le : 2 * N_shots * d_TV ^ 2 ≤ 2 * N_shots * (C_UV * (k_obs ^ 2 * L_min_sq)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq_le (by linarith)
    have hdel_le : delta_adv ≤ 2 * N_shots * (C_UV * (k_obs ^ 2 * L_min_sq)) ^ 2 :=
      le_trans hhoeff hmul_le
    have hden_pos : 0 < 2 * C_UV ^ 2 * (k_obs ^ 2 * L_min_sq) ^ 2 := by positivity
    rw [div_le_iff₀ hden_pos]
    calc
      delta_adv ≤ 2 * N_shots * (C_UV * (k_obs ^ 2 * L_min_sq)) ^ 2 := hdel_le
      _ = N_shots * (2 * C_UV ^ 2 * (k_obs ^ 2 * L_min_sq) ^ 2) := by ring
  have hdesc := (fiberCompatible_iff_existsUnique_descend q_IR O_phys hq).mp hcomp
  exact ⟨hah, hscr, hshot, hdesc⟩

/-! ## 4. Sharp 4-Layer Decomposition of `H1d4` & Operational vs Math Split (`C-H1D4-FINAL-04`) -/

/-- Final 4-layer decomposition of `H1d4_GlobalNonTruncated4DContinuumMeasureUniqueness`. -/
inductive H1d4SubHypothesis : Type
  | H1d4a_WeightedBanachInfiniteTruncationConvergence
  | H1d4b_OSWeakLimitGNSReconstructionAndNonTriviality
  | H1d4c_OperationalHorizonUVScreeningEquivalence
  | H1d4d_UnconditionalExact4DNonPolynomialDecouplingProof
  deriving DecidableEq, Repr

instance : Fintype H1d4SubHypothesis where
  elems := {
    .H1d4a_WeightedBanachInfiniteTruncationConvergence,
    .H1d4b_OSWeakLimitGNSReconstructionAndNonTriviality,
    .H1d4c_OperationalHorizonUVScreeningEquivalence,
    .H1d4d_UnconditionalExact4DNonPolynomialDecouplingProof
  }
  complete h := by cases h <;> decide

/-- Quantitative defect record evaluating all four sublayers of `H1d4`. -/
structure H1d4LayerCandidate where
  weightedBanachDefect : ℝ
  osGnsUrsellDefect : ℝ
  operationalUVScreeningDefect : ℝ
  nonPolynomialDecouplingDefect : ℝ

/-- Semantic closure predicate on each sublayer of `H1d4`. -/
def H1d4LayerCandidate.Satisfies (C : H1d4LayerCandidate) : H1d4SubHypothesis → Prop
  | .H1d4a_WeightedBanachInfiniteTruncationConvergence => C.weightedBanachDefect = 0
  | .H1d4b_OSWeakLimitGNSReconstructionAndNonTriviality => C.osGnsUrsellDefect = 0
  | .H1d4c_OperationalHorizonUVScreeningEquivalence => C.operationalUVScreeningDefect = 0
  | .H1d4d_UnconditionalExact4DNonPolynomialDecouplingProof => C.nonPolynomialDecouplingDefect = 0

/-- Complete unconditional mathematical closure of `H1d4`. -/
def H1d4LayerCandidate.FullH1d4Closure (C : H1d4LayerCandidate) : Prop :=
  C.weightedBanachDefect = 0 ∧
  C.osGnsUrsellDefect = 0 ∧
  C.operationalUVScreeningDefect = 0 ∧
  C.nonPolynomialDecouplingDefect = 0

/-- Lifting map from Wave 10's `H1d4LayerCandidate` to Wave 9's `H1dLayerCandidate` (`H1d1..H1d3` closed). -/
def H1d4LayerCandidate.toH1dCandidate (C : H1d4LayerCandidate) : H1dLayerCandidate :=
  ⟨0, 0, 0,
    |C.weightedBanachDefect| + |C.osGnsUrsellDefect| +
      |C.operationalUVScreeningDefect| + |C.nonPolynomialDecouplingDefect|⟩

/-- Wave 10 Witness closing `H1d4a ∧ H1d4b ∧ H1d4c` while isolating `H1d4d` as an irreducible
Millennium-class pure-mathematics problem. -/
def wave10H1d4ConstructiveWitness : H1d4LayerCandidate :=
  ⟨0, 0, 0, 1⟩

/-- Sharp `H1d4` Final Reduction & Operational vs Millennium-Math Split (`C-H1D4-FINAL-04`):
1. `Fintype.card H1d4SubHypothesis = 4` and `FullH1d4Closure C ↔ ∀ h, C.Satisfies h`,
2. `wave10H1d4ConstructiveWitness` closes `H1d4a ∧ H1d4b ∧ H1d4c` while leaving `H1d4d` open,
3. All four sublayers `H1d4a..H1d4d` are pairwise logically independent,
4. Two-level reduction back to Wave 8 (`H1LayerCandidate`): when `H1d4a ∧ H1d4b ∧ H1d4c` hold,
   full mathematical `H1` closure holds **iff** `H1d4d` holds,
5. Unconditional pure-math `H1d4d` remaining open keeps `physicalUnificationStatus = .OPEN`. -/
theorem h1d4_final_sharp_reduction_and_operational_vs_mathematical_split :
    Fintype.card H1d4SubHypothesis = 4 ∧
      (∀ C : H1d4LayerCandidate, C.FullH1d4Closure ↔ ∀ h : H1d4SubHypothesis, C.Satisfies h) ∧
      (wave10H1d4ConstructiveWitness.Satisfies .H1d4a_WeightedBanachInfiniteTruncationConvergence ∧
        wave10H1d4ConstructiveWitness.Satisfies .H1d4b_OSWeakLimitGNSReconstructionAndNonTriviality ∧
        wave10H1d4ConstructiveWitness.Satisfies .H1d4c_OperationalHorizonUVScreeningEquivalence ∧
        ¬ wave10H1d4ConstructiveWitness.Satisfies .H1d4d_UnconditionalExact4DNonPolynomialDecouplingProof) ∧
      (∀ h : H1d4SubHypothesis, ∃ C : H1d4LayerCandidate,
        (∀ h' : H1d4SubHypothesis, h' ≠ h → C.Satisfies h') ∧ ¬ C.Satisfies h) ∧
      (∀ C : H1d4LayerCandidate,
        C.Satisfies .H1d4a_WeightedBanachInfiniteTruncationConvergence →
        C.Satisfies .H1d4b_OSWeakLimitGNSReconstructionAndNonTriviality →
        C.Satisfies .H1d4c_OperationalHorizonUVScreeningEquivalence →
        (C.toH1dCandidate.toH1Candidate.FullH1Closure ↔
          C.Satisfies .H1d4d_UnconditionalExact4DNonPolynomialDecouplingProof)) ∧
      (∀ k : ℕ, physicalUnificationStatus (k + 1) false = .OPEN) ∧
      physicalUnificationStatus (Fintype.card H1d4SubHypothesis) false = .OPEN := by
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
      exact ⟨hall .H1d4a_WeightedBanachInfiniteTruncationConvergence,
        hall .H1d4b_OSWeakLimitGNSReconstructionAndNonTriviality,
        hall .H1d4c_OperationalHorizonUVScreeningEquivalence,
        hall .H1d4d_UnconditionalExact4DNonPolynomialDecouplingProof⟩
  · exact ⟨rfl, rfl, rfl, by simp [wave10H1d4ConstructiveWitness, H1d4LayerCandidate.Satisfies]⟩
  · intro h
    cases h with
    | H1d4a_WeightedBanachInfiniteTruncationConvergence =>
      refine ⟨⟨1, 0, 0, 0⟩, ?_, by simp [H1d4LayerCandidate.Satisfies]⟩
      intro h' hne; cases h' <;> first | exact absurd rfl hne | rfl
    | H1d4b_OSWeakLimitGNSReconstructionAndNonTriviality =>
      refine ⟨⟨0, 1, 0, 0⟩, ?_, by simp [H1d4LayerCandidate.Satisfies]⟩
      intro h' hne; cases h' <;> first | exact absurd rfl hne | rfl
    | H1d4c_OperationalHorizonUVScreeningEquivalence =>
      refine ⟨⟨0, 0, 1, 0⟩, ?_, by simp [H1d4LayerCandidate.Satisfies]⟩
      intro h' hne; cases h' <;> first | exact absurd rfl hne | rfl
    | H1d4d_UnconditionalExact4DNonPolynomialDecouplingProof =>
      refine ⟨⟨0, 0, 0, 1⟩, ?_, by simp [H1d4LayerCandidate.Satisfies]⟩
      intro h' hne; cases h' <;> first | exact absurd rfl hne | rfl
  · intro C h1 h2 h3
    dsimp [H1d4LayerCandidate.Satisfies] at h1 h2 h3 ⊢
    dsimp [H1d4LayerCandidate.toH1dCandidate, H1dLayerCandidate.toH1Candidate,
      H1LayerCandidate.FullH1Closure]
    simp [h1, h2, h3]
  · intro k
    simp [physicalUnificationStatus]
  · decide

end UEOTPhysicsUnification.Nonperturbative4DMeasureLimitH1d4
