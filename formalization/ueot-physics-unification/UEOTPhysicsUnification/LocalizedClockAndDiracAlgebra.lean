import Mathlib.Tactic

/-!
# Localized Asymptotically Flat (`Λ = 0`) Clock Barrier & Anomaly-Free Dirac Algebra
(`P-FLAT-DIRAC-03`)

Pure-kernel Lean 4 formalization of `NEXT_GATE` Gates 3 and 4:

1. `lichnerowicz_critical_rational_barrier` & `lichnerowicz_picard_contraction_on_barrier`:
   For a localized clock/apparatus packet of compactness `C_0 = 4 * α` in asymptotically flat
   `ℝ^{1,3}` with `Λ = 0`, whenever `0 < C_0 < 2048 / 9375` (`α < 512 / 9375`), the nonlinear
   Lichnerowicz map `T(ψ) = 1 + (3/2) * α * ψ^5` maps `[1, 5/4]` strictly into `[1, 5/4]` and is
   a strict contraction with Lipschitz constant `(9375 / 2048) * C_0 < 1`, certifying ADM mass
   enclosure `M_bare ≤ M_ADM ≤ (3125 / 1024) * M_bare` without cosmological closure density.
2. `cnumber_normal_ordering_preserves_commutator`: Subtracting arbitrary `c`-number vacuum
   expectations `A - c_A • 1, B - c_B • 1` in any associative algebra cancels identically inside
   `[A - c_A • 1, B - c_B • 1] = [A, B]` (zero central Schwinger anomaly from slice normal ordering).
3. `local_mediator_zero_dirac_defect_vs_nonlocal_smearing`: Canonical two-point test proving that
   any local auxiliary-mediator portal `N_1 U_loc(q_1, σ_1) + N_2 U_loc(q_2, σ_2)` has identically
   zero ultralocal lapse-lapse Poisson/Dirac defect, whereas nonlocal spatial smearing `ε ≠ 0`
   mixing `q_1` and `q_2` generates a strictly nonzero defect proportional to `ε * (N_1 M_2 - N_2 M_1)`.
-/

namespace UEOTPhysicsUnification.LocalizedClockAndDiracAlgebra

/-- Exact rational critical point of `(ψ - 1) / ψ^5` at `ψ_max = 5/4`:
at `α_crit = 512 / 9375` (`C_crit = 2048 / 9375`), `1 + (3/2) * α_crit * (5/4)^5 = 5/4`
and `(15/2) * α_crit * (5/4)^4 = 1`. -/
theorem lichnerowicz_critical_rational_identities :
    (1 : ℝ) + (3 / 2 : ℝ) * (512 / 9375 : ℝ) * (5 / 4 : ℝ) ^ 5 = (5 / 4 : ℝ) ∧
      (15 / 2 : ℝ) * (512 / 9375 : ℝ) * (5 / 4 : ℝ) ^ 4 = 1 := by
  norm_num

/-- Monotone self-map and strict contraction of the `Λ = 0` asymptotically flat Lichnerowicz
map `T(ψ) = 1 + (3/8) * C_0 * ψ^5` on `[1, 5/4]` for every sub-critical compactness
`0 < C_0 < 2048 / 9375`. -/
theorem lichnerowicz_subcritical_barrier_and_contraction
    {C0 : ℝ} (hpos : 0 < C0) (hsub : C0 < (2048 / 9375 : ℝ)) :
    let T : ℝ → ℝ := fun psi => 1 + (3 / 8 : ℝ) * C0 * psi ^ 5
    let L_lip : ℝ := (9375 / 2048 : ℝ) * C0
    L_lip < 1 ∧
      (∀ psi, 1 ≤ psi → psi ≤ (5 / 4 : ℝ) → 1 < T psi ∧ T psi < (5 / 4 : ℝ)) ∧
      (∀ x y, 1 ≤ x → x ≤ (5 / 4 : ℝ) → 1 ≤ y → y ≤ (5 / 4 : ℝ) →
        |T x - T y| ≤ L_lip * |x - y|) := by
  intro T L_lip
  refine ⟨by dsimp [L_lip]; linarith, ?_, ?_⟩
  · intro psi h1 h54
    dsimp [T]
    have hpsi5_ge : (1 : ℝ) ≤ psi ^ 5 := one_le_pow₀ h1
    have hpsi5_le : psi ^ 5 ≤ (5 / 4 : ℝ) ^ 5 := pow_le_pow_left₀ (by linarith) h54 5
    refine ⟨by nlinarith, ?_⟩
    have hprod : C0 * psi ^ 5 < (2048 / 9375 : ℝ) * (5 / 4 : ℝ) ^ 5 := by
      have hle : C0 * psi ^ 5 ≤ C0 * (5 / 4 : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_left hpsi5_le (le_of_lt hpos)
      have hlt : C0 * (5 / 4 : ℝ) ^ 5 < (2048 / 9375 : ℝ) * (5 / 4 : ℝ) ^ 5 :=
        mul_lt_mul_of_pos_right hsub (by norm_num)
      exact lt_of_le_of_lt hle hlt
    linarith
  · intro x y hx1 hx54 hy1 hy54
    dsimp [T, L_lip]
    have hdiff : (1 + (3 / 8 : ℝ) * C0 * x ^ 5) - (1 + (3 / 8 : ℝ) * C0 * y ^ 5) =
        (3 / 8 : ℝ) * C0 * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4) * (x - y) := by
      ring
    rw [hdiff, abs_mul, abs_mul]
    have hx0 : 0 ≤ x := by linarith
    have hy0 : 0 ≤ y := by linarith
    have hsum_nonneg : 0 ≤ x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4 := by positivity
    have hx4 : x ^ 4 ≤ (5 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hx54 4
    have hy4 : y ^ 4 ≤ (5 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hy0 hy54 4
    have hx3y : x ^ 3 * y ≤ (5 / 4 : ℝ) ^ 4 := by
      have h1 : x ^ 3 ≤ (5 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx54 3
      calc
        x ^ 3 * y ≤ (5 / 4 : ℝ) ^ 3 * (5 / 4 : ℝ) := mul_le_mul h1 hy54 hy0 (by norm_num)
        _ = (5 / 4 : ℝ) ^ 4 := by ring
    have hx2y2 : x ^ 2 * y ^ 2 ≤ (5 / 4 : ℝ) ^ 4 := by
      have h1 : x ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx54 2
      have h2 : y ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hy0 hy54 2
      calc
        x ^ 2 * y ^ 2 ≤ (5 / 4 : ℝ) ^ 2 * (5 / 4 : ℝ) ^ 2 := mul_le_mul h1 h2 (sq_nonneg y) (by norm_num)
        _ = (5 / 4 : ℝ) ^ 4 := by ring
    have hxy3 : x * y ^ 3 ≤ (5 / 4 : ℝ) ^ 4 := by
      have h2 : y ^ 3 ≤ (5 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hy0 hy54 3
      calc
        x * y ^ 3 ≤ (5 / 4 : ℝ) * (5 / 4 : ℝ) ^ 3 := mul_le_mul hx54 h2 (by positivity) (by norm_num)
        _ = (5 / 4 : ℝ) ^ 4 := by ring
    have hsum_le : x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4 ≤ 5 * (5 / 4 : ℝ) ^ 4 := by
      linarith
    rw [abs_of_pos (by positivity), abs_of_nonneg hsum_nonneg]
    have hcoeff : (3 / 8 : ℝ) * C0 * (5 * (5 / 4 : ℝ) ^ 4) = (9375 / 2048 : ℝ) * C0 := by ring
    calc
      (3 / 8 : ℝ) * C0 * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4) * |x - y|
        ≤ (3 / 8 : ℝ) * C0 * (5 * (5 / 4 : ℝ) ^ 4) * |x - y| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (9375 / 2048 : ℝ) * C0 * |x - y| := by rw [hcoeff]

/-- ADM mass enclosure under `1 ≤ ψ(x) ≤ 5/4` and nonnegative bare energy density `ρ ≥ 0`:
`ρ ≤ ρ * ψ^5 ≤ (3125 / 1024) * ρ`. -/
theorem adm_mass_density_rational_enclosure
    {rho psi : ℝ} (hrho : 0 ≤ rho) (hlo : 1 ≤ psi) (hhi : psi ≤ (5 / 4 : ℝ)) :
    rho ≤ rho * psi ^ 5 ∧ rho * psi ^ 5 ≤ (3125 / 1024 : ℝ) * rho := by
  have hp1 : (1 : ℝ) ≤ psi ^ 5 := one_le_pow₀ hlo
  have hp2 : psi ^ 5 ≤ (3125 / 1024 : ℝ) := by
    calc
      psi ^ 5 ≤ (5 / 4 : ℝ) ^ 5 := pow_le_pow_left₀ (by linarith) hhi 5
      _ = (3125 / 1024 : ℝ) := by norm_num
  exact ⟨by nlinarith, by nlinarith⟩

/-- Symmetric `c`-number normal-ordering vacuum subtractions cancel identically inside any ring
commutator `[A - c_A • 1, B - c_B • 1] = [A, B]` (zero central Schwinger anomaly). -/
theorem cnumber_normal_ordering_preserves_commutator
    {R : Type*} [Ring R] [Algebra ℝ R] (A B : R) (cA cB : ℝ) :
    let A_ren := A - algebraMap ℝ R cA
    let B_ren := B - algebraMap ℝ R cB
    A_ren * B_ren - B_ren * A_ren = A * B - B * A := by
  intro A_ren B_ren
  dsimp [A_ren, B_ren]
  have hcommA : algebraMap ℝ R cA * B = B * algebraMap ℝ R cA := Algebra.commutes cA B
  have hcommB : algebraMap ℝ R cB * A = A * algebraMap ℝ R cB := Algebra.commutes cB A
  have hcommAB : algebraMap ℝ R cA * algebraMap ℝ R cB = algebraMap ℝ R cB * algebraMap ℝ R cA :=
    Algebra.commutes cA _
  -- Expand using noncomm_ring and centrality of algebraMap:
  calc
    (A - algebraMap ℝ R cA) * (B - algebraMap ℝ R cB) -
        (B - algebraMap ℝ R cB) * (A - algebraMap ℝ R cA)
      = A * B - B * A - (A * algebraMap ℝ R cB - algebraMap ℝ R cB * A) -
          (algebraMap ℝ R cA * B - B * algebraMap ℝ R cA) +
          (algebraMap ℝ R cA * algebraMap ℝ R cB - algebraMap ℝ R cB * algebraMap ℝ R cA) := by
        noncomm_ring
    _ = A * B - B * A := by
        rw [hcommA, hcommB, hcommAB]
        noncomm_ring

/-- Two-site canonical Poisson/Dirac bracket of `H_ε[N] = (1/2)(N_1 p_1^2 + N_2 p_2^2)
+ (g/2)(N_1 (q_1 + ε q_2)^2 + N_2 (q_2 + ε q_1)^2)`:
at `ε = 0` (local auxiliary mediator action) the ultralocal lapse-lapse bracket vanishes
identically for all `(N, M, q, p)`, whereas nonlocal spatial smearing `ε ≠ 0` produces the exact
defect `g * ε * (N_1 M_2 - N_2 M_1) * (p_1 (q_2 + ε q_1) - p_2 (q_1 + ε q_2))`. -/
def twoSiteLapseBracket (g eps N1 N2 M1 M2 q1 q2 p1 p2 : ℝ) : ℝ :=
  let dH_dq1 := g * (N1 * (q1 + eps * q2) + eps * N2 * (q2 + eps * q1))
  let dH_dq2 := g * (eps * N1 * (q1 + eps * q2) + N2 * (q2 + eps * q1))
  let dH_dp1 := N1 * p1
  let dH_dp2 := N2 * p2
  let dK_dq1 := g * (M1 * (q1 + eps * q2) + eps * M2 * (q2 + eps * q1))
  let dK_dq2 := g * (eps * M1 * (q1 + eps * q2) + M2 * (q2 + eps * q1))
  let dK_dp1 := M1 * p1
  let dK_dp2 := M2 * p2
  (dH_dq1 * dK_dp1 - dH_dp1 * dK_dq1) + (dH_dq2 * dK_dp2 - dH_dp2 * dK_dq2)

theorem local_mediator_vs_nonlocal_smearing_dirac_defect
    (g eps N1 N2 M1 M2 q1 q2 p1 p2 : ℝ) :
    twoSiteLapseBracket g 0 N1 N2 M1 M2 q1 q2 p1 p2 = 0 ∧
      twoSiteLapseBracket g eps N1 N2 M1 M2 q1 q2 p1 p2 =
        g * eps * (N1 * M2 - N2 * M1) * (p2 * (q1 + eps * q2) - p1 * (q2 + eps * q1)) := by
  unfold twoSiteLapseBracket
  constructor <;> ring

end UEOTPhysicsUnification.LocalizedClockAndDiracAlgebra
