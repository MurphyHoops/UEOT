import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

/-!
# Spacetime Signature Cone, Soft Spin-2 Equivalence Principle & Gravity Bounds
(`B-SIG-01`, `P-EP-02`, `P-GRAV-03`, `P-HORIZON-04`)

Formalizes four foundational gravity and spacetime unification obligations from
`PREMISES_AND_RESPONSIBILITIES.md` (Responsibilities `G02`, `G04`, `G05/G06`, `G14`):

1. **G02 — Fisher Information Pullback Obstruction vs Null-Cone Minkowski Uniqueness**:
   - `fisher_pullback_nonneg` & `fisher_pullback_no_timelike_vector`: Any Fisher-Rao metric pullback
     `∑_i (dp_i)^2 / p_i` (`p_i > 0`) is positive semidefinite on all tangent vectors, proving the
     Chapter 33/67 obstruction that direct real statistical pullback cannot generate a nondegenerate
     Lorentzian signature with `g(v, v) < 0`.
   - `null_cone_uniquely_determines_minkowski_conformal_class`: On `ℝ × (Fin d → ℝ)`, any symmetric
     spacetime tensor `(g00, g0, gSpatial)` whose quadratic form vanishes on the finite-speed causal cone
     `∑_i (x_i)^2 = c^2 t^2` (`c > 0`) satisfies `g0_i = 0`, `gSpatial i i = -g00 / c^2`, and
     `gSpatial j k = 0` (`j ≠ k`), uniquely fixing `Q(t, x) = (-g00 / c^2) * (-c^2 t^2 + ∑_i x_i^2)`.

2. **G04 — Soft Spin-2 Ward Identity & Kinematic Rank Boundary**:
   - `soft_spin2_universal_coupling`: Under momentum conservation `p_last = -∑_a p_a`, the soft spin-2
     gauge-invariance identity `∑_a κ_a p_a + κ_last p_last = 0` forces `∀ a, κ_a = κ_last` whenever
     `{p_a}` is linearly independent (universal gravitational coupling / Equivalence Principle).
   - `reducible_kinematics_nonuniversal_counterexample`: Explicit 4-leg reducible momentum configuration
     satisfying both `∑ p = 0` and `∑ κ p = 0` with `κ_0 ≠ κ_2`, proving the necessity of the rank condition.

3. **G05/G06 — Quadratic Curvature `f(R) = R + R^2/(6 m^2)` PPN Limits**:
   - `starobinsky_ppn_unscreened_vs_screened`: Proves that Yukawa metric potentials `1 ± (1/3) y`
     (`y = exp(-m r) ∈ [0, 1]`) yield `γ_PPN = 1/2` in the unscreened limit `y = 1` (excluded by Cassini)
     and monotonically approach `γ_PPN = 1` in the short-range screened regime `y → 0`.

4. **G14 — Page Entanglement Turnover & Thermal Unitarity Deficit**:
   - `page_unitarity_thermal_deficit_pos`: Past the Page midpoint `2 n s_mode > S_0`, uncorrelated thermal
     radiation entropy `n s_mode` strictly exceeds the coarse-grained horizon capacity `S_0 - n s_mode`
     by `2 n s_mode - S_0 > 0`, quantifying the mandatory multi-mode radiation correlation deficit.
-/

namespace UEOTPhysicsUnification.SpacetimeEquivalenceAndGravityBounds

open scoped BigOperators

/-! ## 1. G02: Fisher Statistical Pullback PSD Obstruction & Causal-Cone Minkowski Uniqueness -/

/-- Fisher-Rao pullback quadratic form `∑_i (dp_i)^2 / p_i` on a finite sample space `Fin m`. -/
noncomputable def fisherQuad {m : ℕ} (p dp : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, (dp i) ^ 2 / p i

/-- Every Fisher-Rao statistical pullback quadratic form with `p_i > 0` is globally nonnegative. -/
theorem fisher_pullback_nonneg
    {m : ℕ} {p : Fin m → ℝ} (hp : ∀ i : Fin m, 0 < p i) (dp : Fin m → ℝ) :
    0 ≤ fisherQuad p dp := by
  unfold fisherQuad
  refine Finset.sum_nonneg ?_
  intro i _
  have hpi : 0 < p i := hp i
  have hsq : 0 ≤ (dp i) ^ 2 := sq_nonneg (dp i)
  exact div_nonneg hsq (le_of_lt hpi)

/-- Direct real Fisher-Rao pullback never admits a timelike vector `g_F(v, v) < 0`. -/
theorem fisher_pullback_no_timelike_vector
    {m : ℕ} {p : Fin m → ℝ} (hp : ∀ i : Fin m, 0 < p i) :
    ¬ ∃ dp : Fin m → ℝ, fisherQuad p dp < 0 := by
  rintro ⟨dp, hlt⟩
  have hge := fisher_pullback_nonneg hp dp
  linarith

/-- General symmetric spacetime quadratic form on `ℝ × (Fin d → ℝ)`. -/
def spacetimeQuad {d : ℕ} (g00 : ℝ) (g0 : Fin d → ℝ) (gS : Fin d → Fin d → ℝ)
    (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  g00 * t ^ 2 + 2 * t * (∑ i : Fin d, g0 i * x i) +
    ∑ i : Fin d, ∑ j : Fin d, gS i j * x i * x j

/-- Standard Minkowski quadratic form `-c^2 t^2 + ∑_i x_i^2`. -/
def minkowskiQuad {d : ℕ} (c t : ℝ) (x : Fin d → ℝ) : ℝ :=
  -(c ^ 2) * t ^ 2 + ∑ i : Fin d, (x i) ^ 2

/-- Vanishing on the finite-speed causal cone `∑_i x_i^2 = c^2 t^2` (`c > 0`) forces every shift
cross-term `g0 k = 0` and every diagonal spatial component `gS k k = -g00 / c^2`. -/
theorem null_cone_fixes_shift_and_diagonal
    {d : ℕ} {c g00 : ℝ} {g0 : Fin d → ℝ} {gS : Fin d → Fin d → ℝ}
    (hc : 0 < c)
    (hcone : ∀ (t : ℝ) (x : Fin d → ℝ), (∑ i : Fin d, (x i) ^ 2 = c ^ 2 * t ^ 2) →
      spacetimeQuad g00 g0 gS t x = 0)
    (k : Fin d) :
    g0 k = 0 ∧ gS k k = -g00 / c ^ 2 := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hc2ne : c ^ 2 ≠ 0 := pow_ne_zero 2 hcne
  let xp : Fin d → ℝ := fun i => if i = k then c else 0
  let xm : Fin d → ℝ := fun i => if i = k then -c else 0
  have hxp_cone : ∑ i : Fin d, (xp i) ^ 2 = c ^ 2 * (1 : ℝ) ^ 2 := by
    simp [xp]
  have hxm_cone : ∑ i : Fin d, (xm i) ^ 2 = c ^ 2 * (1 : ℝ) ^ 2 := by
    simp [xm]
  have hp := hcone 1 xp hxp_cone
  have hm := hcone 1 xm hxm_cone
  have hp_eval : spacetimeQuad g00 g0 gS 1 xp = g00 + 2 * c * g0 k + c ^ 2 * gS k k := by
    unfold spacetimeQuad
    have hs1 : (∑ i : Fin d, g0 i * xp i) = g0 k * c := by
      simp [xp]
    have hs2 : (∑ i : Fin d, ∑ j : Fin d, gS i j * xp i * xp j) = gS k k * c * c := by
      have inner : ∀ i : Fin d, (∑ j : Fin d, gS i j * xp i * xp j) =
          if i = k then gS k k * c * c else 0 := by
        intro i
        by_cases hik : i = k
        · subst hik
          simp [xp]
        · simp [xp, hik]
      simp [inner]
    rw [hs1, hs2]
    ring
  have hm_eval : spacetimeQuad g00 g0 gS 1 xm = g00 - 2 * c * g0 k + c ^ 2 * gS k k := by
    unfold spacetimeQuad
    have hs1 : (∑ i : Fin d, g0 i * xm i) = -(g0 k * c) := by
      simp [xm]
    have hs2 : (∑ i : Fin d, ∑ j : Fin d, gS i j * xm i * xm j) = gS k k * c * c := by
      have inner : ∀ i : Fin d, (∑ j : Fin d, gS i j * xm i * xm j) =
          if i = k then gS k k * c * c else 0 := by
        intro i
        by_cases hik : i = k
        · subst hik
          simp [xm]
        · simp [xm, hik]
      simp [inner]
    rw [hs1, hs2]
    ring
  rw [hp_eval] at hp
  rw [hm_eval] at hm
  have hg0 : g0 k = 0 := by
    have hdiff : 4 * c * g0 k = 0 := by linarith
    have h4c : 4 * c ≠ 0 := by positivity
    exact (mul_eq_zero.mp hdiff).resolve_left h4c
  have hgkk : gS k k = -g00 / c ^ 2 := by
    rw [hg0] at hp
    field_simp [hc2ne]
    linarith
  exact ⟨hg0, hgkk⟩

/-- Using the `(3, 4, 5)` Pythagorean null ray `(t = 5, x = 3 c e_j + 4 c e_k)`, any symmetric spatial
metric `gS j k = gS k j` vanishing on the causal cone satisfies `gS j k = 0` for `j ≠ k`. -/
theorem null_cone_fixes_off_diagonal
    {d : ℕ} {c g00 : ℝ} {g0 : Fin d → ℝ} {gS : Fin d → Fin d → ℝ}
    (hc : 0 < c)
    (hsym : ∀ i j : Fin d, gS i j = gS j i)
    (hcone : ∀ (t : ℝ) (x : Fin d → ℝ), (∑ i : Fin d, (x i) ^ 2 = c ^ 2 * t ^ 2) →
      spacetimeQuad g00 g0 gS t x = 0)
    {j k : Fin d} (hjk : j ≠ k) :
    gS j k = 0 := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hc2ne : c ^ 2 ≠ 0 := pow_ne_zero 2 hcne
  have hkj : k ≠ j := Ne.symm hjk
  let x34 : Fin d → ℝ := fun i => if i = j then 3 * c else if i = k then 4 * c else 0
  have hx_sq : ∀ i : Fin d, (x34 i) ^ 2 =
      (if i = j then 9 * c ^ 2 else 0) + (if i = k then 16 * c ^ 2 else 0) := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp [x34, hjk]
      ring
    · by_cases hik : i = k
      · subst hik
        simp [x34, hkj]
        ring
      · simp [x34, hij, hik]
  have h34_cone : ∑ i : Fin d, (x34 i) ^ 2 = c ^ 2 * (5 : ℝ) ^ 2 := by
    simp [hx_sq, Finset.sum_add_distrib]
    ring
  have hval := hcone 5 x34 h34_cone
  have hg0_zero : ∀ i : Fin d, g0 i = 0 := fun i => (null_cone_fixes_shift_and_diagonal hc hcone i).1
  have hjj : gS j j = -g00 / c ^ 2 := (null_cone_fixes_shift_and_diagonal hc hcone j).2
  have hkk : gS k k = -g00 / c ^ 2 := (null_cone_fixes_shift_and_diagonal hc hcone k).2
  unfold spacetimeQuad at hval
  have hs0 : (∑ i : Fin d, g0 i * x34 i) = 0 := by
    simp [hg0_zero]
  have hsS : (∑ a : Fin d, ∑ b : Fin d, gS a b * x34 a * x34 b) =
      9 * c ^ 2 * gS j j + 16 * c ^ 2 * gS k k + 12 * c ^ 2 * gS j k + 12 * c ^ 2 * gS k j := by
    have row_eval : ∀ a : Fin d, (∑ b : Fin d, gS a b * x34 a * x34 b) =
        (if a = j then 9 * c ^ 2 * gS j j + 12 * c ^ 2 * gS j k else 0) +
        (if a = k then 12 * c ^ 2 * gS k j + 16 * c ^ 2 * gS k k else 0) := by
      intro a
      have col_eval : ∀ b : Fin d, gS a b * x34 a * x34 b =
          (if b = j then gS a j * x34 a * (3 * c) else 0) +
          (if b = k then gS a k * x34 a * (4 * c) else 0) := by
        intro b
        by_cases hbj : b = j
        · subst hbj
          simp [x34, hjk]
        · by_cases hbk : b = k
          · subst hbk
            simp [x34, hkj]
          · simp [x34, hbj, hbk]
      simp only [col_eval, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      by_cases haj : a = j
      · subst haj
        simp [x34, hjk]
        ring
      · by_cases hak : a = k
        · subst hak
          simp [x34, hkj]
          ring
        · simp [x34, haj, hak]
    simp [row_eval, Finset.sum_add_distrib]
    ring
  rw [hs0, hsS, hjj, hkk, hsym k j] at hval
  have h24 : 24 * c ^ 2 * gS j k = 0 := by
    field_simp [hc2ne] at hval
    linarith
  have h24c : 24 * c ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp h24).resolve_left h24c

/-- Complete causal-cone conformal uniqueness theorem (`B-SIG-01`):
any symmetric spacetime quadratic form vanishing on `∑_i x_i^2 = c^2 t^2` (`c > 0`) equals
`(-g00 / c^2) * minkowskiQuad c t x` for every `(t, x) ∈ ℝ × ℝ^d`. -/
theorem null_cone_uniquely_determines_minkowski_conformal_class
    {d : ℕ} {c g00 : ℝ} {g0 : Fin d → ℝ} {gS : Fin d → Fin d → ℝ}
    (hc : 0 < c)
    (hsym : ∀ i j : Fin d, gS i j = gS j i)
    (hcone : ∀ (t : ℝ) (x : Fin d → ℝ), (∑ i : Fin d, (x i) ^ 2 = c ^ 2 * t ^ 2) →
      spacetimeQuad g00 g0 gS t x = 0)
    (t : ℝ) (x : Fin d → ℝ) :
    spacetimeQuad g00 g0 gS t x = (-g00 / c ^ 2) * minkowskiQuad c t x := by
  have hc2ne : c ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hc)
  have hg0 : ∀ i : Fin d, g0 i = 0 := fun i => (null_cone_fixes_shift_and_diagonal hc hcone i).1
  have hdiag : ∀ i : Fin d, gS i i = -g00 / c ^ 2 :=
    fun i => (null_cone_fixes_shift_and_diagonal hc hcone i).2
  have hoff : ∀ i j : Fin d, i ≠ j → gS i j = 0 :=
    fun i j hij => null_cone_fixes_off_diagonal hc hsym hcone hij
  unfold spacetimeQuad minkowskiQuad
  have hs0 : (∑ i : Fin d, g0 i * x i) = 0 := by simp [hg0]
  have hsS : (∑ i : Fin d, ∑ j : Fin d, gS i j * x i * x j) =
      (-g00 / c ^ 2) * ∑ i : Fin d, (x i) ^ 2 := by
    have inner : ∀ i : Fin d, (∑ j : Fin d, gS i j * x i * x j) = (-g00 / c ^ 2) * (x i) ^ 2 := by
      intro i
      have hterm : ∀ j : Fin d, gS i j * x i * x j =
          if j = i then (-g00 / c ^ 2) * (x i) ^ 2 else 0 := by
        intro j
        by_cases hji : j = i
        · rw [hji, hdiag i]
          simp only [↓reduceIte]
          ring
        · simp [hji, hoff i j (Ne.symm hji)]
      simp [hterm]
    simp [inner, Finset.mul_sum]
  rw [hs0, hsS]
  field_simp [hc2ne]
  ring

/-! ## 2. G04: Soft Spin-2 Ward Identity & Equivalence Principle Rank Boundary -/

/-- Weinberg soft spin-2 universality (`P-EP-02`): if `p_last = -∑_a p_a` and `{p_a}` is linearly
independent over `ℝ`, then `∑_a κ_a p_a + κ_last p_last = 0` forces `κ_a = κ_last` for every leg `a`. -/
theorem soft_spin2_universal_coupling
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {m : ℕ} {p : Fin m → V} (hlin : LinearIndependent ℝ p)
    {kappa : Fin m → ℝ} {kappaLast : ℝ}
    (hward : (∑ a : Fin m, kappa a • p a) + kappaLast • (-∑ a : Fin m, p a) = 0) :
    ∀ a : Fin m, kappa a = kappaLast := by
  have hcomb : ∑ a : Fin m, (kappa a - kappaLast) • p a = 0 := by
    have h1 : kappaLast • (-∑ a : Fin m, p a) = -∑ a : Fin m, kappaLast • p a := by
      simp [Finset.smul_sum]
    have h2 : ∀ a : Fin m, (kappa a - kappaLast) • p a = kappa a • p a - kappaLast • p a := by
      intro a
      exact sub_smul (kappa a) kappaLast (p a)
    simp only [h2, Finset.sum_sub_distrib]
    rw [h1] at hward
    exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hward)
  have hzero := (Fintype.linearIndependent_iff.mp hlin) (fun a => kappa a - kappaLast) hcomb
  intro a
  linarith [hzero a]

/-- Explicit reducible-kinematics counterexample when `m = 3` momenta in `ℝ^2` are linearly dependent
in orthogonal sub-channels: `p_0 + p_1 + p_2 + p_3 = 0` and `∑ κ_a p_a = 0` hold with `κ_0 = 1 ≠ 2 = κ_2`. -/
theorem reducible_kinematics_nonuniversal_counterexample :
    let p : Fin 4 → (Fin 2 → ℝ) := ![![1, 0], ![-1, 0], ![0, 1], ![0, -1]]
    let kappa : Fin 4 → ℝ := ![1, 1, 2, 2]
    (∑ a : Fin 4, p a = 0) ∧ (∑ a : Fin 4, kappa a • p a = 0) ∧ kappa 0 ≠ kappa 2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext j
    fin_cases j <;> simp [Fin.sum_univ_four]
  · ext j
    fin_cases j <;> simp [Fin.sum_univ_four]
  · simp

/-! ## 3. G05/G06 & G14: Quadratic Curvature PPN Ratio & Page Unitarity Deficit -/

/-- Effective local PPN ratio `(1 - y/3) / (1 + y/3)` for `f(R) = R + R^2/(6 m^2)` where `y = exp(-m r)`. -/
noncomputable def starobinskyPPNGamma (y : ℝ) : ℝ :=
  (1 - y / 3) / (1 + y / 3)

/-- Unscreened (`y = 1`, `m r → 0`) vs screened (`y = 0`, `m r → ∞`) limits and exact monotonic deficit
`1 - γ_PPN(y) = (2 y) / (3 + y)` across `y ∈ [0, 1]`. -/
theorem starobinsky_ppn_unscreened_vs_screened {y : ℝ} (hy0 : 0 ≤ y) :
    starobinskyPPNGamma 1 = 1 / 2 ∧
      starobinskyPPNGamma 0 = 1 ∧
      1 - starobinskyPPNGamma y = (2 * y) / (3 + y) := by
  unfold starobinskyPPNGamma
  have hden : 1 + y / 3 ≠ 0 := by linarith
  refine ⟨by norm_num, by norm_num, ?_⟩
  field_simp [hden]
  ring

/-- Page entanglement turnover deficit (`P-HORIZON-04`): once emitted radiation modes satisfy
`S_0 < 2 n s_mode`, uncorrelated thermal entropy `n s_mode` strictly exceeds the remaining horizon
entropy budget `S_0 - n s_mode`, forcing multi-mode mutual information `ΔI ≥ 2 n s_mode - S_0 > 0`. -/
theorem page_unitarity_thermal_deficit_pos
    {S0 n smode Srad : ℝ}
    (hunitary : Srad ≤ S0 - n * smode)
    (hpastPage : S0 < 2 * n * smode) :
    0 < n * smode - Srad ∧ 2 * n * smode - S0 ≤ n * smode - Srad := by
  constructor <;> linarith

end UEOTPhysicsUnification.SpacetimeEquivalenceAndGravityBounds
