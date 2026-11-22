import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Non-Perturbative Discrete Quantum Geometry, Anomaly-Free Finite-Graph Hypersurface Algebra &
# Relational Wheeler-DeWitt Closure (`P-DISCRETE-QG-01`)

Pure-kernel Lean 4 formalization addressing `NEXT_GATE` Frontier 1 (and connecting to Mathematics
v4.2 Ch. 6/40 gauge-quotient descent and Philosophy v3.1 Ch. 16–17 relational observables):

1. **Continuum Pauli-Villars Indefinite-Metric Ghost Theorem vs Discrete Planck-Graph Positivity**:
   - `pauli_villars_uv_cancellation_forces_ghost_weight` &
     `pauli_villars_indefinite_metric_negative_norm_state`: Any finite family of real
     Källén-Lehmann / Pauli-Villars spectral weights `c : Fin m → ℝ` canceling leading ultraviolet
     moments (`∑ j, c j = 0`) while nontrivial (`0 < ∑ j, |c j|`) necessarily contains both a
     strictly positive weight `0 < c j_pos` and a strictly negative ghost weight `c j_ghost < 0`,
     producing explicit negative-norm states `klNormSq c v_ghost < 0`.
   - `orthogonal_portal_kallen_lehmann_sum_one_no_uv_cancellation`: Any Hermitian multi-field
     mediator row obeying `∑ j, (o j)^2 = 1` (`AH09`) has nonnegative weights summing to `1`,
     forbidding ghost-free continuum Pauli-Villars cancellation.
   - `discrete_planck_graph_hilbert_positivity_and_uv_finiteness`: On a finite Planck-scale causal
     graph obeying `AH01`'s operational horizon floor `0 < L_min * l_P ≤ a_lat`, the kinematical
     Hilbert inner product is strictly positive definite (`ψ ≠ 0 → 0 < graphNormSq μ ψ`), while
     local equal-time field variance and discrete Laplacian operator norms are strictly positive and
     explicitly UV-finite without ghosts.

2. **Anomaly-Free Finite-Graph Hypersurface Constraint Algebra**:
   - `finite_graph_smeared_hamiltonian_zero_anomaly`: Pairwise commuting local vertex Hamiltonian
     constraints with arbitrary vertex normal-ordering subtractions satisfy `[H_ren[N₁], H_ren[N₂]] = 0`
     identically for all discrete lapses `N₁, N₂` (zero central or bilocal Schwinger anomaly).
   - `finite_graph_diffeomorphism_covariance_closure` &
     `commuting_graph_projectors_product_idempotent`: Discrete spatial graph automorphisms permute
     smeared vertex constraints without operator-ordering anomalies, and products of commuting
     local constraint projectors form exact idempotent graph projectors.

3. **Exact Operator Wheeler-DeWitt Group-Averaging Rigging Map & Relational Dirac Observables**:
   - `rigging_projector_gauge_invariant_idempotent_selfAdjoint`,
     `rigged_inner_product_posSemidef_and_strict_on_range`,
     `relational_observable_commutes_with_rigging_projector`, &
     `rigged_physical_quotient_descent_unique`: For any finite unitary/orthogonal constraint group
     representation `U : G → R`, the group-averaging rigging map `Π_phys := |G|⁻¹ ∑_{g ∈ G} U(g)`
     satisfies `Π_phys^2 = Π_phys`, `U(h) Π_phys = Π_phys`, `(1 - Π_phys) Π_phys = 0`,
     positive-semidefinite rigged inner product (strictly positive on `ran Π_phys`), exact Dirac
     observable commutation `[O_rel, Π_phys] = 0` for `O_rel = ∑_{g ∈ G} U(g) E U(g)*`, and unique
     quotient descent to `Quotient (riggingSetoid U)`.
   - `page_wootters_physical_subspace_and_relational_expectation` &
     `coupled_clock_geometry_pointer_nonvacuous_witness`: Proves the general Page-Wootters isometric
     history reduction over `ZMod N × Fib` (`finrank ℝ (ran Π_phys) = card Fib`) and instantiates an
     explicit 16-dimensional coupled Clock (`ZMod 4`) × Geometry-Source (`Bool`) × Pointer (`Bool`)
     witness with exact physical dimension `4 ≥ 2` and strictly positive relational Dirac pointer
     contrast `ΔC_rel(t₁) = 2 > 0`.
-/

namespace UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt

open Matrix
open scoped BigOperators

/-! ## 1. Continuum Pauli-Villars Ghost Obstruction vs Discrete Planck-Graph Positivity -/

/-- Weighted Källén-Lehmann / Pauli-Villars multi-species quadratic norm form. -/
def klNormSq {m : ℕ} (c : Fin m → ℝ) (v : Fin m → ℝ) : ℝ :=
  ∑ j : Fin m, c j * (v j) ^ 2

/-- Weighted discrete causal-graph Hilbert norm squared with vertex volume weights `μ_v > 0`. -/
def graphNormSq {N_sites : ℕ} (mu : Fin N_sites → ℝ) (psi : Fin N_sites → ℝ) : ℝ :=
  ∑ v : Fin N_sites, mu v * (psi v) ^ 2

/-- Continuum Pauli-Villars Indefinite-Metric Ghost Theorem:
Any finite family of real spectral weights `c : Fin m → ℝ` canceling ultraviolet divergence moments
(`∑ j, c j = 0`) while nontrivial (`0 < ∑ j, |c j|`) necessarily contains both a strictly positive
sector `0 < c j_pos` and a strictly negative indefinite-metric ghost weight `c j_ghost < 0`. -/
theorem pauli_villars_uv_cancellation_forces_ghost_weight
    {m : ℕ} (c : Fin m → ℝ)
    (hcancel : ∑ j : Fin m, c j = 0)
    (hnontriv : 0 < ∑ j : Fin m, |c j|) :
    (∃ j_pos : Fin m, 0 < c j_pos) ∧ (∃ j_ghost : Fin m, c j_ghost < 0) := by
  refine ⟨?_, ?_⟩
  · by_contra h_nonpos
    push Not at h_nonpos
    have habs : (∑ j : Fin m, |c j|) = -∑ j : Fin m, c j := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      exact abs_of_nonpos (h_nonpos j)
    linarith
  · by_contra h_nonneg
    push Not at h_nonneg
    have habs : (∑ j : Fin m, |c j|) = ∑ j : Fin m, c j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact abs_of_nonneg (h_nonneg j)
    linarith

/-- Indefinite-Metric Negative-Norm State Corollary:
Whenever `∑ j, c j = 0` and `0 < ∑ j, |c j|`, the multi-field inner product `klNormSq c` admits both
strictly positive-norm states and strictly negative-norm ghost states (`klNormSq c v_ghost < 0`),
violating Hilbert-space positivity. -/
theorem pauli_villars_indefinite_metric_negative_norm_state
    {m : ℕ} (c : Fin m → ℝ)
    (hcancel : ∑ j : Fin m, c j = 0)
    (hnontriv : 0 < ∑ j : Fin m, |c j|) :
    (∃ v_pos : Fin m → ℝ, 0 < klNormSq c v_pos) ∧
      (∃ v_ghost : Fin m → ℝ, klNormSq c v_ghost < 0) ∧
      ¬ (∀ v : Fin m → ℝ, 0 ≤ klNormSq c v) := by
  rcases pauli_villars_uv_cancellation_forces_ghost_weight c hcancel hnontriv with
    ⟨⟨j_pos, hj_pos⟩, ⟨j_ghost, hj_ghost⟩⟩
  have hsingle : ∀ j0 : Fin m, klNormSq c (fun i => if i = j0 then 1 else 0) = c j0 := by
    intro j0
    unfold klNormSq
    calc
      (∑ j : Fin m, c j * (if j = j0 then (1 : ℝ) else 0) ^ 2)
        = ∑ j : Fin m, if j = j0 then c j else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j _
          split_ifs <;> ring
      _ = c j0 := by simp
  refine ⟨⟨fun i => if i = j_pos then 1 else 0, by rw [hsingle]; exact hj_pos⟩,
    ⟨fun i => if i = j_ghost then 1 else 0, by rw [hsingle]; exact hj_ghost⟩, ?_⟩
  intro hall
  have hbad := hall (fun i => if i = j_ghost then 1 else 0)
  rw [hsingle] at hbad
  linarith

/-- Positive-norm orthogonal mediator sum rule (`AH09` Källén-Lehmann identity):
any orthogonal diagonalization row `o : Fin m → ℝ` satisfying `∑ j, (o j)^2 = 1` produces
nonnegative spectral weights `c j = (o j)^2 ≥ 0` with `∑ j, c j = 1 ≠ 0`, precluding Pauli-Villars
UV cancellation in a ghost-free Fock space. -/
theorem orthogonal_portal_kallen_lehmann_sum_one_no_uv_cancellation
    {m : ℕ} (o : Fin m → ℝ) (horth : ∑ j : Fin m, (o j) ^ 2 = 1) :
    let c : Fin m → ℝ := fun j => (o j) ^ 2
    (∀ j : Fin m, 0 ≤ c j) ∧ (∑ j : Fin m, c j) = 1 ∧ (∑ j : Fin m, c j) ≠ 0 := by
  intro c
  exact ⟨fun j => sq_nonneg (o j), horth, by rw [horth]; norm_num⟩

/-- Discrete Planck-Graph Ghost-Free Positivity and Ultraviolet Finiteness Theorem:
On a finite causal graph of `N_sites` vertices with lattice spacing `a_lat ≥ L_min * l_P > 0`
(`AH01` operational Planck floor), positive vertex measures `μ_v > 0`, normalized mode weights
`u_k ≥ 0`, `∑_k u_k = 1`, mode frequencies `0 < m_gap ≤ ω_k ≤ ω_max`, and discrete graph Laplacian
eigenvalues `0 ≤ λ_k ≤ 4 d_deg / a_lat^2`:
1. `graphNormSq μ` is strictly positive definite (`ψ ≠ 0 → 0 < graphNormSq μ ψ`, zero ghosts),
2. Equal-time local variance `∑_k u_k / (2 a_lat^3 ω_k)` is strictly positive and bounded above by
   `1 / (2 (L_min l_P)^3 m_gap)`,
3. Discrete Laplacian quadratic form `∑_k λ_k ψ_k^2` is nonnegative and bounded above by
   `(4 d_deg / (L_min l_P)^2) ∑_k ψ_k^2`. -/
theorem discrete_planck_graph_hilbert_positivity_and_uv_finiteness
    {N_sites : ℕ} {a_lat L_min l_P m_gap omega_max d_deg : ℝ}
    {mu u omega lam : Fin N_sites → ℝ}
    (hLmin : 0 < L_min) (hlP : 0 < l_P) (halat : L_min * l_P ≤ a_lat)
    (hgap : 0 < m_gap) (homax : m_gap ≤ omega_max) (hdeg : 0 ≤ d_deg)
    (hmu : ∀ v : Fin N_sites, 0 < mu v)
    (hu_nn : ∀ k : Fin N_sites, 0 ≤ u k) (hu_sum : ∑ k : Fin N_sites, u k = 1)
    (homega_lo : ∀ k : Fin N_sites, m_gap ≤ omega k)
    (homega_hi : ∀ k : Fin N_sites, omega k ≤ omega_max)
    (hlam_lo : ∀ k : Fin N_sites, 0 ≤ lam k)
    (hlam_hi : ∀ k : Fin N_sites, lam k ≤ (4 * d_deg) / a_lat ^ 2) :
    let l_floor := L_min * l_P
    let graphEqualTimeVar := ∑ k : Fin N_sites, u k / (2 * a_lat ^ 3 * omega k)
    (∀ psi : Fin N_sites → ℝ, 0 ≤ graphNormSq mu psi) ∧
      (∀ psi : Fin N_sites → ℝ, psi ≠ 0 → 0 < graphNormSq mu psi) ∧
      0 < graphEqualTimeVar ∧
      graphEqualTimeVar ≤ 1 / (2 * l_floor ^ 3 * m_gap) ∧
      (∀ psi : Fin N_sites → ℝ,
        0 ≤ ∑ k : Fin N_sites, lam k * (psi k) ^ 2 ∧
          (∑ k : Fin N_sites, lam k * (psi k) ^ 2) ≤
            ((4 * d_deg) / l_floor ^ 2) * ∑ k : Fin N_sites, (psi k) ^ 2) := by
  intro l_floor graphEqualTimeVar
  have hl_pos : 0 < l_floor := mul_pos hLmin hlP
  have halat_pos : 0 < a_lat := lt_of_lt_of_le hl_pos halat
  have homax_pos : 0 < omega_max := lt_of_lt_of_le hgap homax
  have hl3_le : l_floor ^ 3 ≤ a_lat ^ 3 := pow_le_pow_left₀ (le_of_lt hl_pos) halat 3
  have hl2_le : l_floor ^ 2 ≤ a_lat ^ 2 := pow_le_pow_left₀ (le_of_lt hl_pos) halat 2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro psi
    exact Finset.sum_nonneg (fun v _ => mul_nonneg (le_of_lt (hmu v)) (sq_nonneg (psi v)))
  · intro psi hpsi
    have hex : ∃ v0 : Fin N_sites, psi v0 ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hpsi (funext hall)
    rcases hex with ⟨v0, hv0⟩
    have hterm_pos : 0 < mu v0 * (psi v0) ^ 2 := mul_pos (hmu v0) (sq_pos_of_ne_zero hv0)
    have hle_sum : mu v0 * (psi v0) ^ 2 ≤ graphNormSq mu psi := by
      unfold graphNormSq
      exact Finset.single_le_sum (fun v _ => mul_nonneg (le_of_lt (hmu v)) (sq_nonneg (psi v)))
        (Finset.mem_univ v0)
    exact lt_of_lt_of_le hterm_pos hle_sum
  · have hden_max_pos : 0 < 2 * a_lat ^ 3 * omega_max := by positivity
    have hvar_lb : 1 / (2 * a_lat ^ 3 * omega_max) ≤ graphEqualTimeVar := by
      calc
        1 / (2 * a_lat ^ 3 * omega_max)
          = (∑ k : Fin N_sites, u k) * (1 / (2 * a_lat ^ 3 * omega_max)) := by rw [hu_sum, one_mul]
        _ = ∑ k : Fin N_sites, u k / (2 * a_lat ^ 3 * omega_max) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun k _ => mul_one_div (u k) _)
        _ ≤ ∑ k : Fin N_sites, u k / (2 * a_lat ^ 3 * omega k) := by
          refine Finset.sum_le_sum ?_
          intro k _
          have hk_pos : 0 < omega k := lt_of_lt_of_le hgap (homega_lo k)
          have hden_k_pos : 0 < 2 * a_lat ^ 3 * omega k := by positivity
          have hden_le : 2 * a_lat ^ 3 * omega k ≤ 2 * a_lat ^ 3 * omega_max :=
            mul_le_mul_of_nonneg_left (homega_hi k) (by positivity)
          exact div_le_div_of_nonneg_left (hu_nn k) hden_k_pos hden_le
    exact lt_of_lt_of_le (by positivity) hvar_lb
  · have hden_lo_pos : 0 < 2 * l_floor ^ 3 * m_gap := by positivity
    calc
      graphEqualTimeVar
        ≤ ∑ k : Fin N_sites, u k / (2 * l_floor ^ 3 * m_gap) := by
          refine Finset.sum_le_sum ?_
          intro k _
          have hden_le : 2 * l_floor ^ 3 * m_gap ≤ 2 * a_lat ^ 3 * omega k := by
            have h1 : 2 * l_floor ^ 3 ≤ 2 * a_lat ^ 3 := by linarith
            exact mul_le_mul h1 (homega_lo k) (le_of_lt hgap) (by positivity)
          exact div_le_div_of_nonneg_left (hu_nn k) hden_lo_pos hden_le
      _ = (∑ k : Fin N_sites, u k) * (1 / (2 * l_floor ^ 3 * m_gap)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun k _ => (mul_one_div (u k) _).symm)
      _ = 1 / (2 * l_floor ^ 3 * m_gap) := by rw [hu_sum, one_mul]
  · intro psi
    refine ⟨Finset.sum_nonneg (fun k _ => mul_nonneg (hlam_lo k) (sq_nonneg (psi k))), ?_⟩
    have hcap_le : (4 * d_deg) / a_lat ^ 2 ≤ (4 * d_deg) / l_floor ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hl_pos) hl2_le
    calc
      (∑ k : Fin N_sites, lam k * (psi k) ^ 2)
        ≤ ∑ k : Fin N_sites, ((4 * d_deg) / l_floor ^ 2) * (psi k) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro k _
          exact mul_le_mul_of_nonneg_right ((hlam_hi k).trans hcap_le) (sq_nonneg (psi k))
      _ = ((4 * d_deg) / l_floor ^ 2) * ∑ k : Fin N_sites, (psi k) ^ 2 := by
          rw [Finset.mul_sum]

/-! ## 2. Anomaly-Free Finite-Graph Hypersurface Constraint Algebra -/

/-- Smeared Ultralocal Finite-Graph Hamiltonian Commutator Theorem:
In any `ℝ`-algebra `R`, pairwise commuting local vertex constraints `H : Fin N_sites → R` with
arbitrary vertex normal-ordering subtractions `c : Fin N_sites → ℝ` have identically zero lapse-lapse
commutator `[H_ren[N₁], H_ren[N₂]] = 0` for all discrete lapse profiles `N₁, N₂` (zero central or
bilocal Schwinger anomaly). -/
theorem finite_graph_smeared_hamiltonian_zero_anomaly
    {N_sites : ℕ} {R : Type*} [Ring R] [Algebra ℝ R]
    (H : Fin N_sites → R) (c N1 N2 : Fin N_sites → ℝ)
    (hcomm : ∀ u v : Fin N_sites, H u * H v = H v * H u) :
    let H_ren : Fin N_sites → R := fun v => H v - algebraMap ℝ R (c v)
    let smear : (Fin N_sites → ℝ) → R :=
      fun N => ∑ v : Fin N_sites, algebraMap ℝ R (N v) * H_ren v
    smear N1 * smear N2 - smear N2 * smear N1 = 0 := by
  intro H_ren smear
  have hren_comm : ∀ u v : Fin N_sites, H_ren u * H_ren v = H_ren v * H_ren u := by
    intro u v
    dsimp [H_ren]
    have hc1 : algebraMap ℝ R (c u) * H v = H v * algebraMap ℝ R (c u) :=
      Algebra.commutes (c u) (H v)
    have hc2 : algebraMap ℝ R (c v) * H u = H u * algebraMap ℝ R (c v) :=
      Algebra.commutes (c v) (H u)
    have hc3 : algebraMap ℝ R (c u) * algebraMap ℝ R (c v) =
        algebraMap ℝ R (c v) * algebraMap ℝ R (c u) :=
      Algebra.commutes (c u) _
    calc
      (H u - algebraMap ℝ R (c u)) * (H v - algebraMap ℝ R (c v))
        = H u * H v - H u * algebraMap ℝ R (c v) - algebraMap ℝ R (c u) * H v +
            algebraMap ℝ R (c u) * algebraMap ℝ R (c v) := by noncomm_ring
      _ = H v * H u - algebraMap ℝ R (c v) * H u - H v * algebraMap ℝ R (c u) +
            algebraMap ℝ R (c v) * algebraMap ℝ R (c u) := by rw [hcomm u v, ← hc2, hc1, hc3]
      _ = (H v - algebraMap ℝ R (c v)) * (H u - algebraMap ℝ R (c u)) := by noncomm_ring
  have hterm_comm : ∀ u v : Fin N_sites,
      (algebraMap ℝ R (N1 u) * H_ren u) * (algebraMap ℝ R (N2 v) * H_ren v) =
        (algebraMap ℝ R (N2 v) * H_ren v) * (algebraMap ℝ R (N1 u) * H_ren u) := by
    intro u v
    have ha1 : algebraMap ℝ R (N1 u) * H_ren v = H_ren v * algebraMap ℝ R (N1 u) :=
      Algebra.commutes (N1 u) _
    have ha2 : algebraMap ℝ R (N2 v) * H_ren u = H_ren u * algebraMap ℝ R (N2 v) :=
      Algebra.commutes (N2 v) _
    have ha12 : algebraMap ℝ R (N1 u) * algebraMap ℝ R (N2 v) =
        algebraMap ℝ R (N2 v) * algebraMap ℝ R (N1 u) :=
      Algebra.commutes (N1 u) _
    calc
      (algebraMap ℝ R (N1 u) * H_ren u) * (algebraMap ℝ R (N2 v) * H_ren v)
        = algebraMap ℝ R (N1 u) * (H_ren u * algebraMap ℝ R (N2 v)) * H_ren v := by noncomm_ring
      _ = algebraMap ℝ R (N1 u) * (algebraMap ℝ R (N2 v) * H_ren u) * H_ren v := by rw [← ha2]
      _ = (algebraMap ℝ R (N1 u) * algebraMap ℝ R (N2 v)) * (H_ren u * H_ren v) := by noncomm_ring
      _ = (algebraMap ℝ R (N2 v) * algebraMap ℝ R (N1 u)) * (H_ren v * H_ren u) := by
          rw [ha12, hren_comm u v]
      _ = algebraMap ℝ R (N2 v) * (algebraMap ℝ R (N1 u) * H_ren v) * H_ren u := by noncomm_ring
      _ = algebraMap ℝ R (N2 v) * (H_ren v * algebraMap ℝ R (N1 u)) * H_ren u := by rw [ha1]
      _ = (algebraMap ℝ R (N2 v) * H_ren v) * (algebraMap ℝ R (N1 u) * H_ren u) := by noncomm_ring
  have hprod_eq : smear N1 * smear N2 = smear N2 * smear N1 := by
    dsimp [smear]
    calc
      (∑ u : Fin N_sites, algebraMap ℝ R (N1 u) * H_ren u) *
          (∑ v : Fin N_sites, algebraMap ℝ R (N2 v) * H_ren v)
        = ∑ u : Fin N_sites, ∑ v : Fin N_sites,
            (algebraMap ℝ R (N1 u) * H_ren u) * (algebraMap ℝ R (N2 v) * H_ren v) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun u _ => Finset.mul_sum _ _ _)
      _ = ∑ v : Fin N_sites, ∑ u : Fin N_sites,
            (algebraMap ℝ R (N2 v) * H_ren v) * (algebraMap ℝ R (N1 u) * H_ren u) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => hterm_comm u v))
      _ = (∑ v : Fin N_sites, algebraMap ℝ R (N2 v) * H_ren v) *
            (∑ u : Fin N_sites, algebraMap ℝ R (N1 u) * H_ren u) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun v _ => (Finset.mul_sum _ _ _).symm)
  rw [hprod_eq, sub_self]

/-- Discrete Spatial Diffeomorphism Covariance Closure:
If an automorphism operator `D : R` permutes local vertex constraints via `σ : Fin N_sites ≃ Fin N_sites`
(`D * H v = H (σ v) * D`), then `D` intertwines smeared vertex constraints with zero ordering anomaly:
`D * ∑_v N(v) H(v) = (∑_u N(σ⁻¹(u)) H(u)) * D`. -/
theorem finite_graph_diffeomorphism_covariance_closure
    {N_sites : ℕ} {R : Type*} [Ring R] [Algebra ℝ R]
    (H : Fin N_sites → R) (D : R) (sigma : Fin N_sites ≃ Fin N_sites)
    (N : Fin N_sites → ℝ)
    (hcov : ∀ v : Fin N_sites, D * H v = H (sigma v) * D) :
    D * (∑ v : Fin N_sites, algebraMap ℝ R (N v) * H v) =
      (∑ u : Fin N_sites, algebraMap ℝ R (N (sigma.symm u)) * H u) * D := by
  rw [Finset.mul_sum, Finset.sum_mul]
  have step1 :
      (∑ v : Fin N_sites, D * (algebraMap ℝ R (N v) * H v)) =
        ∑ v : Fin N_sites, algebraMap ℝ R (N v) * H (sigma v) * D := by
    refine Finset.sum_congr rfl ?_
    intro v _
    have hD_sc : D * algebraMap ℝ R (N v) = algebraMap ℝ R (N v) * D :=
      (Algebra.commutes (N v) D).symm
    calc
      D * (algebraMap ℝ R (N v) * H v)
        = (D * algebraMap ℝ R (N v)) * H v := (mul_assoc _ _ _).symm
      _ = (algebraMap ℝ R (N v) * D) * H v := by rw [hD_sc]
      _ = algebraMap ℝ R (N v) * (D * H v) := mul_assoc _ _ _
      _ = algebraMap ℝ R (N v) * (H (sigma v) * D) := by rw [hcov v]
      _ = algebraMap ℝ R (N v) * H (sigma v) * D := (mul_assoc _ _ _).symm
  rw [step1]
  exact Fintype.sum_equiv sigma
    (fun v => algebraMap ℝ R (N v) * H (sigma v) * D)
    (fun u => algebraMap ℝ R (N (sigma.symm u)) * H u * D)
    (fun v => by simp)

private lemma list_prod_comm_of_mem {R : Type*} [Monoid R] (q : R) (Ps : List R)
    (hq : ∀ r ∈ Ps, q * r = r * q) :
    q * Ps.prod = Ps.prod * q := by
  induction Ps with
  | nil => simp
  | cons r rs ih =>
    simp only [List.prod_cons]
    have hr : q * r = r * q := hq r List.mem_cons_self
    have hrs : q * rs.prod = rs.prod * q :=
      ih (fun s hs => hq s (List.mem_cons_of_mem _ hs))
    calc
      q * (r * rs.prod) = (q * r) * rs.prod := (mul_assoc _ _ _).symm
      _ = (r * q) * rs.prod := by rw [hr]
      _ = r * (q * rs.prod) := mul_assoc _ _ _
      _ = r * (rs.prod * q) := by rw [hrs]
      _ = (r * rs.prod) * q := (mul_assoc _ _ _).symm

/-- Product of Pairwise Commuting Local Graph Projectors:
Any finite list `Ps` of pairwise commuting idempotents (`p * p = p`, `p * q = q * p`) multiplies to
an exact idempotent graph projector `Ps.prod * Ps.prod = Ps.prod` absorbed by every vertex projector
`p ∈ Ps` (`p * Ps.prod = Ps.prod`). -/
theorem commuting_graph_projectors_product_idempotent
    {R : Type*} [Monoid R] (Ps : List R)
    (hidem : ∀ p ∈ Ps, p * p = p)
    (hcomm : ∀ p ∈ Ps, ∀ q ∈ Ps, p * q = q * p) :
    Ps.prod * Ps.prod = Ps.prod ∧ ∀ p ∈ Ps, p * Ps.prod = Ps.prod := by
  induction Ps with
  | nil =>
    exact ⟨by simp, fun _ hp => nomatch hp⟩
  | cons r rs ih =>
    rcases ih (fun a ha => hidem a (List.mem_cons_of_mem _ ha))
              (fun a ha b hb => hcomm a (List.mem_cons_of_mem _ ha)
                b (List.mem_cons_of_mem _ hb)) with ⟨hrs_idem, hrs_abs⟩
    simp only [List.prod_cons]
    have hr_idem : r * r = r := hidem r List.mem_cons_self
    have hr_comm_rs : rs.prod * r = r * rs.prod :=
      (list_prod_comm_of_mem r rs (fun s hs =>
        hcomm r List.mem_cons_self s (List.mem_cons_of_mem _ hs))).symm
    refine ⟨?_, ?_⟩
    · calc
        (r * rs.prod) * (r * rs.prod)
          = r * ((rs.prod * r) * rs.prod) := by simp [mul_assoc]
        _ = r * ((r * rs.prod) * rs.prod) := by rw [hr_comm_rs]
        _ = (r * r) * (rs.prod * rs.prod) := by simp [mul_assoc]
        _ = r * rs.prod := by rw [hr_idem, hrs_idem]
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp_tail
      · calc
          p * (p * rs.prod) = (p * p) * rs.prod := (mul_assoc _ _ _).symm
          _ = p * rs.prod := by rw [hr_idem]
      · have hpr : p * r = r * p :=
          hcomm p (List.mem_cons_of_mem _ hp_tail) r List.mem_cons_self
        calc
          p * (r * rs.prod) = (p * r) * rs.prod := (mul_assoc _ _ _).symm
          _ = (r * p) * rs.prod := by rw [hpr]
          _ = r * (p * rs.prod) := mul_assoc _ _ _
          _ = r * rs.prod := by rw [hrs_abs p hp_tail]

/-! ## 3. Exact Operator Wheeler-DeWitt Group-Averaging Rigging Map & Relational Dirac Observables -/

/-- Group-averaging Wheeler-DeWitt rigging projector `Π_phys := |G|⁻¹ ∑_{g ∈ G} U(g)`. -/
noncomputable def riggingProjector {G R : Type*} [Fintype G] [Ring R] [Algebra ℝ R]
    (U : G → R) : R :=
  algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * ∑ g : G, U g

/-- Group-averaged relational Dirac observable `O_rel := ∑_{g ∈ G} U(g) E U(g)*`
(in particular for clock-conditioned kinematical operators `E = |t₀⟩⟨t₀| ⊗ A`). -/
def relationalObservable {G R : Type*} [Fintype G] [Ring R] [StarRing R]
    (U : G → R) (E : R) : R :=
  ∑ g : G, U g * E * star (U g)

/-- Exact Operator Wheeler-DeWitt Group-Averaging Projector Theorem:
For any finite unitary/orthogonal group representation `U : G → R`:
1. `U(h) Π_phys = Π_phys` and `Π_phys U(h) = Π_phys` (exact two-sided gauge invariance),
2. `Π_phys * Π_phys = Π_phys` (idempotence),
3. `(1 - Π_phys) * Π_phys = 0` (exact Wheeler-DeWitt constraint kernel annihilation),
4. `star Π_phys = Π_phys` (self-adjointness whenever real scalars are star-fixed). -/
theorem rigging_projector_gauge_invariant_idempotent_selfAdjoint
    {G R : Type*} [Group G] [Fintype G] [Ring R] [StarRing R] [Algebra ℝ R]
    (U : G → R)
    (h_one : U 1 = 1)
    (h_mul : ∀ g h : G, U (g * h) = U g * U h)
    (h_unitary : ∀ g : G, U g * star (U g) = 1 ∧ star (U g) * U g = 1)
    (hstar_alg : ∀ c : ℝ, star (algebraMap ℝ R c) = algebraMap ℝ R c) :
    let Pi := riggingProjector U
    (∀ h : G, U h * Pi = Pi) ∧
      (∀ h : G, Pi * U h = Pi) ∧
      Pi * Pi = Pi ∧
      (1 - Pi) * Pi = 0 ∧
      star Pi = Pi := by
  intro Pi
  have hsum_left : ∀ h : G, U h * (∑ g : G, U g) = ∑ g : G, U g := by
    intro h
    rw [Finset.mul_sum]
    calc
      (∑ g : G, U h * U g) = ∑ g : G, U (h * g) :=
        Finset.sum_congr rfl (fun g _ => (h_mul h g).symm)
      _ = ∑ k : G, U k := Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
  have hsum_right : ∀ h : G, (∑ g : G, U g) * U h = ∑ g : G, U g := by
    intro h
    rw [Finset.sum_mul]
    calc
      (∑ g : G, U g * U h) = ∑ g : G, U (g * h) :=
        Finset.sum_congr rfl (fun g _ => (h_mul g h).symm)
      _ = ∑ k : G, U k := Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun _ => rfl)
  have hleft : ∀ h : G, U h * Pi = Pi := by
    intro h
    dsimp [Pi, riggingProjector]
    have hc : U h * algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) =
        algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * U h :=
      (Algebra.commutes _ (U h)).symm
    calc
      U h * (algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * ∑ g : G, U g)
        = (U h * algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹)) * ∑ g : G, U g := (mul_assoc _ _ _).symm
      _ = (algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * U h) * ∑ g : G, U g := by rw [hc]
      _ = algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * (U h * ∑ g : G, U g) := mul_assoc _ _ _
      _ = algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * ∑ g : G, U g := by rw [hsum_left h]
  have hright : ∀ h : G, Pi * U h = Pi := by
    intro h
    dsimp [Pi, riggingProjector]
    rw [mul_assoc, hsum_right h]
  have hidem : Pi * Pi = Pi := by
    have hcard_pos : 0 < Fintype.card G := Fintype.card_pos
    have hcard_ne : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hcard_pos)
    have hsum_Pi : (∑ g : G, U g) * Pi = algebraMap ℝ R (Fintype.card G : ℝ) * Pi := by
      rw [Finset.sum_mul]
      calc
        (∑ g : G, U g * Pi) = ∑ _g : G, Pi :=
          Finset.sum_congr rfl (fun g _ => hleft g)
        _ = (∑ _g : G, (1 : R)) * Pi := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun _ _ => (one_mul Pi).symm)
        _ = (Fintype.card G : R) * Pi := by simp
        _ = algebraMap ℝ R (Fintype.card G : ℝ) * Pi := by rw [map_natCast]
    calc
      Pi * Pi = (algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * ∑ g : G, U g) * Pi := rfl
      _ = algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * ((∑ g : G, U g) * Pi) := mul_assoc _ _ _
      _ = algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * (algebraMap ℝ R (Fintype.card G : ℝ) * Pi) := by
          rw [hsum_Pi]
      _ = (algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * algebraMap ℝ R (Fintype.card G : ℝ)) * Pi :=
          (mul_assoc _ _ _).symm
      _ = algebraMap ℝ R (((Fintype.card G : ℝ)⁻¹) * (Fintype.card G : ℝ)) * Pi := by rw [← map_mul]
      _ = algebraMap ℝ R 1 * Pi := by rw [inv_mul_cancel₀ hcard_ne]
      _ = Pi := by rw [map_one, one_mul]
  have hwdw_ker : (1 - Pi) * Pi = 0 := by
    rw [sub_mul, one_mul, hidem, sub_self]
  have hstar_U : ∀ g : G, star (U g) = U g⁻¹ := by
    intro g
    have hinv_mul : U g⁻¹ * U g = 1 := by
      rw [← h_mul g⁻¹ g, inv_mul_cancel, h_one]
    calc
      star (U g) = 1 * star (U g) := (one_mul _).symm
      _ = (U g⁻¹ * U g) * star (U g) := by rw [hinv_mul]
      _ = U g⁻¹ * (U g * star (U g)) := mul_assoc _ _ _
      _ = U g⁻¹ * 1 := by rw [(h_unitary g).1]
      _ = U g⁻¹ := mul_one _
  have hstar_sum : star (∑ g : G, U g) = ∑ g : G, U g := by
    rw [star_sum]
    calc
      (∑ g : G, star (U g)) = ∑ g : G, U g⁻¹ :=
        Finset.sum_congr rfl (fun g _ => hstar_U g)
      _ = ∑ k : G, U k := Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)
  have hstar_Pi : star Pi = Pi := by
    dsimp [Pi, riggingProjector]
    rw [star_mul, hstar_sum, hstar_alg, Algebra.commutes]
  exact ⟨hleft, hright, hidem, hwdw_ker, hstar_Pi⟩

/-- Exact Relational Dirac Observable Commutation Theorem:
For any unitary representation `U : G → R` and any clock-conditioned kinematical operator `E : R`,
the group-averaged observable `O_rel = ∑_{g ∈ G} U(g) E U(g)*` commutes with every `U(h)` and
commutes identically with the rigging projector (`[O_rel, Π_phys] = 0`), preserving self-adjointness. -/
theorem relational_observable_commutes_with_rigging_projector
    {G R : Type*} [Group G] [Fintype G] [Ring R] [StarRing R] [Algebra ℝ R]
    (U : G → R) (E : R)
    (h_mul : ∀ g h : G, U (g * h) = U g * U h)
    (h_unitary : ∀ g : G, U g * star (U g) = 1 ∧ star (U g) * U g = 1) :
    let Pi := riggingProjector U
    let O_rel := relationalObservable U E
    (∀ h : G, U h * O_rel = O_rel * U h) ∧
      O_rel * Pi = Pi * O_rel ∧
      O_rel * Pi - Pi * O_rel = 0 ∧
      (star E = E → star O_rel = O_rel) := by
  intro Pi O_rel
  have hconj : ∀ h : G, U h * O_rel * star (U h) = O_rel := by
    intro h
    dsimp [O_rel, relationalObservable]
    rw [Finset.mul_sum, Finset.sum_mul]
    calc
      (∑ g : G, U h * (U g * E * star (U g)) * star (U h))
        = ∑ g : G, U (h * g) * E * star (U (h * g)) := by
          refine Finset.sum_congr rfl ?_
          intro g _
          have hst : star (U g) * star (U h) = star (U (h * g)) := by
            rw [h_mul h g, star_mul]
          calc
            U h * (U g * E * star (U g)) * star (U h)
              = (U h * U g) * E * (star (U g) * star (U h)) := by simp [mul_assoc]
            _ = U (h * g) * E * star (U (h * g)) := by rw [← h_mul h g, hst]
      _ = ∑ k : G, U k * E * star (U k) :=
          Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
  have hcomm_U : ∀ h : G, U h * O_rel = O_rel * U h := by
    intro h
    calc
      U h * O_rel = (U h * O_rel) * 1 := (mul_one _).symm
      _ = (U h * O_rel) * (star (U h) * U h) := by rw [(h_unitary h).2]
      _ = (U h * O_rel * star (U h)) * U h := (mul_assoc _ _ _).symm
      _ = O_rel * U h := by rw [hconj h]
  have hcomm_Pi : O_rel * Pi = Pi * O_rel := by
    dsimp [Pi, riggingProjector]
    have hc : O_rel * algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) =
        algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * O_rel :=
      (Algebra.commutes _ O_rel).symm
    have hsum : O_rel * (∑ g : G, U g) = (∑ g : G, U g) * O_rel := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun g _ => (hcomm_U g).symm)
    calc
      O_rel * (algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * ∑ g : G, U g)
        = (O_rel * algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹)) * ∑ g : G, U g := (mul_assoc _ _ _).symm
      _ = (algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * O_rel) * ∑ g : G, U g := by rw [hc]
      _ = algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * (O_rel * ∑ g : G, U g) := mul_assoc _ _ _
      _ = algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * ((∑ g : G, U g) * O_rel) := by rw [hsum]
      _ = (algebraMap ℝ R ((Fintype.card G : ℝ)⁻¹) * ∑ g : G, U g) * O_rel := (mul_assoc _ _ _).symm
  refine ⟨hcomm_U, hcomm_Pi, by rw [hcomm_Pi, sub_self], ?_⟩
  intro hE
  dsimp [O_rel, relationalObservable]
  rw [star_sum]
  refine Finset.sum_congr rfl ?_
  intro g _
  simp [star_mul, mul_assoc, hE]

private lemma dotProduct_transpose_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (v : ι → ℝ) (u : κ → ℝ) :
    dotProduct v (M.mulVec u) = dotProduct (Mᵀ.mulVec v) u := by
  calc
    dotProduct v (M.mulVec u)
      = ∑ i : ι, v i * ∑ j : κ, M i j * u j := rfl
    _ = ∑ i : ι, ∑ j : κ, v i * (M i j * u j) :=
        Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
    _ = ∑ j : κ, ∑ i : ι, (M i j * v i) * u j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
    _ = ∑ j : κ, (∑ i : ι, M i j * v i) * u j :=
        Finset.sum_congr rfl (fun j _ => (Finset.sum_mul _ _ _).symm)
    _ = dotProduct (Mᵀ.mulVec v) u := rfl

/-- Positive-Semidefinite Rigged Physical Inner Product and Null-Space Characterization:
For any orthogonal representation `U : G → Matrix d d ℝ` (`U(g) U(g)ᵀ = 1`, `U(g)ᵀ U(g) = 1`),
`Π_phys := riggingProjector U` satisfies `Π_physᵀ = Π_phys`, `Π_phys * Π_phys = Π_phys`,
`⟨ψ, Π_phys ψ⟩ = ∑_i (Π_phys ψ)_i^2 ≥ 0`, and `⟨ψ, Π_phys ψ⟩ = 0 ↔ Π_phys ψ = 0`. -/
theorem rigged_inner_product_posSemidef_and_strict_on_range
    {G d : Type*} [Group G] [Fintype G] [Fintype d] [DecidableEq d]
    (U : G → Matrix d d ℝ)
    (h_one : U 1 = 1)
    (h_mul : ∀ g h : G, U (g * h) = U g * U h)
    (h_orth : ∀ g : G, U g * (U g)ᵀ = 1 ∧ (U g)ᵀ * U g = 1) :
    let Pi := riggingProjector U
    Piᵀ = Pi ∧ Pi * Pi = Pi ∧
      (∀ psi : d → ℝ, dotProduct psi (Pi.mulVec psi) = ∑ i : d, (Pi.mulVec psi i) ^ 2) ∧
      (∀ psi : d → ℝ, 0 ≤ dotProduct psi (Pi.mulVec psi)) ∧
      (∀ psi : d → ℝ, dotProduct psi (Pi.mulVec psi) = 0 ↔ Pi.mulVec psi = 0) := by
  intro Pi
  have hstar_mat : ∀ M : Matrix d d ℝ, star M = Mᵀ := by
    intro M
    ext i j
    simp [Matrix.star_apply]
  have h_unitary : ∀ g : G, U g * star (U g) = 1 ∧ star (U g) * U g = 1 := by
    intro g
    rw [hstar_mat]
    exact h_orth g
  have hstar_alg : ∀ c : ℝ, star (algebraMap ℝ (Matrix d d ℝ) c) = algebraMap ℝ (Matrix d d ℝ) c := by
    intro c
    rw [hstar_mat]
    ext i j
    simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply, eq_comm]
  rcases rigging_projector_gauge_invariant_idempotent_selfAdjoint U h_one h_mul h_unitary hstar_alg
    with ⟨_, _, hidem, _, hstar_Pi⟩
  have hPi_symm : Piᵀ = Pi := by
    rw [← hstar_mat]
    exact hstar_Pi
  have hquad : ∀ psi : d → ℝ, dotProduct psi (Pi.mulVec psi) = ∑ i : d, (Pi.mulVec psi i) ^ 2 := by
    intro psi
    have hPi_eq : Pi = Piᵀ * Pi := by rw [hPi_symm, hidem]
    calc
      dotProduct psi (Pi.mulVec psi)
        = dotProduct psi ((Piᵀ * Pi).mulVec psi) := by nth_rw 1 [hPi_eq]
      _ = dotProduct psi (Piᵀ.mulVec (Pi.mulVec psi)) := by rw [← mulVec_mulVec]
      _ = dotProduct (Piᵀᵀ.mulVec psi) (Pi.mulVec psi) :=
          dotProduct_transpose_mulVec Piᵀ psi (Pi.mulVec psi)
      _ = dotProduct (Pi.mulVec psi) (Pi.mulVec psi) := by rw [transpose_transpose]
      _ = ∑ i : d, (Pi.mulVec psi i) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => (sq (Pi.mulVec psi i)).symm)
  refine ⟨hPi_symm, hidem, hquad, ?_, ?_⟩
  · intro psi
    rw [hquad psi]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  · intro psi
    rw [hquad psi]
    constructor
    · intro hzero
      ext i
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (Pi.mulVec psi j))).mp hzero
      exact sq_eq_zero_iff.mp (hall i (Finset.mem_univ i))
    · intro hv
      simp [hv]

/-- Canonical gauge-equivalence relation `ψ₁ ≈ ψ₂ ↔ Π_phys ψ₁ = Π_phys ψ₂` inducing the physical
quotient Hilbert space `Quotient (riggingSetoid U)` (matching Mathematics v4.2 `QuotientDescent` /
Ch. 40 `M-40.6` observable gauge-quotient structure). -/
def riggingSetoid {G d : Type*} [Fintype G] [Fintype d] [DecidableEq d]
    (U : G → Matrix d d ℝ) : Setoid (d → ℝ) where
  r x y := (riggingProjector U).mulVec x = (riggingProjector U).mulVec y
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- Unique Quotient Descent of Rigged Relational Dirac Expectations:
For every kinematical operator `E`, the rigged expectation `ψ ↦ ⟨Π_phys ψ, O_rel (Π_phys ψ)⟩`
descends uniquely to a well-defined physical observable valuation on `Quotient (riggingSetoid U)`. -/
theorem rigged_physical_quotient_descent_unique
    {G d : Type*} [Fintype G] [Fintype d] [DecidableEq d]
    (U : G → Matrix d d ℝ) (E : Matrix d d ℝ) :
    let Pi := riggingProjector U
    let O_rel := relationalObservable U E
    ∃! val : Quotient (riggingSetoid U) → ℝ,
      ∀ psi : d → ℝ, val ⟦psi⟧ = dotProduct (Pi.mulVec psi) (O_rel.mulVec (Pi.mulVec psi)) := by
  intro Pi O_rel
  refine ⟨Quotient.lift (fun psi => dotProduct (Pi.mulVec psi) (O_rel.mulVec (Pi.mulVec psi)))
    (fun a b hab => by
      change Pi.mulVec a = Pi.mulVec b at hab
      rw [hab]),
    fun _ => rfl, ?_⟩
  intro val' hval'
  ext q
  rcases Quotient.exists_rep q with ⟨psi, rfl⟩
  exact hval' psi

/-! ## 4. Page-Wootters Relational Reduction & Coupled Clock-Geometry-Pointer Witness -/

/-- Unitary/orthogonal Page-Wootters constraint group action `U(g) = S_clk^g ⊗ W^g` on
`ZMod N × Fib` indexed by `Multiplicative (ZMod N)`. -/
def pwGroupAction {N : ℕ} {Fib : Type*} [Fintype Fib] [DecidableEq Fib]
    (W : Matrix Fib Fib ℝ) (g : Multiplicative (ZMod N)) :
    Matrix (ZMod N × Fib) (ZMod N × Fib) ℝ :=
  Matrix.of fun tf' tf =>
    if tf'.1 = tf.1 + Multiplicative.toAdd g then
      (W ^ (Multiplicative.toAdd g).val) tf'.2 tf.2
    else 0

@[simp]
private lemma pwGroupAction_apply {N : ℕ} {Fib : Type*} [Fintype Fib] [DecidableEq Fib]
    (W : Matrix Fib Fib ℝ) (g : Multiplicative (ZMod N)) (t' t : ZMod N) (f' f : Fib) :
    pwGroupAction W g (t', f') (t, f) =
      if t' = t + Multiplicative.toAdd g then
        (W ^ (Multiplicative.toAdd g).val) f' f
      else 0 := rfl

/-- Unnormalized Page-Wootters history embedding `χ ↦ (t, f) ↦ (W^t χ)_f`. -/
def pwHistoryEmbed {N : ℕ} {Fib : Type*} [Fintype Fib] [DecidableEq Fib]
    (W : Matrix Fib Fib ℝ) : (Fib → ℝ) →ₗ[ℝ] (ZMod N × Fib → ℝ) where
  toFun chi tf := (W ^ tf.1.val).mulVec chi tf.2
  map_add' x y := by
    ext tf
    simp [mulVec_add]
  map_smul' c x := by
    ext tf
    simp [mulVec_smul]

/-- Clock-conditioned kinematical operator `|t₀⟩⟨t₀| ⊗ A` on `ZMod N × Fib`. -/
def clockConditionedOp {N : ℕ} {Fib : Type*} [DecidableEq (ZMod N)]
    (t0 : ZMod N) (A : Matrix Fib Fib ℝ) :
    Matrix (ZMod N × Fib) (ZMod N × Fib) ℝ :=
  fun tf' tf => if tf'.1 = t0 ∧ tf.1 = t0 then A tf'.2 tf.2 else 0

private lemma orth_pow {Fib : Type*} [Fintype Fib] [DecidableEq Fib]
    {W : Matrix Fib Fib ℝ} (h1 : W * Wᵀ = 1) (h2 : Wᵀ * W = 1) (m : ℕ) :
    (W ^ m) * (W ^ m)ᵀ = 1 ∧ (W ^ m)ᵀ * (W ^ m) = 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rcases ih with ⟨ih1, ih2⟩
    rw [pow_succ, transpose_mul]
    refine ⟨?_, ?_⟩
    · calc
        ((W ^ k) * W) * (Wᵀ * (W ^ k)ᵀ)
          = (W ^ k) * (W * Wᵀ) * (W ^ k)ᵀ := by simp [mul_assoc]
        _ = 1 := by rw [h1, mul_one, ih1]
    · calc
        (Wᵀ * (W ^ k)ᵀ) * ((W ^ k) * W)
          = Wᵀ * ((W ^ k)ᵀ * (W ^ k)) * W := by simp [mul_assoc]
        _ = 1 := by rw [ih2, mul_one, h2]

private lemma pow_zmod_val_add {N : ℕ} [NeZero N] {Fib : Type*} [Fintype Fib] [DecidableEq Fib]
    {W : Matrix Fib Fib ℝ} (hWN : W ^ N = 1) (a b : ZMod N) :
    W ^ a.val * W ^ b.val = W ^ (a + b).val := by
  have hmod : (a + b).val = (a.val + b.val) % N := ZMod.val_add a b
  have hdiv : N * ((a.val + b.val) / N) + (a + b).val = a.val + b.val := by
    rw [hmod]
    exact Nat.div_add_mod (a.val + b.val) N
  calc
    W ^ a.val * W ^ b.val = W ^ (a.val + b.val) := (pow_add W a.val b.val).symm
    _ = W ^ (N * ((a.val + b.val) / N) + (a + b).val) := by rw [hdiv]
    _ = (W ^ N) ^ ((a.val + b.val) / N) * W ^ (a + b).val := by rw [pow_add, pow_mul]
    _ = W ^ (a + b).val := by rw [hWN, one_pow, one_mul]

/-- General Page-Wootters Physical Subspace Dimension & Relational Expectation Theorem:
Whenever `W : Matrix Fib Fib ℝ` is orthogonal (`W Wᵀ = 1`, `Wᵀ W = 1`) of finite period `W ^ N = 1`
(`N ≥ 1`), the constraint group action `U = pwGroupAction W` is an exact orthogonal representation
of `Multiplicative (ZMod N)` such that:
1. `LinearMap.range (riggingProjector U).mulVecLin` is linearly isomorphic to `Fib → ℝ`, so
   `Module.finrank ℝ (LinearMap.range (riggingProjector U).mulVecLin) = Fintype.card Fib`,
2. Normalized history states `Ψ_phys χ = (√N)⁻¹ • pwHistoryEmbed W χ` lie in `ran Π_phys`,
   preserve inner products (`⟨Ψ_phys χ₁, Ψ_phys χ₂⟩ = ⟨χ₁, χ₂⟩`), and satisfy the exact relational
   Dirac expectation identity `⟨Ψ_phys χ, O_rel(t_*, A) (Ψ_phys χ)⟩ = ⟨W^{t_*} χ, A (W^{t_*} χ)⟩`. -/
theorem page_wootters_physical_subspace_and_relational_expectation
    {N : ℕ} [NeZero N] {Fib : Type*} [Fintype Fib] [DecidableEq Fib]
    (W : Matrix Fib Fib ℝ)
    (hWWt : W * Wᵀ = 1) (hWtW : Wᵀ * W = 1) (hWN : W ^ N = 1) :
    let U := pwGroupAction (N := N) W
    let Pi := riggingProjector U
    let psiPhys : (Fib → ℝ) → (ZMod N × Fib → ℝ) :=
      fun chi => ((N : ℝ).sqrt)⁻¹ • pwHistoryEmbed W chi
    (U 1 = 1 ∧ (∀ g h, U (g * h) = U g * U h) ∧ (∀ g, U g * (U g)ᵀ = 1 ∧ (U g)ᵀ * U g = 1)) ∧
      Module.finrank ℝ (LinearMap.range Pi.mulVecLin) = Fintype.card Fib ∧
      (∀ chi : Fib → ℝ, Pi.mulVec (psiPhys chi) = psiPhys chi) ∧
      (∀ chi1 chi2 : Fib → ℝ, dotProduct (psiPhys chi1) (psiPhys chi2) = dotProduct chi1 chi2) ∧
      (∀ (t_star : ZMod N) (A : Matrix Fib Fib ℝ) (chi : Fib → ℝ),
        let O_rel := relationalObservable U (clockConditionedOp t_star A)
        dotProduct (psiPhys chi) (O_rel.mulVec (psiPhys chi)) =
          dotProduct ((W ^ t_star.val).mulVec chi) (A.mulVec ((W ^ t_star.val).mulVec chi))) := by
  intro U Pi psiPhys
  have hN_pos : 0 < N := NeZero.pos N
  have hN_real_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_real_pos
  have hU_one : U 1 = 1 := by
    ext ⟨t', f'⟩ ⟨t, f⟩
    have h1 : Multiplicative.toAdd (1 : Multiplicative (ZMod N)) = 0 := rfl
    simp only [U, pwGroupAction_apply, h1, add_zero, ZMod.val_zero, pow_zero,
      Matrix.one_apply, Prod.ext_iff]
    by_cases ht : t' = t <;> by_cases hf : f' = f <;> simp [ht, hf]
  have hU_mul : ∀ g h : Multiplicative (ZMod N), U (g * h) = U g * U h := by
    intro g h
    ext ⟨t'', f''⟩ ⟨t, f⟩
    rw [mul_apply, Fintype.sum_prod_type]
    have htoAdd : Multiplicative.toAdd (g * h) =
        Multiplicative.toAdd g + Multiplicative.toAdd h := rfl
    simp only [U, pwGroupAction_apply, htoAdd]
    set a : ZMod N := Multiplicative.toAdd g
    set b : ZMod N := Multiplicative.toAdd h
    rw [Finset.sum_eq_single (t + b)]
    · simp only [↓reduceIte]
      have hab_eq : t + b + a = t + (a + b) := by abel
      rw [hab_eq]
      by_cases ht : t'' = t + (a + b)
      · simp only [ht, ↓reduceIte]
        rw [← pow_zmod_val_add hWN a b, mul_apply]
      · simp [ht]
    · intro t' _ ht'
      simp [ht']
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ _))
  have hU_orth : ∀ g : Multiplicative (ZMod N), U g * (U g)ᵀ = 1 ∧ (U g)ᵀ * U g = 1 := by
    intro g
    rcases orth_pow hWWt hWtW (Multiplicative.toAdd g).val with ⟨ho1, ho2⟩
    refine ⟨?_, ?_⟩
    · ext ⟨t1, f1⟩ ⟨t2, f2⟩
      rw [mul_apply, Fintype.sum_prod_type]
      simp only [U, transpose_apply, pwGroupAction_apply]
      set a : ZMod N := Multiplicative.toAdd g
      rw [Finset.sum_eq_single (t1 - a)]
      · have hsub : t1 - a + a = t1 := sub_add_cancel t1 a
        simp only [hsub, ↓reduceIte]
        by_cases ht : t1 = t2
        · subst ht
          simp only [↓reduceIte]
          have hentry : (∑ x : Fib, (W ^ a.val) f1 x * (W ^ a.val) f2 x) =
              ((W ^ a.val) * (W ^ a.val)ᵀ) f1 f2 := by
            rw [mul_apply]; rfl
          rw [hentry, ho1]
          simp [Matrix.one_apply]
        · have ht2 : t2 ≠ t1 := Ne.symm ht
          simp [ht, ht2, Prod.ext_iff]
      · intro t' _ ht'
        have hne : t1 ≠ t' + a := by
          intro heq
          apply ht'
          rw [heq, add_sub_cancel_right]
        simp [hne]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ _))
    · ext ⟨t1, f1⟩ ⟨t2, f2⟩
      rw [mul_apply, Fintype.sum_prod_type]
      simp only [U, transpose_apply, pwGroupAction_apply]
      set a : ZMod N := Multiplicative.toAdd g
      rw [Finset.sum_eq_single (t1 + a)]
      · simp only [↓reduceIte]
        by_cases ht : t1 = t2
        · subst ht
          simp only [↓reduceIte]
          have hentry : (∑ x : Fib, (W ^ a.val) x f1 * (W ^ a.val) x f2) =
              ((W ^ a.val)ᵀ * (W ^ a.val)) f1 f2 := by
            rw [mul_apply]; rfl
          rw [hentry, ho2]
          simp [Matrix.one_apply]
        · have ht2 : t1 + a ≠ t2 + a := fun h => ht (add_right_cancel h)
          simp [ht, ht2, Prod.ext_iff]
      · intro t' _ ht'
        simp [ht']
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ _))
  -- Exact invariance of pwHistoryEmbed W chi under U g:
  have hU_fix : ∀ (g : Multiplicative (ZMod N)) (chi : Fib → ℝ),
      (U g).mulVec (pwHistoryEmbed W chi) = pwHistoryEmbed W chi := by
    intro g chi
    ext ⟨t', f'⟩
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, U, pwGroupAction_apply, pwHistoryEmbed,
      LinearMap.coe_mk, AddHom.coe_mk]
    set a : ZMod N := Multiplicative.toAdd g
    rw [Finset.sum_eq_single (t' - a)]
    · have hsub : t' - a + a = t' := sub_add_cancel t' a
      simp only [hsub, ↓reduceIte]
      change ((W ^ a.val).mulVec ((W ^ (t' - a).val).mulVec chi)) f' =
        (W ^ t'.val).mulVec chi f'
      rw [mulVec_mulVec, pow_zmod_val_add hWN a (t' - a)]
      have hadd : a + (t' - a) = t' := add_sub_cancel a t'
      rw [hadd]
    · intro t _ ht
      have hne : t' ≠ t + a := by
        intro heq
        apply ht
        rw [heq, add_sub_cancel_right]
      simp [hne]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ _))
  have hPi_fix_raw : ∀ chi : Fib → ℝ, Pi.mulVec (pwHistoryEmbed W chi) = pwHistoryEmbed W chi := by
    intro chi
    have hcard_eq : Fintype.card (Multiplicative (ZMod N)) = N := by
      rw [Fintype.card_multiplicative, ZMod.card]
    have hsmul_mat : ∀ (c : ℝ) (S : Matrix (ZMod N × Fib) (ZMod N × Fib) ℝ)
        (v : ZMod N × Fib → ℝ),
        (algebraMap ℝ (Matrix (ZMod N × Fib) (ZMod N × Fib) ℝ) c * S).mulVec v = c • S.mulVec v := by
      intro c S v
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      ext idx
      change (∑ x : ZMod N × Fib, (c • S) idx x * v x) = c * ∑ x : ZMod N × Fib, S idx x * v x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by simp [Matrix.smul_apply, mul_assoc])
    dsimp [Pi, riggingProjector]
    rw [hsmul_mat, sum_mulVec]
    have hsum_eq : (∑ g : Multiplicative (ZMod N), (U g).mulVec (pwHistoryEmbed W chi)) =
        (N : ℝ) • pwHistoryEmbed W chi := by
      calc
        (∑ g : Multiplicative (ZMod N), (U g).mulVec (pwHistoryEmbed W chi))
          = ∑ _g : Multiplicative (ZMod N), pwHistoryEmbed W chi :=
            Finset.sum_congr rfl (fun g _ => hU_fix g chi)
        _ = Fintype.card (Multiplicative (ZMod N)) • pwHistoryEmbed W chi := by
            rw [Finset.sum_const, Finset.card_univ]
        _ = N • pwHistoryEmbed W chi := by rw [hcard_eq]
        _ = (N : ℝ) • pwHistoryEmbed W chi := (Nat.cast_smul_eq_nsmul ℝ N _).symm
    rw [hsum_eq, smul_smul, hcard_eq, inv_mul_cancel₀ hN_ne, one_smul]
  -- Linear equivalence Fib → ℝ ≃ₗ[ℝ] LinearMap.range Pi.mulVecLin:
  have hstar_mat : ∀ M : Matrix (ZMod N × Fib) (ZMod N × Fib) ℝ, star M = Mᵀ := by
    intro M; ext i j; simp [Matrix.star_apply]
  have h_unitary : ∀ g, U g * star (U g) = 1 ∧ star (U g) * U g = 1 := by
    intro g; rw [hstar_mat]; exact hU_orth g
  have hstar_alg : ∀ c : ℝ,
      star (algebraMap ℝ (Matrix (ZMod N × Fib) (ZMod N × Fib) ℝ) c) =
        algebraMap ℝ (Matrix (ZMod N × Fib) (ZMod N × Fib) ℝ) c := by
    intro c; rw [hstar_mat]; ext i j; simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply, eq_comm]
  rcases rigging_projector_gauge_invariant_idempotent_selfAdjoint U hU_one hU_mul h_unitary hstar_alg
    with ⟨hU_Pi, _, hidem_Pi, _, _⟩
  let toRange : (Fib → ℝ) →ₗ[ℝ] LinearMap.range Pi.mulVecLin :=
    { toFun := fun chi => ⟨pwHistoryEmbed W chi, ⟨pwHistoryEmbed W chi, hPi_fix_raw chi⟩⟩
      map_add' := fun x y => Subtype.ext (map_add (pwHistoryEmbed W) x y)
      map_smul' := fun c x => Subtype.ext (map_smul (pwHistoryEmbed W) c x) }
  let fromRange : LinearMap.range Pi.mulVecLin →ₗ[ℝ] (Fib → ℝ) :=
    { toFun := fun v f => v.1 (0, f)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hleft_inv : Function.LeftInverse fromRange toRange := by
    intro chi
    ext f
    change (W ^ (0 : ZMod N).val).mulVec chi f = chi f
    simp [ZMod.val_zero]
  have hright_inv : Function.RightInverse fromRange toRange := by
    rintro ⟨psi, psi0, hpsi0⟩
    apply Subtype.ext
    have hPi_psi : Pi.mulVec psi = psi := by
      change Pi.mulVec psi0 = psi at hpsi0
      rw [← hpsi0, mulVec_mulVec, hidem_Pi]
    ext ⟨t, f⟩
    have hUt_psi : (U (Multiplicative.ofAdd t)).mulVec psi = psi := by
      rw [← hPi_psi, mulVec_mulVec, hU_Pi (Multiplicative.ofAdd t)]
    have heval := congrFun hUt_psi (t, f)
    change (W ^ t.val).mulVec (fun f0 => psi (0, f0)) f = psi (t, f)
    rw [← heval]
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, U, pwGroupAction_apply, toAdd_ofAdd]
    symm
    rw [Finset.sum_eq_single 0]
    · simp
    · intro t' _ ht'
      have hne : t ≠ t' + t := by
        intro heq
        apply ht'
        have : t' + t = 0 + t := by rw [zero_add, ← heq]
        exact add_right_cancel this
      simp [hne]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ _))
  let equivRange : (Fib → ℝ) ≃ₗ[ℝ] LinearMap.range Pi.mulVecLin :=
    LinearEquiv.ofLinearMap toRange fromRange
      (LinearMap.ext hright_inv) (LinearMap.ext hleft_inv)
  have hfinrank : Module.finrank ℝ (LinearMap.range Pi.mulVecLin) = Fintype.card Fib := by
    rw [← equivRange.finrank_eq, Module.finrank_pi]
  have hPi_psi : ∀ chi : Fib → ℝ, Pi.mulVec (psiPhys chi) = psiPhys chi := by
    intro chi
    dsimp [psiPhys]
    rw [mulVec_smul, hPi_fix_raw chi]
  have hW_isom : ∀ (m : ℕ) (c1 c2 : Fib → ℝ),
      dotProduct ((W ^ m).mulVec c1) ((W ^ m).mulVec c2) = dotProduct c1 c2 := by
    intro m c1 c2
    rcases orth_pow hWWt hWtW m with ⟨_, ho2⟩
    calc
      dotProduct ((W ^ m).mulVec c1) ((W ^ m).mulVec c2)
        = dotProduct ((W ^ m)ᵀ.mulVec ((W ^ m).mulVec c1)) c2 :=
            dotProduct_transpose_mulVec (W ^ m) ((W ^ m).mulVec c1) c2
      _ = dotProduct (((W ^ m)ᵀ * (W ^ m)).mulVec c1) c2 := by rw [mulVec_mulVec]
      _ = dotProduct c1 c2 := by rw [ho2, one_mulVec]
  have hisom : ∀ chi1 chi2 : Fib → ℝ,
      dotProduct (psiPhys chi1) (psiPhys chi2) = dotProduct chi1 chi2 := by
    intro chi1 chi2
    have hsqrt_sq : ((N : ℝ).sqrt)⁻¹ * ((N : ℝ).sqrt)⁻¹ = (N : ℝ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (le_of_lt hN_real_pos)]
    dsimp [psiPhys]
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hsqrt_sq]
    change (N : ℝ)⁻¹ * ∑ x : ZMod N × Fib,
      ((W ^ x.1.val).mulVec chi1 x.2) * ((W ^ x.1.val).mulVec chi2 x.2) = dotProduct chi1 chi2
    rw [Fintype.sum_prod_type]
    have hslice : (∑ t : ZMod N, ∑ f : Fib,
        ((W ^ t.val).mulVec chi1 f) * ((W ^ t.val).mulVec chi2 f)) =
        (N : ℝ) * dotProduct chi1 chi2 := by
      calc
        (∑ t : ZMod N, dotProduct ((W ^ t.val).mulVec chi1) ((W ^ t.val).mulVec chi2))
          = ∑ _t : ZMod N, dotProduct chi1 chi2 :=
            Finset.sum_congr rfl (fun t _ => hW_isom t.val chi1 chi2)
        _ = (Fintype.card (ZMod N) : ℝ) * dotProduct chi1 chi2 := by simp
        _ = (N : ℝ) * dotProduct chi1 chi2 := by rw [ZMod.card N]
    rw [hslice, ← mul_assoc, inv_mul_cancel₀ hN_ne, one_mul]
  -- Exact relational Dirac observable expectation formula:
  have hrel_exp : ∀ (t_star : ZMod N) (A : Matrix Fib Fib ℝ) (chi : Fib → ℝ),
      dotProduct (psiPhys chi)
        ((relationalObservable U (clockConditionedOp t_star A)).mulVec (psiPhys chi)) =
        dotProduct ((W ^ t_star.val).mulVec chi) (A.mulVec ((W ^ t_star.val).mulVec chi)) := by
    intro t_star A chi
    let E := clockConditionedOp t_star A
    have hUt_inv : ∀ g : Multiplicative (ZMod N), (U g)ᵀ = U g⁻¹ := by
      intro g
      have hinv_U : U g⁻¹ * U g = 1 := by rw [← hU_mul, inv_mul_cancel, hU_one]
      calc
        (U g)ᵀ = 1 * (U g)ᵀ := (one_mul _).symm
        _ = (U g⁻¹ * U g) * (U g)ᵀ := by rw [hinv_U]
        _ = U g⁻¹ * (U g * (U g)ᵀ) := mul_assoc _ _ _
        _ = U g⁻¹ := by rw [(hU_orth g).1, mul_one]
    have hUt_fix : ∀ g : Multiplicative (ZMod N), (U g)ᵀ.mulVec (psiPhys chi) = psiPhys chi := by
      intro g
      rw [hUt_inv g]
      dsimp [psiPhys]
      rw [mulVec_smul, hU_fix g⁻¹ chi]
    have hterm : ∀ g : Multiplicative (ZMod N),
        dotProduct (psiPhys chi) ((U g * E * star (U g)).mulVec (psiPhys chi)) =
          dotProduct (psiPhys chi) (E.mulVec (psiPhys chi)) := by
      intro g
      rw [hstar_mat (U g), mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hUt_fix g,
        dotProduct_transpose_mulVec (U g) (psiPhys chi) (E.mulVec (psiPhys chi)), hUt_fix g]
    have hE_exp : dotProduct (psiPhys chi) (E.mulVec (psiPhys chi)) =
        (N : ℝ)⁻¹ * dotProduct ((W ^ t_star.val).mulVec chi)
          (A.mulVec ((W ^ t_star.val).mulVec chi)) := by
      have hsqrt_sq : ((N : ℝ).sqrt)⁻¹ * ((N : ℝ).sqrt)⁻¹ = (N : ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (le_of_lt hN_real_pos)]
      dsimp [psiPhys]
      rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          ← mul_assoc, hsqrt_sq]
      congr 1
      change (∑ x : ZMod N × Fib, pwHistoryEmbed W chi x *
        ∑ y : ZMod N × Fib, (if x.1 = t_star ∧ y.1 = t_star then A x.2 y.2 else 0) *
          pwHistoryEmbed W chi y) =
        dotProduct ((W ^ t_star.val).mulVec chi) (A.mulVec ((W ^ t_star.val).mulVec chi))
      rw [Fintype.sum_prod_type, Finset.sum_eq_single t_star]
      · refine Finset.sum_congr rfl (fun f' _ => ?_)
        congr 1
        rw [Fintype.sum_prod_type, Finset.sum_eq_single t_star]
        · simp [pwHistoryEmbed, mulVec, dotProduct]
        · intro t _ ht
          simp [ht]
        · intro hmem
          exact False.elim (hmem (Finset.mem_univ _))
      · intro t' _ ht'
        simp [ht']
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ _))
    change dotProduct (psiPhys chi)
      ((∑ g : Multiplicative (ZMod N), U g * E * star (U g)).mulVec (psiPhys chi)) = _
    rw [sum_mulVec, dotProduct_sum]
    calc
      (∑ g : Multiplicative (ZMod N),
          dotProduct (psiPhys chi) ((U g * E * star (U g)).mulVec (psiPhys chi)))
        = ∑ _g : Multiplicative (ZMod N), dotProduct (psiPhys chi) (E.mulVec (psiPhys chi)) :=
          Finset.sum_congr rfl (fun g _ => hterm g)
      _ = (Fintype.card (Multiplicative (ZMod N)) : ℝ) *
            dotProduct (psiPhys chi) (E.mulVec (psiPhys chi)) := by simp
      _ = (N : ℝ) * ((N : ℝ)⁻¹ * dotProduct ((W ^ t_star.val).mulVec chi)
            (A.mulVec ((W ^ t_star.val).mulVec chi))) := by
          rw [Fintype.card_multiplicative, ZMod.card, hE_exp]
      _ = dotProduct ((W ^ t_star.val).mulVec chi) (A.mulVec ((W ^ t_star.val).mulVec chi)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hN_ne, one_mul]
  exact ⟨⟨hU_one, hU_mul, hU_orth⟩, hfinrank, hPi_psi, hisom, hrel_exp⟩

/-- Explicit coupled Geometry-Source (`Bool`) × Pointer (`Bool`) step unitary `W_cgp`:
- Branch `false` (vacuum discrete FRW/Regge geometry): identity on pointer,
- Branch `true` (source-dressed curved Regge sector): quarter-turn pointer rotation `R_{π/2}`. -/
def cgpStepMatrix : Matrix (Bool × Bool) (Bool × Bool) ℝ :=
  fun bp' bp =>
    match bp'.1, bp.1 with
    | false, false => if bp'.2 = bp.2 then 1 else 0
    | true, true =>
        match bp'.2, bp.2 with
        | false, false => 0
        | false, true => -1
        | true, false => 1
        | true, true => 0
    | _, _ => 0

/-- Pointer Pauli-`Z` readout matrix `I_branch ⊗ diag(+1, -1)` on `Bool × Bool`. -/
def cgpPointerZ : Matrix (Bool × Bool) (Bool × Bool) ℝ :=
  fun bp' bp =>
    if bp' = bp then (if bp.2 = false then 1 else -1) else 0

/-- Flagship Non-Vacuous Coupled Clock-Geometry-Pointer Wheeler-DeWitt Witness Theorem:
On the 16-dimensional kinematical Hilbert space `ZMod 4 × (Bool × Bool)` with constraint group
action `U = pwGroupAction cgpStepMatrix`:
1. `Π_phys * Π_phys = Π_phys` and `∀ h, U h * Π_phys = Π_phys`,
2. Exact Dirac observable commutation `[O_rel(t₁, Z_ptr), Π_phys] = 0`,
3. Non-vacuous physical Hilbert space dimension `finrank ℝ (ran Π_phys) = 4 ≥ 2`,
4. Two orthonormal physical Wheeler-DeWitt states `Ψ₀, Ψ₁` (`(1 - Π_phys) Ψ_b = 0`,
   `⟨Ψ₀, Ψ₀⟩ = 1`, `⟨Ψ₁, Ψ₁⟩ = 1`, `⟨Ψ₀, Ψ₁⟩ = 0`),
5. Identical initial relational pointer readout at `t₀ = 0` (`ΔC_rel(0) = 0`) and strictly
   positive relational Dirac pointer contrast at `t₁ = 1`:
   `⟨Ψ₀, O_rel(1, Z_ptr) Ψ₀⟩ - ⟨Ψ₁, O_rel(1, Z_ptr) Ψ₁⟩ = 2 > 0`. -/
theorem coupled_clock_geometry_pointer_nonvacuous_witness :
    let U := pwGroupAction (N := 4) cgpStepMatrix
    let Pi := riggingProjector U
    let O_rel_0 := relationalObservable U (clockConditionedOp (0 : ZMod 4) cgpPointerZ)
    let O_rel_1 := relationalObservable U (clockConditionedOp (1 : ZMod 4) cgpPointerZ)
    let chi0 : Bool × Bool → ℝ := fun bp => if bp = (false, false) then 1 else 0
    let chi1 : Bool × Bool → ℝ := fun bp => if bp = (true, false) then 1 else 0
    let Psi0 : ZMod 4 × (Bool × Bool) → ℝ :=
      (((4 : ℕ) : ℝ).sqrt)⁻¹ • pwHistoryEmbed cgpStepMatrix chi0
    let Psi1 : ZMod 4 × (Bool × Bool) → ℝ :=
      (((4 : ℕ) : ℝ).sqrt)⁻¹ • pwHistoryEmbed cgpStepMatrix chi1
    Pi * Pi = Pi ∧
      (∀ h, U h * Pi = Pi) ∧
      O_rel_1 * Pi - Pi * O_rel_1 = 0 ∧
      Module.finrank ℝ (LinearMap.range Pi.mulVecLin) = 4 ∧
      2 ≤ Module.finrank ℝ (LinearMap.range Pi.mulVecLin) ∧
      Pi.mulVec Psi0 = Psi0 ∧ Pi.mulVec Psi1 = Psi1 ∧
      (1 - Pi).mulVec Psi0 = 0 ∧ (1 - Pi).mulVec Psi1 = 0 ∧
      dotProduct Psi0 Psi0 = 1 ∧ dotProduct Psi1 Psi1 = 1 ∧ dotProduct Psi0 Psi1 = 0 ∧
      dotProduct Psi0 (O_rel_0.mulVec Psi0) - dotProduct Psi1 (O_rel_0.mulVec Psi1) = 0 ∧
      dotProduct Psi0 (O_rel_1.mulVec Psi0) - dotProduct Psi1 (O_rel_1.mulVec Psi1) = 2 ∧
      0 < dotProduct Psi0 (O_rel_1.mulVec Psi0) - dotProduct Psi1 (O_rel_1.mulVec Psi1) := by
  intro U Pi O_rel_0 O_rel_1 chi0 chi1 Psi0 Psi1
  have hWWt : cgpStepMatrix * cgpStepMatrixᵀ = 1 := by
    ext ⟨b1, p1⟩ ⟨b2, p2⟩
    rw [mul_apply, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Matrix.one_apply, transpose_apply, Prod.ext_iff]
    cases b1 <;> cases p1 <;> cases b2 <;> cases p2 <;> norm_num [cgpStepMatrix]
  have hWtW : cgpStepMatrixᵀ * cgpStepMatrix = 1 := by
    ext ⟨b1, p1⟩ ⟨b2, p2⟩
    rw [mul_apply, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Matrix.one_apply, transpose_apply, Prod.ext_iff]
    cases b1 <;> cases p1 <;> cases b2 <;> cases p2 <;> norm_num [cgpStepMatrix]
  have hW4 : cgpStepMatrix ^ 4 = 1 := by
    have h4 : cgpStepMatrix ^ 4 =
        (cgpStepMatrix * cgpStepMatrix) * (cgpStepMatrix * cgpStepMatrix) := by
      simp [pow_succ, mul_assoc]
    rw [h4]
    ext ⟨b1, p1⟩ ⟨b2, p2⟩
    simp only [mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, Matrix.one_apply, Prod.ext_iff]
    cases b1 <;> cases p1 <;> cases b2 <;> cases p2 <;> norm_num [cgpStepMatrix]
  rcases page_wootters_physical_subspace_and_relational_expectation
      (N := 4) cgpStepMatrix hWWt hWtW hW4 with
    ⟨⟨hU_one, hU_mul, hU_orth⟩, hfinrank, hPi_psi, hisom, hrel_exp⟩
  have hstar_mat : ∀ M : Matrix (ZMod 4 × (Bool × Bool)) (ZMod 4 × (Bool × Bool)) ℝ,
      star M = Mᵀ := by
    intro M; ext i j; simp [Matrix.star_apply]
  have h_unitary : ∀ g, U g * star (U g) = 1 ∧ star (U g) * U g = 1 := by
    intro g; rw [hstar_mat]; exact hU_orth g
  have hstar_alg : ∀ c : ℝ,
      star (algebraMap ℝ (Matrix (ZMod 4 × (Bool × Bool)) (ZMod 4 × (Bool × Bool)) ℝ) c) =
        algebraMap ℝ (Matrix (ZMod 4 × (Bool × Bool)) (ZMod 4 × (Bool × Bool)) ℝ) c := by
    intro c; rw [hstar_mat]; ext i j; simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply, eq_comm]
  rcases rigging_projector_gauge_invariant_idempotent_selfAdjoint U hU_one hU_mul h_unitary hstar_alg
    with ⟨hU_Pi, _, hidem, _, _⟩
  rcases relational_observable_commutes_with_rigging_projector
      U (clockConditionedOp (1 : ZMod 4) cgpPointerZ) hU_mul h_unitary with
    ⟨_, _, hcomm_1, _⟩
  have hcard4 : Fintype.card (Bool × Bool) = 4 := by decide
  have hrank4 : Module.finrank ℝ (LinearMap.range Pi.mulVecLin) = 4 := hfinrank.trans hcard4
  have hPsi0 : Pi.mulVec Psi0 = Psi0 := hPi_psi chi0
  have hPsi1 : Pi.mulVec Psi1 = Psi1 := hPi_psi chi1
  have hker0 : (1 - Pi).mulVec Psi0 = 0 := by rw [sub_mulVec, one_mulVec, hPsi0, sub_self]
  have hker1 : (1 - Pi).mulVec Psi1 = 0 := by rw [sub_mulVec, one_mulVec, hPsi1, sub_self]
  have hnorm0 : dotProduct Psi0 Psi0 = 1 := by
    exact (hisom chi0 chi0).trans (by simp [chi0, dotProduct])
  have hnorm1 : dotProduct Psi1 Psi1 = 1 := by
    exact (hisom chi1 chi1).trans (by simp [chi1, dotProduct])
  have horth01 : dotProduct Psi0 Psi1 = 0 := by
    exact (hisom chi0 chi1).trans (by simp [chi0, chi1, dotProduct])
  have hexp0_t0 : dotProduct Psi0 (O_rel_0.mulVec Psi0) = 1 := by
    refine (hrel_exp (0 : ZMod 4) cgpPointerZ chi0).trans ?_
    simp [ZMod.val_zero, chi0, cgpPointerZ, mulVec, dotProduct, Fintype.sum_prod_type]
  have hexp1_t0 : dotProduct Psi1 (O_rel_0.mulVec Psi1) = 1 := by
    refine (hrel_exp (0 : ZMod 4) cgpPointerZ chi1).trans ?_
    simp [ZMod.val_zero, chi1, cgpPointerZ, mulVec, dotProduct, Fintype.sum_prod_type]
  have hexp0_t1 : dotProduct Psi0 (O_rel_1.mulVec Psi0) = 1 := by
    refine (hrel_exp (1 : ZMod 4) cgpPointerZ chi0).trans ?_
    have hval1 : (1 : ZMod 4).val = 1 := rfl
    rw [hval1, pow_one]
    simp [chi0, cgpStepMatrix, cgpPointerZ, mulVec, dotProduct, Fintype.sum_prod_type]
  have hexp1_t1 : dotProduct Psi1 (O_rel_1.mulVec Psi1) = -1 := by
    refine (hrel_exp (1 : ZMod 4) cgpPointerZ chi1).trans ?_
    have hval1 : (1 : ZMod 4).val = 1 := rfl
    rw [hval1, pow_one]
    simp [chi1, cgpStepMatrix, cgpPointerZ, mulVec, dotProduct, Fintype.sum_prod_type]
  refine ⟨hidem, hU_Pi, hcomm_1, hrank4, by linarith, hPsi0, hPsi1, hker0, hker1,
    hnorm0, hnorm1, horth01, by linarith, by linarith, by linarith⟩

end UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt
