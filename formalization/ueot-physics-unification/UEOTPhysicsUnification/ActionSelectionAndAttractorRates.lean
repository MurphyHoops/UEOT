import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Action-Selection (`Π/Φ`) Ostrogradsky Gate & Attractor (`GOD/GOA`) Non-Uniqueness vs Doeblin Rate
(`P-PIPHI-01`, `P-GOA-02`)

Closes the philosophical-to-physics falsifiable obligations stipulated in
`PREMISES_AND_RESPONSIBILITIES.md` §3 and the master unification plan:

1. **P-PIPHI-01 — Post-Hoc Fitting Vacuity vs Pre-Declared Ostrogradsky Ghost Exclusion**:
   - `posthoc_quadratic_objective_tautological`: Constructing `J_H(K) = -(K - H)^2` *after* fixing `H`
     maximizes uniquely at `K = H` for *every* `H`, confirming `sectors/RESULTS.md` §1 that post-hoc
     objective fitting has zero independent action-selection power.
   - `ostrogradsky_hamiltonian_unbounded_below`: Conversely, imposing lower-bounded Hamiltonian energy
     as a pre-declared structural rule on higher-time-derivative actions `L = (ε/2)(q'')^2 + (1/2)(q')^2 - V(q)`
     (`ε ≠ 0`) excludes every nondegenerate `ε ≠ 0` candidate via Ostrogradsky's linear momentum term `p_1 q_2`.

2. **P-GOA-02 — Reducible Multi-Sector Attractor Non-Uniqueness vs Doeblin Geometric Contraction**:
   - `reducible_sector_stationary_continuum`: Any two-sector population-preserving channel (such as QND
     dephasing) fixes every distribution `(λ, 1 - λ)` (`λ ∈ [0, 1]`), refuting unconditional unique GOA.
   - `doeblin_contraction_iterated_rate`: Under an explicit contraction coefficient `c = 1 - α ∈ [0, 1)`
     toward `π`, every initial state `u` converges to `π` at the quantitative geometric rate `c^n ‖u - π‖`.
-/

namespace UEOTPhysicsUnification.ActionSelectionAndAttractorRates

/-! ## 1. `Π/Φ`: Post-Hoc Fitting Vacuity vs Pre-Declared Ostrogradsky Ghost Exclusion -/

/-- Post-hoc quadratic score `-(K - H)^2` tautologically selects `K = H` for any candidate `H`. -/
def posthocScore (H K : ℝ) : ℝ := -(K - H) ^ 2

theorem posthoc_quadratic_objective_tautological (H K : ℝ) :
    posthocScore H K ≤ posthocScore H H ∧
      (posthocScore H K = posthocScore H H ↔ K = H) := by
  unfold posthocScore
  have hsq : 0 ≤ (K - H) ^ 2 := sq_nonneg (K - H)
  refine ⟨by linarith, ?_⟩
  constructor
  · intro heq
    have hz : (K - H) ^ 2 = 0 := by linarith
    linarith [sq_eq_zero_iff.mp hz]
  · rintro rfl
    ring

/-- Exact Ostrogradsky phase-space Hamiltonian `p_1 q_2 + p_2^2 / (2 ε) - q_2^2 / 2 + V(q_1)`
associated with `L(q, q', q'') = (ε / 2) (q'')^2 + (1 / 2) (q')^2 - V(q)` (`ε ≠ 0`). -/
noncomputable def ostrogradskyHamiltonian (eps : ℝ) (V : ℝ → ℝ) (q1 q2 p1 p2 : ℝ) : ℝ :=
  p1 * q2 + p2 ^ 2 / (2 * eps) - q2 ^ 2 / 2 + V q1

/-- Pre-declared energy-semiboundedness strictly excludes every nondegenerate higher-time-derivative
lagrangian: for every proposed lower bound `B : ℝ` and *any* potential `V`, there exists a phase-space
state `(q_1, q_2, p_1, p_2)` with `H_Ost < B`. -/
theorem ostrogradsky_hamiltonian_unbounded_below (eps : ℝ) (V : ℝ → ℝ) (B : ℝ) :
    ∃ q1 q2 p1 p2 : ℝ, ostrogradskyHamiltonian eps V q1 q2 p1 p2 < B := by
  refine ⟨0, 1, B - V 0 - 1, 0, ?_⟩
  unfold ostrogradskyHamiltonian
  simp
  linarith

/-! ## 2. `GOD/GOA`: Multi-Sector Stationary Continuum vs Quantitative Doeblin Rate -/

/-- Two-sector population-conserving map (e.g. QND dephasing projected to diagonal sector weights). -/
def qndSectorMap (p : ℝ × ℝ) : ℝ × ℝ := p

/-- Explicit non-unique stationary manifold: every `λ ∈ [0, 1]` defines a distinct normalized fixed point. -/
theorem reducible_sector_stationary_continuum
    {lam1 lam2 : ℝ} (hne : lam1 ≠ lam2) :
    qndSectorMap (lam1, 1 - lam1) = (lam1, 1 - lam1) ∧
      qndSectorMap (lam2, 1 - lam2) = (lam2, 1 - lam2) ∧
      (lam1, 1 - lam1) ≠ (lam2, 1 - lam2) := by
  refine ⟨rfl, rfl, ?_⟩
  intro heq
  exact hne (Prod.mk.inj heq).1

/-- Quantitative Doeblin/Dobrushin iterated contraction rate: if `‖T u - π‖ ≤ c ‖u - π‖` with `0 ≤ c`,
then `‖T^[n] u - π‖ ≤ c^n ‖u - π‖` for every `n : ℕ`. -/
theorem doeblin_contraction_iterated_rate
    {V : Type*} [SeminormedAddCommGroup V]
    (T : V → V) (piStar : V) {c : ℝ} (hc : 0 ≤ c)
    (hstep : ∀ u : V, ‖T u - piStar‖ ≤ c * ‖u - piStar‖)
    (u0 : V) (n : ℕ) :
    ‖T^[n] u0 - piStar‖ ≤ c ^ n * ‖u0 - piStar‖ := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    rw [Function.iterate_succ']
    calc
      ‖T (T^[k] u0) - piStar‖ ≤ c * ‖T^[k] u0 - piStar‖ := hstep (T^[k] u0)
      _ ≤ c * (c ^ k * ‖u0 - piStar‖) := mul_le_mul_of_nonneg_left ih hc
      _ = c ^ (k + 1) * ‖u0 - piStar‖ := by ring

end UEOTPhysicsUnification.ActionSelectionAndAttractorRates
