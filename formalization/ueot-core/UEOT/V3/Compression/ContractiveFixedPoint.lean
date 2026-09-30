import UEOT.V3.FiniteDiscountedControl
import UEOT.V3.FiniteDobrushin

/-!
# Experimental M-CF — contractive fixed-point certificate calculus

This module tests a second-order compression between discounted Bellman
contraction and finite Dobrushin contraction.

The core deliberately assumes less than a `MetricSpace`.  It only records the
distance-like facts actually used by the shared fixed-point certificates:
nonnegativity, separation at zero, triangle inequality, and one-step
contraction.  This lets the finite total-variation law distance participate
directly without rebuilding an ambient metric-space instance.

Fixed-point *existence* is intentionally outside this core.  Bellman existence
comes from Banach/`ContractingWith`; Dobrushin existence in frozen P-GOA-02 is
supplied by P-GOA-01.  The common layer owns uniqueness, geometric transport,
residual error, and fixed-point perturbation certificates.
-/

namespace UEOT.V3.Compression.ContractiveFixedPoint

open Function

universe uX uS uA

/-- Minimal real-valued distance-like interface needed by the shared
contraction arguments.  Symmetry and topology are deliberately unnecessary. -/
structure DistanceLike (X : Type uX) where
  d : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ d x y
  triangle : ∀ x y z, d x z ≤ d x y + d y z
  eq_of_zero : ∀ {x y}, d x y = 0 → x = y

/-- A strict contraction relative to a `DistanceLike` certificate. -/
structure ContractiveWith {X : Type uX}
    (D : DistanceLike X) (alpha : ℝ) (F : X → X) : Prop where
  alpha_nonneg : 0 ≤ alpha
  alpha_lt_one : alpha < 1
  contract : ∀ x y, D.d (F x) (F y) ≤ alpha * D.d x y

namespace ContractiveWith

variable {X : Type uX} {D : DistanceLike X} {alpha : ℝ} {F : X → X}

theorem one_sub_alpha_pos (hF : ContractiveWith D alpha F) :
    0 < 1 - alpha :=
  sub_pos.mpr hF.alpha_lt_one

/-- Two fixed points of the same strict contraction coincide. -/
theorem fixedPoint_unique
    (hF : ContractiveWith D alpha F)
    {x y : X} (hx : F x = x) (hy : F y = y) :
    x = y := by
  have hc := hF.contract x y
  rw [hx, hy] at hc
  have hnonneg := D.nonneg x y
  have hz : D.d x y = 0 := by
    nlinarith [hF.alpha_lt_one]
  exact D.eq_of_zero hz

/-- A fixed point remains fixed under every iterate. -/
theorem iterate_fixed_of_fixed
    {xstar : X} (hstar : F xstar = xstar) :
    ∀ n : ℕ, (F^[n]) xstar = xstar := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hstar]

/-- Geometric contraction of equal-time iterates. -/
theorem iterate_le
    (hF : ContractiveWith D alpha F)
    (x y : X) :
    ∀ n : ℕ,
      D.d ((F^[n]) x) ((F^[n]) y) ≤ alpha ^ n * D.d x y := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      calc
        D.d (F ((F^[n]) x)) (F ((F^[n]) y))
            ≤ alpha * D.d ((F^[n]) x) ((F^[n]) y) :=
          hF.contract _ _
        _ ≤ alpha * (alpha ^ n * D.d x y) := by
          exact mul_le_mul_of_nonneg_left ih hF.alpha_nonneg
        _ = alpha ^ (n + 1) * D.d x y := by
          rw [pow_succ]
          ring

/-- A-posteriori fixed-point error from the one-step residual. -/
theorem error_le_residual
    (hF : ContractiveWith D alpha F)
    (x : X) {xstar : X} (hstar : F xstar = xstar) :
    D.d x xstar ≤ D.d x (F x) / (1 - alpha) := by
  have htri := D.triangle x (F x) xstar
  have hc := hF.contract x xstar
  rw [hstar] at hc
  have hbound :
      D.d x xstar ≤ D.d x (F x) + alpha * D.d x xstar :=
    htri.trans (add_le_add le_rfl hc)
  rw [le_div_iff₀ hF.one_sub_alpha_pos]
  nlinarith

/-- Fixed-point perturbation certificate.  Only the baseline map `F` needs to
be contractive; `G` may be arbitrary once one fixed point and the cross-map
defect at that point are known. -/
theorem fixedPoint_perturbation
    (hF : ContractiveWith D alpha F)
    (G : X → X)
    {xstar ystar : X}
    (hx : F xstar = xstar)
    (hy : G ystar = ystar)
    (epsilon : ℝ)
    (hcross : D.d (F ystar) (G ystar) ≤ epsilon) :
    D.d xstar ystar ≤ epsilon / (1 - alpha) := by
  have htri := D.triangle (F xstar) (F ystar) (G ystar)
  have hc := hF.contract xstar ystar
  rw [hx] at hc
  rw [hy] at hcross
  have hbound :
      D.d xstar ystar ≤ alpha * D.d xstar ystar + epsilon := by
    rw [hx, hy] at htri
    exact htri.trans (add_le_add hc hcross)
  rw [le_div_iff₀ hF.one_sub_alpha_pos]
  nlinarith

end ContractiveWith

/-! ## Bellman adapter -/

open UEOT.V3.FiniteDiscountedControl

/-- Ordinary metric distance as a `DistanceLike`. -/
def metricDistanceLike (X : Type uX) [MetricSpace X] : DistanceLike X where
  d := dist
  nonneg := fun _ _ => dist_nonneg
  triangle := fun x y z => dist_triangle x y z
  eq_of_zero := dist_eq_zero.mp

theorem bellman_contractiveWith
    {X : Type uX} [Fintype X]
    {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (M : Model X A) :
    ContractiveWith (metricDistanceLike (X → ℝ)) M.discount M.bellman := by
  refine ⟨M.discount_pos.le, M.discount_lt_one, ?_⟩
  intro v w
  change dist (M.bellman v) (M.bellman w) ≤ M.discount * dist v w
  simpa using M.bellman_contracting.dist_le_mul v w

/-- Exact P-CTL-01 residual certificate through M-CF. -/
theorem bellman_valueError_le_residual_via_mcf
    {X : Type uX} [Fintype X]
    {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (M : Model X A) (v : X → ℝ) :
    dist v M.optimalValue ≤
      dist v (M.bellman v) / (1 - M.discount) := by
  exact (bellman_contractiveWith M).error_le_residual
    v M.optimalValue_fixed

/-- Bellman fixed-point uniqueness through the weak M-CF interface rather
than directly through the ambient metric-space theorem. -/
theorem bellman_fixedPoint_unique_via_mcf
    {X : Type uX} [Fintype X]
    {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (M : Model X A) {v : X → ℝ} (hv : M.bellman v = v) :
    v = M.optimalValue :=
  (bellman_contractiveWith M).fixedPoint_unique hv M.optimalValue_fixed

/-- Explicit geometric Bellman iterate error against the optimal fixed point. -/
theorem bellman_iterate_le_via_mcf
    {X : Type uX} [Fintype X]
    {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (M : Model X A) (v : X → ℝ) (n : ℕ) :
    dist ((M.bellman^[n]) v) M.optimalValue ≤
      M.discount ^ n * dist v M.optimalValue := by
  have h := (bellman_contractiveWith M).iterate_le v M.optimalValue n
  have hfixed := ContractiveWith.iterate_fixed_of_fixed
    (F := M.bellman) M.optimalValue_fixed n
  change
    dist ((M.bellman^[n]) v) ((M.bellman^[n]) M.optimalValue) ≤
      M.discount ^ n * dist v M.optimalValue at h
  rw [hfixed] at h
  exact h

/-! ## Dobrushin adapter -/

open UEOT.V3.FiniteDobrushin

section Dobrushin

variable {S : Type uS} [Fintype S] [Nonempty S]

noncomputable local instance : DecidableEq S := Classical.decEq S
local instance : MeasurableSpace S := ⊤

noncomputable def lawTVDistanceLike : DistanceLike (stdSimplex ℝ S) where
  d := lawTV
  nonneg := lawTV_nonneg
  triangle := lawTV_triangle
  eq_of_zero := lawTV_eq_zero_imp_eq _ _

theorem dobrushinAlpha_nonneg
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) :
    0 ≤ dobrushinAlpha P hP := by
  let x : S := Classical.choice inferInstance
  have hrow := rowTV_le_dobrushinAlpha P hP x x
  have htv0 : 0 ≤ rowTV P hP x x := by
    unfold rowTV FiniteProbabilityRow.tvDist
    exact UEOT.V3.TotalVariation.tvDist_nonneg _ _
  exact htv0.trans hrow

theorem dobrushin_contractiveWith
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha P hP < 1) :
    ContractiveWith lawTVDistanceLike (dobrushinAlpha P hP) (step P hP) := by
  refine ⟨dobrushinAlpha_nonneg P hP, halpha, ?_⟩
  intro mu nu
  exact tv_step_le_dobrushin P hP mu nu

/-- Dobrushin invariant-law uniqueness through the same M-CF theorem used by
the Bellman residual certificate. -/
theorem invariant_eq_of_dobrushin_lt_one_via_mcf
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha P hP < 1)
    (mu nu : stdSimplex ℝ S)
    (hmu : step P hP mu = mu) (hnu : step P hP nu = nu) :
    mu = nu :=
  (dobrushin_contractiveWith P hP halpha).fixedPoint_unique hmu hnu

/-- Exact frozen stationary perturbation bound through M-CF. -/
theorem stationary_perturbation_via_mcf
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha P hP < 1)
    (mu muhat : stdSimplex ℝ S)
    (hmu : step P hP mu = mu)
    (hmuhat : step Q hQ muhat = muhat)
    (epsilon : ℝ)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    lawTV mu muhat ≤ epsilon / (1 - dobrushinAlpha P hP) := by
  apply (dobrushin_contractiveWith P hP halpha).fixedPoint_perturbation
    (step Q hQ) hmu hmuhat epsilon
  exact tv_step_cross_le P hP Q hQ muhat epsilon hrow

/-- Out-of-sample geometric mixing certificate: once one invariant law is
given, every iterate contracts toward it at the Dobrushin geometric rate. -/
theorem dobrushin_iterate_to_invariant_le_via_mcf
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha P hP < 1)
    (mu mustar : stdSimplex ℝ S)
    (hmustar : step P hP mustar = mustar)
    (n : ℕ) :
    lawTV (((step P hP)^[n]) mu) mustar ≤
      dobrushinAlpha P hP ^ n * lawTV mu mustar := by
  have h := (dobrushin_contractiveWith P hP halpha).iterate_le mu mustar n
  have hfixedIter := ContractiveWith.iterate_fixed_of_fixed
    (F := step P hP) hmustar n
  change
    lawTV (((step P hP)^[n]) mu) (((step P hP)^[n]) mustar) ≤
      dobrushinAlpha P hP ^ n * lawTV mu mustar at h
  rw [hfixedIter] at h
  exact h

/-- Exact source-signature P-GOA-02 wrapper using M-CF for uniqueness and
stationary perturbation while retaining the frozen P-GOA-01 existence route. -/
theorem p_goa_02_via_mcf
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha P hP < 1) :
    (∃! mu : stdSimplex ℝ S, step P hP mu = mu) ∧
      ∀ (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
        (mu muhat : stdSimplex ℝ S) (epsilon : ℝ),
        step P hP mu = mu →
        step Q hQ muhat = muhat →
        (∀ x, crossRowTV P hP Q hQ x ≤ epsilon) →
        lawTV mu muhat ≤ epsilon / (1 - dobrushinAlpha P hP) := by
  constructor
  · rcases exists_invariant P hP with ⟨mu, hmu⟩
    refine ⟨mu, hmu, ?_⟩
    intro nu hnu
    exact invariant_eq_of_dobrushin_lt_one_via_mcf
      P hP halpha nu mu hnu hmu
  · intro Q hQ mu muhat epsilon hmu hmuhat hrow
    exact stationary_perturbation_via_mcf
      P hP Q hQ halpha mu muhat hmu hmuhat epsilon hrow

end Dobrushin

end UEOT.V3.Compression.ContractiveFixedPoint
