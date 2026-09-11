import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# P-INV-04 — noiseless design identifiability

For the frozen linear model `Y_t = phi_t^T theta_* + xi_t`, P-INV-04 states
that in the noiseless model with parameter space all of `R^d`, the parameter is
uniquely identified by the fixed design iff the Gram matrix
`G_N = sum_t phi_t phi_t^T` is positive definite.

Rather than introducing a matrix representation only to eliminate it again, we
formalize the equivalent Gram quadratic form

`v^T G_N v = sum_t (phi_t^T v)^2`.

Strict positivity of this quadratic form away from zero is literally
`G_N ≻ 0` and is proved equivalent to injectivity of the noiseless design map.
-/

namespace UEOT.V3.DesignIdentifiability

open scoped BigOperators

/-- Fixed linear design map `theta ↦ (phi_t^T theta)_t`. -/
def designMap {N d : ℕ} (phi : Fin N → Fin d → ℝ)
    (theta : Fin d → ℝ) : Fin N → ℝ :=
  fun t => ∑ j, phi t j * theta j

/-- Gram quadratic form `v^T G_N v = sum_t (phi_t^T v)^2`. -/
def gramQuadratic {N d : ℕ} (phi : Fin N → Fin d → ℝ)
    (v : Fin d → ℝ) : ℝ :=
  ∑ t, (designMap phi v t) ^ 2

/-- Positive definiteness of the source Gram matrix, expressed by its quadratic
form. -/
def GramPositive {N d : ℕ} (phi : Fin N → Fin d → ℝ) : Prop :=
  ∀ v : Fin d → ℝ, v ≠ 0 → 0 < gramQuadratic phi v

/-- Source notion of unique noiseless identification over the full parameter
space `R^d`. -/
def UniquelyIdentifies {N d : ℕ} (phi : Fin N → Fin d → ℝ) : Prop :=
  Function.Injective (designMap phi)

@[simp]
theorem designMap_zero {N d : ℕ} (phi : Fin N → Fin d → ℝ) :
    designMap phi (0 : Fin d → ℝ) = 0 := by
  funext t
  simp [designMap]

theorem designMap_sub {N d : ℕ} (phi : Fin N → Fin d → ℝ)
    (theta theta' : Fin d → ℝ) :
    designMap phi (theta - theta') = designMap phi theta - designMap phi theta' := by
  funext t
  simp [designMap, mul_sub, Finset.sum_sub_distrib]

/-- `G_N ≻ 0` iff the fixed noiseless design uniquely identifies every
parameter in `R^d`. This is the literal algebraic content of P-INV-04. -/
theorem p_inv_04 {N d : ℕ} (phi : Fin N → Fin d → ℝ) :
    UniquelyIdentifies phi ↔ GramPositive phi := by
  constructor
  · intro hinj v hv
    have hnonneg : 0 ≤ gramQuadratic phi v := by
      unfold gramQuadratic
      exact Finset.sum_nonneg fun i hi => sq_nonneg _
    have hne : gramQuadratic phi v ≠ 0 := by
      intro hz
      have hz_each : ∀ t : Fin N, designMap phi v t = 0 := by
        have h :=
          (Finset.sum_sq_eq_zero_iff (s := Finset.univ)
            (f := fun t : Fin N => designMap phi v t)).mp (by simpa [gramQuadratic] using hz)
        intro t
        exact h t (Finset.mem_univ t)
      have hmap : designMap phi v = designMap phi 0 := by
        funext t
        simp [hz_each t]
      exact hv (hinj hmap)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  · intro hpd theta theta' hEq
    by_contra hne
    have hv : theta - theta' ≠ 0 := sub_ne_zero.mpr hne
    have hpos := hpd (theta - theta') hv
    have hzeroMap : designMap phi (theta - theta') = 0 := by
      rw [designMap_sub, hEq, sub_self]
    have hzeroQuad : gramQuadratic phi (theta - theta') = 0 := by
      unfold gramQuadratic
      simp [hzeroMap]
    rw [hzeroQuad] at hpos
    exact lt_irrefl 0 hpos

end UEOT.V3.DesignIdentifiability
