import UEOT.V3.DesignIdentifiability
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# P-INV-05 — predictable-design OLS concentration foundation

The frozen theorem considers

`Y_t = phi_t^T theta_* + xi_t`,
`G_N = sum_t phi_t phi_t^T`,

with predictable bounded design, conditionally sub-Gaussian noise, and the
samplewise lower bound `G_N ⪰ N κ I`.

This file begins with the deterministic algebraic core.  If the OLS normal
equation is `G_N err = Z`, where `err = thetaHat - thetaStar` and
`Z = sum_t phi_t xi_t`, then Gram coercivity plus finite-dimensional
Cauchy-Schwarz gives

`(N κ)^2 ||err||_2^2 ≤ ||Z||_2^2`.

The probability layer will subsequently bound the score vector `Z` with the
exact source constants.
-/

namespace UEOT.V3.PredictableOLS

open UEOT.V3.DesignIdentifiability
open scoped BigOperators

/-- Squared Euclidean norm on finite real coordinates. -/
def sqNorm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ∑ j, (v j) ^ 2

/-- Euclidean dot product on finite real coordinates. -/
def dot {d : ℕ} (u v : Fin d → ℝ) : ℝ :=
  ∑ j, u j * v j

/-- Action of the unnormalised Gram matrix `G_N = Σ_t phi_t phi_tᵀ`. -/
def gramAction {N d : ℕ} (phi : Fin N → Fin d → ℝ)
    (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∑ t, phi t i * designMap phi v t

/-- Noise score vector `Z = Σ_t phi_t xi_t`. -/
def scoreVector {N d : ℕ} (phi : Fin N → Fin d → ℝ)
    (xi : Fin N → ℝ) : Fin d → ℝ :=
  fun i => ∑ t, phi t i * xi t

/-- Squared Euclidean norms are nonnegative. -/
theorem sqNorm_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ sqNorm v := by
  unfold sqNorm
  exact Finset.sum_nonneg fun j hj => sq_nonneg (v j)

/-- Matrix-free identity `vᵀ G_N v = gramQuadratic phi v`. -/
theorem dot_gramAction_eq_gramQuadratic {N d : ℕ}
    (phi : Fin N → Fin d → ℝ) (v : Fin d → ℝ) :
    dot v (gramAction phi v) = gramQuadratic phi v := by
  unfold dot gramAction gramQuadratic
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hsum : (∑ x, v x * phi t x) = designMap phi v t := by
    unfold designMap
    apply Finset.sum_congr rfl
    intro x hx
    ring
  calc
    ∑ x, v x * (phi t x * designMap phi v t)
        = ∑ x, (v x * phi t x) * designMap phi v t := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = (∑ x, v x * phi t x) * designMap phi v t := by
          rw [Finset.sum_mul]
    _ = designMap phi v t * designMap phi v t := by rw [hsum]
    _ = designMap phi v t ^ 2 := by ring

/-- Finite-dimensional Cauchy-Schwarz in the squared-norm notation used by
P-INV-05. -/
theorem dot_sq_le_sqNorm_mul_sqNorm {d : ℕ} (u v : Fin d → ℝ) :
    (dot u v) ^ 2 ≤ sqNorm u * sqNorm v := by
  simpa [dot, sqNorm] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) u v)

/-- Deterministic OLS error core for P-INV-05.

`hcoercive` is exactly the samplewise matrix inequality `G_N ⪰ N κ I`,
expressed through the Gram quadratic form. `hnormal` is the OLS normal equation
`G_N err = Z`.
-/
theorem gram_coercive_normalEq_sqNorm_bound
    {N d : ℕ} (hN : 0 < N)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (phi : Fin N → Fin d → ℝ)
    (err Z : Fin d → ℝ)
    (hcoercive :
      (N : ℝ) * kappa * sqNorm err ≤ gramQuadratic phi err)
    (hnormal : gramAction phi err = Z) :
    (((N : ℝ) * kappa) ^ 2) * sqNorm err ≤ sqNorm Z := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hq : 0 ≤ sqNorm err := sqNorm_nonneg err
  by_cases hq0 : sqNorm err = 0
  · simp [hq0, sqNorm_nonneg Z]
  have hqpos : 0 < sqNorm err := lt_of_le_of_ne hq (Ne.symm hq0)
  have hdot : dot err Z = gramQuadratic phi err := by
    rw [← hnormal]
    exact dot_gramAction_eq_gramQuadratic phi err
  have hlower :
      (N : ℝ) * kappa * sqNorm err ≤ dot err Z := by
    rw [hdot]
    exact hcoercive
  have hleft_nonneg : 0 ≤ (N : ℝ) * kappa * sqNorm err :=
    mul_nonneg (mul_nonneg hNreal.le hkappa.le) hq
  have hdot_nonneg : 0 ≤ dot err Z := hleft_nonneg.trans hlower
  have hsquare_lower :
      (((N : ℝ) * kappa * sqNorm err) ^ 2) ≤ (dot err Z) ^ 2 :=
    (sq_le_sq₀ hleft_nonneg hdot_nonneg).2 hlower
  have hcauchy := dot_sq_le_sqNorm_mul_sqNorm err Z
  have hcombined :
      (((N : ℝ) * kappa * sqNorm err) ^ 2) ≤
        sqNorm err * sqNorm Z :=
    hsquare_lower.trans hcauchy
  have hmul :
      sqNorm err * ((((N : ℝ) * kappa) ^ 2) * sqNorm err) ≤
        sqNorm err * sqNorm Z := by
    calc
      sqNorm err * ((((N : ℝ) * kappa) ^ 2) * sqNorm err)
          = (((N : ℝ) * kappa * sqNorm err) ^ 2) := by ring
      _ ≤ sqNorm err * sqNorm Z := hcombined
  exact le_of_mul_le_mul_left hmul hqpos

/-- Uniform coordinate control implies the standard `d R²` control of the
squared Euclidean norm. -/
theorem sqNorm_le_natCast_mul_sq_of_abs_le
    {d : ℕ} (Z : Fin d → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hcoord : ∀ j, |Z j| ≤ R) :
    sqNorm Z ≤ (d : ℝ) * R ^ 2 := by
  unfold sqNorm
  calc
    (∑ j, (Z j) ^ 2) ≤ ∑ _j : Fin d, R ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact (sq_le_sq).2 (by simpa [abs_of_nonneg hR] using hcoord j)
    _ = (d : ℝ) * R ^ 2 := by simp

/-- The deterministic P-INV-05 bridge in coordinate-threshold form. -/
theorem gram_coercive_normalEq_sqNorm_bound_of_abs_score_le
    {N d : ℕ} (hN : 0 < N)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (phi : Fin N → Fin d → ℝ)
    (err Z : Fin d → ℝ)
    (hcoercive :
      (N : ℝ) * kappa * sqNorm err ≤ gramQuadratic phi err)
    (hnormal : gramAction phi err = Z)
    (R : ℝ) (hR : 0 ≤ R)
    (hscore : ∀ j, |Z j| ≤ R) :
    (((N : ℝ) * kappa) ^ 2) * sqNorm err ≤ (d : ℝ) * R ^ 2 := by
  exact (gram_coercive_normalEq_sqNorm_bound hN kappa hkappa phi err Z
    hcoercive hnormal).trans
      (sqNorm_le_natCast_mul_sq_of_abs_le Z R hR hscore)

/-- Dividing the deterministic bound by the strictly positive Gram scale gives
an explicit squared-error estimate. -/
theorem sqNorm_error_le_of_abs_score_le
    {N d : ℕ} (hN : 0 < N)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (phi : Fin N → Fin d → ℝ)
    (err Z : Fin d → ℝ)
    (hcoercive :
      (N : ℝ) * kappa * sqNorm err ≤ gramQuadratic phi err)
    (hnormal : gramAction phi err = Z)
    (R : ℝ) (hR : 0 ≤ R)
    (hscore : ∀ j, |Z j| ≤ R) :
    sqNorm err ≤ ((d : ℝ) * R ^ 2) / (((N : ℝ) * kappa) ^ 2) := by
  have hcore := gram_coercive_normalEq_sqNorm_bound_of_abs_score_le
    hN kappa hkappa phi err Z hcoercive hnormal R hR hscore
  have hden : 0 < (((N : ℝ) * kappa) ^ 2) := by
    have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  rw [le_div_iff₀ hden]
  simpa [mul_comm] using hcore

end UEOT.V3.PredictableOLS
