import UEOT.V3.PredictableOLSRadius
import Mathlib.Tactic

/-!
# P-INV-05 — high-probability OLS confidence closure

This module composes the already verified deterministic OLS estimate, the
finite-dimensional two-sided sub-Gaussian union bound, and the exact frozen
score threshold. The only source-specific probability input still abstracted
here is the coordinate sub-Gaussian property of the predictable score vector.
-/

namespace UEOT.V3.PredictableOLSConfidence

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.PredictableOLS
open UEOT.V3.PredictableOLSRadius
open scoped NNReal

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω]

/-- Squared version of the frozen P-INV-05 Euclidean error radius. -/
noncomputable def errorSqRadius
    (N d : ℕ) (sigma B kappa alpha : ℝ) : ℝ :=
  ((sigma * B) / kappa) ^ 2 *
    (2 * (d : ℝ) * log ((2 * (d : ℝ)) / alpha) / (N : ℝ))

/-- Frozen P-INV-05 Euclidean error radius. -/
noncomputable def errorRadius
    (N d : ℕ) (sigma B kappa alpha : ℝ) : ℝ :=
  ((sigma * B) / kappa) *
    sqrt (2 * (d : ℝ) * log ((2 * (d : ℝ)) / alpha) / (N : ℝ))

/-- The frozen Euclidean radius is nonnegative under the source assumptions. -/
theorem errorRadius_nonneg
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {sigma B kappa alpha : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B) (hkappa : 0 < kappa)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    0 ≤ errorRadius N d sigma B kappa alpha := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdoneNat : 1 ≤ d := Nat.succ_le_iff.mpr hd
  have hdone : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdoneNat
  have hratio_one : 1 ≤ (2 * (d : ℝ)) / alpha := by
    rw [le_div_iff₀ halpha0]
    have htwo_d : (1 : ℝ) ≤ 2 * (d : ℝ) := by nlinarith
    simpa using halpha1.trans htwo_d
  have hlog : 0 ≤ log ((2 * (d : ℝ)) / alpha) := Real.log_nonneg hratio_one
  unfold errorRadius
  positivity

/-- Squaring the frozen Euclidean radius gives the squared-error radius. -/
theorem errorRadius_sq_eq_errorSqRadius
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {sigma B kappa alpha : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B) (hkappa : 0 < kappa)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    (errorRadius N d sigma B kappa alpha) ^ 2 =
      errorSqRadius N d sigma B kappa alpha := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdoneNat : 1 ≤ d := Nat.succ_le_iff.mpr hd
  have hdone : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdoneNat
  have hratio_one : 1 ≤ (2 * (d : ℝ)) / alpha := by
    rw [le_div_iff₀ halpha0]
    have htwo_d : (1 : ℝ) ≤ 2 * (d : ℝ) := by nlinarith
    simpa using halpha1.trans htwo_d
  have hlog : 0 ≤ log ((2 * (d : ℝ)) / alpha) := Real.log_nonneg hratio_one
  have hinside :
      0 ≤ 2 * (d : ℝ) * log ((2 * (d : ℝ)) / alpha) / (N : ℝ) := by
    positivity
  unfold errorRadius errorSqRadius
  rw [mul_pow, Real.sq_sqrt hinside]

/-- Substituting the exact score radius into the deterministic OLS estimate
produces exactly the frozen squared-error constant. -/
theorem scoreRadius_sq_error_identity
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {sigma B kappa alpha : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B) (hkappa : 0 < kappa)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    (d : ℝ) * (scoreRadius N d sigma B alpha) ^ 2 /
        (((N : ℝ) * kappa) ^ 2) =
      errorSqRadius N d sigma B kappa alpha := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdoneNat : 1 ≤ d := Nat.succ_le_iff.mpr hd
  have hdone : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdoneNat
  have hratio_one : 1 ≤ (2 * (d : ℝ)) / alpha := by
    rw [le_div_iff₀ halpha0]
    have htwo_d : (1 : ℝ) ≤ 2 * (d : ℝ) := by nlinarith
    simpa using halpha1.trans htwo_d
  have hlog : 0 ≤ log ((2 * (d : ℝ)) / alpha) := Real.log_nonneg hratio_one
  have hrad : 0 ≤ 2 * (N : ℝ) * log ((2 * (d : ℝ)) / alpha) := by
    positivity
  unfold scoreRadius errorSqRadius
  rw [mul_pow, Real.sq_sqrt hrad]
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNreal
  have hk0 : kappa ≠ 0 := ne_of_gt hkappa
  field_simp [hN0, hk0] <;> ring

/-- Once each score coordinate has the correct sub-Gaussian proxy, the complete
P-INV-05 squared-error event has failure probability at most `alpha`.

The design and error may depend on the sample point. The Gram lower bound and
normal equation are required samplewise, exactly as in the frozen theorem.
-/
theorem measure_sqNorm_error_gt_le_alpha
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (phi : Ω → Fin N → Fin d → ℝ)
    (err : Ω → Fin d → ℝ)
    (Z : Fin d → Ω → ℝ)
    {sigma B kappa alpha : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B) (hkappa : 0 < kappa)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hcoercive : ∀ ω,
      (N : ℝ) * kappa * sqNorm (err ω) ≤
        UEOT.V3.DesignIdentifiability.gramQuadratic (phi ω) (err ω))
    (hnormal : ∀ ω,
      gramAction (phi ω) (err ω) = fun j => Z j ω)
    (hZ : ∀ j,
      HasSubgaussianMGF (Z j) (scoreParam N sigma B) μ) :
    μ.real {ω |
      errorSqRadius N d sigma B kappa alpha < sqNorm (err ω)} ≤ alpha := by
  have hR : 0 ≤ scoreRadius N d sigma B alpha := by
    unfold scoreRadius
    positivity
  have htail := measure_exists_score_coord_gt_le_alpha
    hN hd μ Z hsigma hB halpha0 halpha1 hZ
  have hsubset :
      {ω | errorSqRadius N d sigma B kappa alpha < sqNorm (err ω)} ⊆
        {ω | ∃ j : Fin d,
          scoreRadius N d sigma B alpha < |Z j ω|} := by
    intro ω hω
    by_contra hnot
    have hscore : ∀ j : Fin d,
        |Z j ω| ≤ scoreRadius N d sigma B alpha := by
      intro j
      apply le_of_not_gt
      intro hj
      exact hnot ⟨j, hj⟩
    have hdet := sqNorm_error_le_of_abs_score_le
      hN kappa hkappa (phi ω) (err ω) (fun j => Z j ω)
      (hcoercive ω) (hnormal ω)
      (scoreRadius N d sigma B alpha) hR hscore
    rw [scoreRadius_sq_error_identity hN hd hsigma hB hkappa halpha0 halpha1] at hdet
    exact (not_lt_of_ge hdet) hω
  exact (measureReal_mono hsubset).trans htail

/-- Source-form Euclidean confidence bound, conditional only on the remaining
coordinate sub-Gaussian score bridge. The norm is written explicitly as
`sqrt (sqNorm err)` to keep the finite-coordinate representation transparent. -/
theorem measure_euclidean_error_gt_le_alpha
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (phi : Ω → Fin N → Fin d → ℝ)
    (err : Ω → Fin d → ℝ)
    (Z : Fin d → Ω → ℝ)
    {sigma B kappa alpha : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B) (hkappa : 0 < kappa)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hcoercive : ∀ ω,
      (N : ℝ) * kappa * sqNorm (err ω) ≤
        UEOT.V3.DesignIdentifiability.gramQuadratic (phi ω) (err ω))
    (hnormal : ∀ ω,
      gramAction (phi ω) (err ω) = fun j => Z j ω)
    (hZ : ∀ j,
      HasSubgaussianMGF (Z j) (scoreParam N sigma B) μ) :
    μ.real {ω |
      errorRadius N d sigma B kappa alpha < sqrt (sqNorm (err ω))} ≤ alpha := by
  have hsq := measure_sqNorm_error_gt_le_alpha
    hN hd μ phi err Z hsigma hB hkappa halpha0 halpha1 hcoercive hnormal hZ
  have hrad_nonneg :=
    errorRadius_nonneg hN hd hsigma hB hkappa halpha0 halpha1
  have hsubset :
      {ω | errorRadius N d sigma B kappa alpha < sqrt (sqNorm (err ω))} ⊆
        {ω | errorSqRadius N d sigma B kappa alpha < sqNorm (err ω)} := by
    intro ω hω
    have hsqrt_nonneg : 0 ≤ sqrt (sqNorm (err ω)) := Real.sqrt_nonneg _
    have hsquared :
        (errorRadius N d sigma B kappa alpha) ^ 2 <
          (sqrt (sqNorm (err ω))) ^ 2 :=
      (sq_lt_sq₀ hrad_nonneg hsqrt_nonneg).2 hω
    rw [errorRadius_sq_eq_errorSqRadius hN hd hsigma hB hkappa halpha0 halpha1,
      Real.sq_sqrt (sqNorm_nonneg (err ω))] at hsquared
    exact hsquared
  exact (measureReal_mono hsubset).trans hsq

end UEOT.V3.PredictableOLSConfidence
