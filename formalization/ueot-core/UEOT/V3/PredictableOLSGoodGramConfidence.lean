import UEOT.V3.PredictableOLSConfidence
import Mathlib.Tactic

/-!
# P-INV-05 — confidence bound on the good-Gram event

The source statement does not assume the Gram lower bound holds for every
sample.  It says that on samples satisfying `G_N ⪰ N κ I`, the OLS radius can
fail only on an event of probability at most `alpha`.

This module expresses that statement literally: the intersection of the
samplewise Gram-coercivity event with the error-beyond-radius event has
probability at most `alpha`.
-/

namespace UEOT.V3.PredictableOLSGoodGramConfidence

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.PredictableOLS
open UEOT.V3.PredictableOLSRadius
open UEOT.V3.PredictableOLSConfidence
open scoped NNReal

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω]

/-- Squared-error P-INV-05 bound with Gram coercivity imposed only on the
samples inside the event, rather than globally. -/
theorem measure_goodGram_and_sqNorm_error_gt_le_alpha
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (phi : Ω → Fin N → Fin d → ℝ)
    (err : Ω → Fin d → ℝ)
    (Z : Fin d → Ω → ℝ)
    {sigma B kappa alpha : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B) (hkappa : 0 < kappa)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hnormal : ∀ ω,
      gramAction (phi ω) (err ω) = fun j => Z j ω)
    (hZ : ∀ j,
      HasSubgaussianMGF (Z j) (scoreParam N sigma B) μ) :
    μ.real {ω |
      ((N : ℝ) * kappa * sqNorm (err ω) ≤
        UEOT.V3.DesignIdentifiability.gramQuadratic (phi ω) (err ω)) ∧
      errorSqRadius N d sigma B kappa alpha < sqNorm (err ω)} ≤ alpha := by
  have hR : 0 ≤ scoreRadius N d sigma B alpha := by
    unfold scoreRadius
    positivity
  have htail := measure_exists_score_coord_gt_le_alpha
    hN hd μ Z hsigma hB halpha0 halpha1 hZ
  have hsubset :
      {ω |
        ((N : ℝ) * kappa * sqNorm (err ω) ≤
          UEOT.V3.DesignIdentifiability.gramQuadratic (phi ω) (err ω)) ∧
        errorSqRadius N d sigma B kappa alpha < sqNorm (err ω)} ⊆
        {ω | ∃ j : Fin d,
          scoreRadius N d sigma B alpha < |Z j ω|} := by
    intro ω hω
    rcases hω with ⟨hcoercive, herr⟩
    by_contra hnot
    have hscore : ∀ j : Fin d,
        |Z j ω| ≤ scoreRadius N d sigma B alpha := by
      intro j
      apply le_of_not_gt
      intro hj
      exact hnot ⟨j, hj⟩
    have hdet := sqNorm_error_le_of_abs_score_le
      hN kappa hkappa (phi ω) (err ω) (fun j => Z j ω)
      hcoercive (hnormal ω)
      (scoreRadius N d sigma B alpha) hR hscore
    rw [scoreRadius_sq_error_identity hN hd hsigma hB hkappa halpha0 halpha1] at hdet
    exact (not_lt_of_ge hdet) herr
  exact (measureReal_mono hsubset).trans htail

/-- Euclidean source radius on the samplewise good-Gram event. -/
theorem measure_goodGram_and_euclidean_error_gt_le_alpha
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (phi : Ω → Fin N → Fin d → ℝ)
    (err : Ω → Fin d → ℝ)
    (Z : Fin d → Ω → ℝ)
    {sigma B kappa alpha : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B) (hkappa : 0 < kappa)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hnormal : ∀ ω,
      gramAction (phi ω) (err ω) = fun j => Z j ω)
    (hZ : ∀ j,
      HasSubgaussianMGF (Z j) (scoreParam N sigma B) μ) :
    μ.real {ω |
      ((N : ℝ) * kappa * sqNorm (err ω) ≤
        UEOT.V3.DesignIdentifiability.gramQuadratic (phi ω) (err ω)) ∧
      errorRadius N d sigma B kappa alpha < sqrt (sqNorm (err ω))} ≤ alpha := by
  have hsq := measure_goodGram_and_sqNorm_error_gt_le_alpha
    hN hd μ phi err Z hsigma hB hkappa halpha0 halpha1 hnormal hZ
  have hrad_nonneg :=
    errorRadius_nonneg hN hd hsigma hB hkappa halpha0 halpha1
  have hsubset :
      {ω |
        ((N : ℝ) * kappa * sqNorm (err ω) ≤
          UEOT.V3.DesignIdentifiability.gramQuadratic (phi ω) (err ω)) ∧
        errorRadius N d sigma B kappa alpha < sqrt (sqNorm (err ω))} ⊆
        {ω |
          ((N : ℝ) * kappa * sqNorm (err ω) ≤
            UEOT.V3.DesignIdentifiability.gramQuadratic (phi ω) (err ω)) ∧
          errorSqRadius N d sigma B kappa alpha < sqNorm (err ω)} := by
    intro ω hω
    rcases hω with ⟨hcoercive, herr⟩
    refine ⟨hcoercive, ?_⟩
    have hsqrt_nonneg : 0 ≤ sqrt (sqNorm (err ω)) := Real.sqrt_nonneg _
    have hsquared :
        (errorRadius N d sigma B kappa alpha) ^ 2 <
          (sqrt (sqNorm (err ω))) ^ 2 :=
      (sq_lt_sq₀ hrad_nonneg hsqrt_nonneg).2 herr
    rw [errorRadius_sq_eq_errorSqRadius hN hd hsigma hB hkappa halpha0 halpha1,
      Real.sq_sqrt (sqNorm_nonneg (err ω))] at hsquared
    exact hsquared
  exact (measureReal_mono hsubset).trans hsq

end UEOT.V3.PredictableOLSGoodGramConfidence
