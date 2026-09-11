import UEOT.V3.PredictableOLSSourceScore
import UEOT.V3.PredictableOLSSourceIndex
import UEOT.V3.PredictableOLSNormalEquation
import UEOT.V3.PredictableOLSGoodGramConfidence
import Mathlib.Tactic

/-!
# P-INV-05 — source-facing predictable-design OLS confidence theorem

This module composes the complete P-INV-05 proof chain:

* source-time predictable design and conditionally sub-Gaussian noise;
* predictable-multiplier conditional MGF control;
* martingale score accumulation;
* source-time / `Fin N` sample-index identification;
* the OLS normal equation from the source linear model;
* the exact finite-dimensional confidence radius on the samplewise good-Gram
  event.

The source statement is minimally corrected by making explicit that the noise
at source time `n+1` is measurable with respect to `F (n+1)`.  This adaptedness
is needed to iterate the conditional MGF and is implicit in the usual filtered
stochastic-process formulation.
-/

namespace UEOT.V3.PredictableOLSSourceConfidence

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.DesignIdentifiability
open UEOT.V3.PredictableOLS
open UEOT.V3.PredictableOLSRadius
open UEOT.V3.PredictableOLSConfidence
open UEOT.V3.PredictableOLSGoodGramConfidence
open UEOT.V3.PredictableOLSNormalEquation
open UEOT.V3.PredictableOLSSourceIndex
open UEOT.V3.PredictableOLSSourceMGF
open UEOT.V3.PredictableOLSSourceScore
open scoped BigOperators NNReal

universe uΩ

variable {Ω : Type uΩ} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Literal matrix-form good-Gram predicate corresponding to
`G_N ⪰ N κ I`: every parameter direction has Gram quadratic form at least
`N κ` times its squared Euclidean norm. -/
def GoodGram {N d : ℕ}
    (phi : Fin N → Fin d → ℝ) (kappa : ℝ) : Prop :=
  ∀ v : Fin d → ℝ,
    (N : ℝ) * kappa * sqNorm v ≤ gramQuadratic phi v

/-- Corrected source-form P-INV-05.

Under predictable bounded design, adapted conditionally `sigma^2`-sub-Gaussian
noise, and the unconstrained OLS normal equation for the source linear model,
the probability that both the full matrix good-Gram condition holds and the
Euclidean estimation error exceeds the frozen P-INV-05 radius is at most
`alpha`.
-/
theorem measure_source_goodGram_and_euclidean_error_gt_le_alpha
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → Fin d → ℝ)
    (xi : ℕ → Ω → ℝ)
    (thetaStar : Fin d → ℝ)
    (thetaHat : Ω → Fin d → ℝ)
    {sigma B kappa alpha : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B) (hkappa : 0 < kappa)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hphi : ∀ n j, @Measurable Ω ℝ (F n) inferInstance
      (fun ω => phi (n + 1) ω j))
    (hxi_meas : ∀ n, @Measurable Ω ℝ (F (n + 1)) inferInstance
      (xi (n + 1)))
    (hbound : ∀ n ω j, |phi (n + 1) ω j| ≤ B)
    (hnoise : ∀ n,
      HasCondSubgaussianMGF (F n) (F.le n)
        (xi (n + 1)) (noiseParam sigma) μ)
    (hOLS : ∀ ω,
      IsOLSNormalEq
        (finDesign (N := N) phi ω)
        (linearResponse
          (finDesign (N := N) phi ω) thetaStar
          (finNoise (N := N) xi ω))
        (thetaHat ω)) :
    μ.real {ω |
      GoodGram (finDesign (N := N) phi ω) kappa ∧
      errorRadius N d sigma B kappa alpha <
        sqrt (sqNorm (thetaHat ω - thetaStar))} ≤ alpha := by
  let phiFin : Ω → Fin N → Fin d → ℝ :=
    fun ω => finDesign (N := N) phi ω
  let err : Ω → Fin d → ℝ :=
    fun ω => thetaHat ω - thetaStar
  let Z : Fin d → Ω → ℝ :=
    fun j ω => ∑ t ∈ Finset.range N,
      phi (t + 1) ω j * xi (t + 1) ω

  have hZraw := allCoord_sourceScore_hasSubgaussianMGF
    (N := N) μ F phi xi sigma B hB.le hphi hxi_meas hbound hnoise
  have hZ : ∀ j : Fin d,
      HasSubgaussianMGF (Z j) (scoreParam N sigma B) μ := by
    intro j
    simpa [Z] using hZraw j

  have hnormal : ∀ ω,
      gramAction (phiFin ω) (err ω) = fun j => Z j ω := by
    intro ω
    have hfin := gramAction_error_eq_scoreVector
      (phiFin ω) thetaStar (thetaHat ω) (finNoise (N := N) xi ω)
      (by simpa [phiFin] using hOLS ω)
    calc
      gramAction (phiFin ω) (err ω) =
          scoreVector (phiFin ω) (finNoise (N := N) xi ω) := by
        simpa [err] using hfin
      _ = fun j => Z j ω := by
        funext j
        change scoreVector (finDesign (N := N) phi ω)
            (finNoise (N := N) xi ω) j = Z j ω
        rw [scoreVector_finSource_eq_range]

  have htail := measure_goodGram_and_euclidean_error_gt_le_alpha
    hN hd μ phiFin err Z hsigma hB hkappa halpha0 halpha1 hnormal hZ

  have hsubset :
      {ω |
        GoodGram (finDesign (N := N) phi ω) kappa ∧
        errorRadius N d sigma B kappa alpha <
          sqrt (sqNorm (thetaHat ω - thetaStar))} ⊆
      {ω |
        ((N : ℝ) * kappa * sqNorm (err ω) ≤
          gramQuadratic (phiFin ω) (err ω)) ∧
        errorRadius N d sigma B kappa alpha < sqrt (sqNorm (err ω))} := by
    intro ω hω
    rcases hω with ⟨hgood, herr⟩
    refine ⟨?_, ?_⟩
    · exact hgood (err ω)
    · simpa [err] using herr

  exact (measureReal_mono hsubset).trans htail

end UEOT.V3.PredictableOLSSourceConfidence
