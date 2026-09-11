import UEOT.V3.PredictableOLSConditionalLift
import UEOT.V3.PredictableOLSSourceAdapted
import UEOT.V3.PredictableOLSSourceMGF
import UEOT.V3.PredictableOLSScore
import Mathlib.Tactic

/-!
# P-INV-05 — source assumptions imply score sub-Gaussianity

This module composes the source-facing one-step multiplier theorem with the
martingale accumulation theorem.  Source time starts at `t = 1`, while
Mathlib's sequence starts at zero, so we use the shifted filtration from
`PredictableOLSSourceAdapted`.

The only strengthening relative to the literal v3.0 statement is explicit
adaptedness of the noise: `xi (n+1)` is measurable with respect to `F (n+1)`.
This condition is mathematically necessary for conditional-MGF iteration and
is not introduced merely for formalization.
-/

namespace UEOT.V3.PredictableOLSSourceScore

open MeasureTheory ProbabilityTheory
open UEOT.V3.PredictableOLSScore
open UEOT.V3.PredictableOLSSourceAdapted
open UEOT.V3.PredictableOLSSourceMGF
open UEOT.V3.PredictableOLSConditionalLift
open scoped BigOperators NNReal

universe uΩ

variable {Ω : Type uΩ} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Under the corrected source assumptions, every coordinate of the
predictable OLS score has the exact proxy `N * (sigma B)^2`. -/
theorem allCoord_sourceScore_hasSubgaussianMGF
    {d N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ)
    (phi : ℕ → Ω → Fin d → ℝ)
    (xi : ℕ → Ω → ℝ)
    (sigma B : ℝ)
    (hB0 : 0 ≤ B)
    (hphi : ∀ n j, @Measurable Ω ℝ (F n) inferInstance
      (fun ω => phi (n + 1) ω j))
    (hxi_meas : ∀ n, @Measurable Ω ℝ (F (n + 1)) inferInstance
      (xi (n + 1)))
    (hbound : ∀ n ω j, |phi (n + 1) ω j| ≤ B)
    (hnoise : ∀ n,
      HasCondSubgaussianMGF (F n) (F.le n)
        (xi (n + 1)) (noiseParam sigma) μ) :
    ∀ j : Fin d,
      HasSubgaussianMGF
        (fun ω => ∑ t ∈ Finset.range N,
          phi (t + 1) ω j * xi (t + 1) ω)
        (scoreParam N sigma B) μ := by
  let phiS : ℕ → Ω → Fin d → ℝ := fun n ω j => phi (n + 1) ω j
  let xiS : ℕ → Ω → ℝ := fun n ω => xi (n + 1) ω
  have hadapt : ∀ j : Fin d,
      StronglyAdapted (succFiltration F) (scoreProcess phiS xiS j) := by
    intro j
    have h := shiftedScore_stronglyAdapted F phi xi j hphi hxi_meas
    simpa [phiS, xiS, scoreProcess, shiftedScoreProcess] using h
  have h0 : ∀ j : Fin d,
      HasSubgaussianMGF
        (scoreProcess phiS xiS j 0) (incrementParam sigma B) μ := by
    intro j
    have hcond := hasCondSubgaussianMGF_predictable_mul
      (μ := μ) (F.le 0)
      (fun ω => phi 1 ω j) (xi 1) sigma B hB0
      (hphi 0 j) (hbound 0) (hnoise 0)
    have huncond := hcond.toHasSubgaussianMGF (F.le 0)
    simpa [phiS, xiS, scoreProcess] using huncond
  have hsub : ∀ j : Fin d, ∀ i < N - 1,
      HasCondSubgaussianMGF (succFiltration F i) ((succFiltration F).le i)
        (scoreProcess phiS xiS j (i + 1)) (incrementParam sigma B) μ := by
    intro j i hi
    have hcond := hasCondSubgaussianMGF_predictable_mul
      (μ := μ) (F.le (i + 1))
      (fun ω => phi ((i + 1) + 1) ω j) (xi ((i + 1) + 1)) sigma B hB0
      (hphi (i + 1) j) (hbound (i + 1)) (hnoise (i + 1))
    simpa [succFiltration, phiS, xiS, scoreProcess] using hcond
  have hall := allCoordScore_hasSubgaussianMGF
    μ (succFiltration F) phiS xiS sigma B hadapt h0 hsub
  intro j
  simpa [phiS, xiS] using hall j

end UEOT.V3.PredictableOLSSourceScore
