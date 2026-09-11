import UEOT.V3.TVSpan
import Mathlib.Tactic.Linarith

/-!
# P-STAT-09 — average-error transport

The frozen source has two independent transport statements for a measurable
error observable `0 ≤ e ≤ 1`:

1. a density-ratio bound `dν/dμ ≤ C` gives `E_ν e ≤ C E_μ e`;
2. a total-variation bound gives `E_ν e ≤ E_μ e + δ`.

This module first closes the second statement directly from the already proved
P-MET-02 span inequality.  The Radon--Nikodym density statement is added in the
same lane as a separate theorem so its measure-theoretic assumptions remain
visible.
-/

namespace UEOT.V3.AverageErrorTransport

open MeasureTheory
open UEOT.V3.TotalVariation
open UEOT.V3.TVSpan

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- P-STAT-09, total-variation half.  A `[0,1]` error observable has span at
most one, so deployment expectation can increase by at most the TV shift. -/
theorem expectation_le_of_tvDist_le
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : X → ℝ) (he : Measurable e)
    (he0 : ∀ x, 0 ≤ e x) (he1 : ∀ x, e x ≤ 1)
    {δ : ℝ} (hδ : tvDist ν μ ≤ δ) :
    (∫ x, e x ∂ν) ≤ (∫ x, e x ∂μ) + δ := by
  have hspan := abs_integral_sub_le_span_tvDist
    ν μ e he 0 1 (by norm_num) he0 he1
  have hdiff : (∫ x, e x ∂ν) - (∫ x, e x ∂μ) ≤ tvDist ν μ := by
    have habs :
        |(∫ x, e x ∂ν) - (∫ x, e x ∂μ)| ≤ tvDist ν μ := by
      simpa using hspan
    exact le_trans (le_abs_self _) habs
  linarith

/-- Literal source wrapper for the TV branch of P-STAT-09. -/
theorem p_stat_09_tv
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : X → ℝ) (he : Measurable e)
    (he0 : ∀ x, 0 ≤ e x) (he1 : ∀ x, e x ≤ 1)
    {δ : ℝ} (hδ : tvDist ν μ ≤ δ) :
    (∫ x, e x ∂ν) ≤ (∫ x, e x ∂μ) + δ :=
  expectation_le_of_tvDist_le μ ν e he he0 he1 hδ

end UEOT.V3.AverageErrorTransport
