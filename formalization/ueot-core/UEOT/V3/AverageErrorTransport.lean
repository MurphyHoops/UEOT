import UEOT.V3.TVSpan
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Tactic.Linarith

/-!
# P-STAT-09 — average-error transport

The frozen source has two independent transport statements for a measurable
error observable `0 ≤ e ≤ 1`:

1. a density-ratio bound `dν/dμ ≤ C` gives `E_ν e ≤ C E_μ e`;
2. a total-variation bound gives `E_ν e ≤ E_μ e + δ`.

Both statements below preserve those exact hypotheses.  The density-ratio
branch is proved through Mathlib's Radon--Nikodym integral identity rather than
by replacing the source assumption with a stronger measure-domination axiom.
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

/-- P-STAT-09, density-ratio half.  If the deployment law is absolutely
continuous with respect to the reference law and its Radon--Nikodym derivative
is at most `C`, every nonnegative bounded error has deployment expectation at
most `C` times its reference expectation. -/
theorem expectation_le_of_rnDeriv_le
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : X → ℝ) (he : Measurable e)
    (he0 : ∀ x, 0 ≤ e x) (he1 : ∀ x, e x ≤ 1)
    (C : ℝ)
    (hAC : ν ≪ μ)
    (hC : ∀ᵐ x ∂μ, (ν.rnDeriv μ x).toReal ≤ C) :
    (∫ x, e x ∂ν) ≤ C * (∫ x, e x ∂μ) := by
  have heμ : Integrable e μ :=
    integrable_of_interval μ e he 0 1 (by norm_num) he0 he1
  have heν : Integrable e ν :=
    integrable_of_interval ν e he 0 1 (by norm_num) he0 he1
  have hleft : Integrable (fun x => (ν.rnDeriv μ x).toReal * e x) μ :=
    (Measure.integrable_rnDeriv_mul_iff hAC).2 heν
  have hright : Integrable (fun x => C * e x) μ := heμ.const_mul C
  have hmono :
      (∫ x, (ν.rnDeriv μ x).toReal * e x ∂μ) ≤
        ∫ x, C * e x ∂μ := by
    apply integral_mono_ae hleft hright
    filter_upwards [hC] with x hx
    exact mul_le_mul_of_nonneg_right hx (he0 x)
  rw [Measure.integral_toReal_rnDeriv_mul hAC] at hmono
  simpa only [integral_const_mul] using hmono

/-- Literal source wrapper exposing both branches of P-STAT-09 together. -/
theorem p_stat_09
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : X → ℝ) (he : Measurable e)
    (he0 : ∀ x, 0 ≤ e x) (he1 : ∀ x, e x ≤ 1)
    (C δ : ℝ)
    (hAC : ν ≪ μ)
    (hC : ∀ᵐ x ∂μ, (ν.rnDeriv μ x).toReal ≤ C)
    (hδ : tvDist ν μ ≤ δ) :
    (∫ x, e x ∂ν) ≤ C * (∫ x, e x ∂μ) ∧
      (∫ x, e x ∂ν) ≤ (∫ x, e x ∂μ) + δ := by
  exact ⟨expectation_le_of_rnDeriv_le μ ν e he he0 he1 C hAC hC,
    expectation_le_of_tvDist_le μ ν e he he0 he1 hδ⟩

/-- Literal source wrapper for the TV branch alone. -/
theorem p_stat_09_tv
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : X → ℝ) (he : Measurable e)
    (he0 : ∀ x, 0 ≤ e x) (he1 : ∀ x, e x ≤ 1)
    {δ : ℝ} (hδ : tvDist ν μ ≤ δ) :
    (∫ x, e x ∂ν) ≤ (∫ x, e x ∂μ) + δ :=
  expectation_le_of_tvDist_le μ ν e he he0 he1 hδ

end UEOT.V3.AverageErrorTransport
