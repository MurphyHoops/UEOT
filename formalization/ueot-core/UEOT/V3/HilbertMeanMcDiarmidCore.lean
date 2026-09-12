import UEOT.V3.HilbertMeanConditionalHoeffding

/-!
# P-STAT-06 — McDiarmid probability core

This module composes the two machine-checked probabilistic layers used by the
frozen P-STAT-06 proof.  Once a Doob increment process has conditional support
width at most `2/N` and conditional mean zero, `HilbertMeanConditionalHoeffding`
turns each noninitial increment into proxy `1/N²`; `HilbertMeanAzuma` then gives
exactly `exp (-N ε²/2)`.

The remaining source-facing task is therefore purely structural: construct the
Doob increments of the bounded-difference statistic from independent samples
and discharge the fiber-range hypotheses below.
-/

namespace UEOT.V3.HilbertMeanMcDiarmidCore

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Exact McDiarmid/Azuma tail once the Doob increment fiber ranges have been
exhibited.  The initial increment is left as an ordinary sub-Gaussian input;
the source bridge will obtain it from the same width-`2/N` Hoeffding argument
with the trivial initial sigma-algebra. -/
theorem tail_from_doob_fiber_ranges
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ}
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    (N : ℕ) (hN : 0 < N)
    (a b : ℕ → Ω → ℝ)
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : HasSubgaussianMGF (Y 0) (HilbertMeanAzuma.invSqParam N) μ)
    (hXm : ∀ i < N - 1, AEMeasurable (Y (i + 1)) μ)
    (hglobal : ∀ i < N - 1, ∀ᵐ ω ∂μ,
      Y (i + 1) ω ∈ Set.Icc (-(2 / (N : ℝ))) (2 / (N : ℝ)))
    (hfiber : ∀ i < N - 1, ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
      ∀ᵐ ω ∂(condExpKernel μ (ℱ i) ω'),
        Y (i + 1) ω ∈ Set.Icc (a i ω') (b i ω'))
    (hcenter : ∀ i < N - 1, ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
      (∫ ω, Y (i + 1) ω ∂condExpKernel μ (ℱ i) ω') = 0)
    (hwidth : ∀ i < N - 1, ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
      ‖b i ω' - a i ω'‖₊ ≤ (2 : ℝ≥0) / (N : ℝ≥0))
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range N, Y i ω}
      ≤ Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
  apply HilbertMeanAzuma.azuma_invSqParam_tail
    (μ := μ) N hN h_adapted h0
  · intro i hi
    exact HilbertMeanConditionalHoeffding.hasCondSubgaussianMGF_invSqParam_of_fiber_range
      (μ := μ) (ℱ.le i) hN (Y (i + 1)) (a i) (b i)
      (hXm i hi) (hglobal i hi) (hfiber i hi) (hcenter i hi) (hwidth i hi)
  · exact hε

end UEOT.V3.HilbertMeanMcDiarmidCore
