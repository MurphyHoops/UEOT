import UEOT.V3.HilbertMeanConcentration
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# P-STAT-06 — Hilbert second-moment core

This module formalizes the key off-diagonal cancellation used in the frozen
RKHS empirical-mean concentration proof: independent centered Hilbert-valued
random variables have zero expected cross inner product.
-/

namespace UEOT.V3.HilbertMeanSecondMoment

open MeasureTheory ProbabilityTheory

universe uΩ uH

variable {Ω : Type uΩ} {H : Type uH}
variable [MeasurableSpace Ω] [MeasurableSpace H]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [BorelSpace H]

/-- Two independent integrable centered Hilbert-valued random variables have
zero expected cross inner product. -/
theorem integral_inner_eq_zero_of_indep_centered
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → H)
    (hXY : X ⟂ᵢ[μ] Y)
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hX0 : (∫ ω, X ω ∂μ) = 0)
    (hY0 : (∫ ω, Y ω ∂μ) = 0) :
    (∫ ω, inner ℝ (X ω) (Y ω) ∂μ) = 0 := by
  have hfactor := hXY.integral_bilin hX hY (innerSL ℝ)
  simpa [hX0, hY0] using hfactor

/-- In an independent finite family of centered Hilbert-valued random
variables, every off-diagonal cross inner product has expectation zero. -/
theorem integral_inner_eq_zero_of_iIndep_centered
    {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin N → Ω → H)
    (hindep : iIndepFun Z μ)
    (hint : ∀ i, Integrable (Z i) μ)
    (hmean : ∀ i, (∫ ω, Z i ω ∂μ) = 0)
    (i j : Fin N) (hij : i ≠ j) :
    (∫ ω, inner ℝ (Z i ω) (Z j ω) ∂μ) = 0 := by
  exact integral_inner_eq_zero_of_indep_centered μ (Z i) (Z j)
    (hindep.indepFun hij) (hint i) (hint j) (hmean i) (hmean j)

end UEOT.V3.HilbertMeanSecondMoment
