import UEOT.V3.HilbertMeanConcentration
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# P-STAT-06 — Hilbert second-moment core

This module formalizes the key second-moment identities used in the frozen
RKHS empirical-mean concentration proof: independent centered Hilbert-valued
random variables have zero expected cross inner product, and the squared norm
of an empirical mean expands into the corresponding double inner-product sum.
-/

namespace UEOT.V3.HilbertMeanSecondMoment

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open scoped BigOperators

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
  simpa only [innerSL_apply_apply ℝ, hX0, hY0, map_zero] using hfactor

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

/-- Algebraic expansion of the squared Hilbert norm of an empirical mean.
This is the deterministic identity underlying the P-STAT-06 second-moment
calculation. -/
theorem norm_empiricalMean_sq_eq_double_sum
    {N : ℕ} (hN : 0 < N) (z : Fin N → H) :
    ‖empiricalMean z‖ ^ 2 =
      ((N : ℝ)⁻¹) ^ 2 * ∑ i : Fin N, ∑ j : Fin N, inner ℝ (z i) (z j) := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [← real_inner_self_eq_norm_sq]
  unfold empiricalMean
  rw [real_inner_smul_left, real_inner_smul_right]
  simp_rw [sum_inner, inner_sum]
  ring

end UEOT.V3.HilbertMeanSecondMoment
