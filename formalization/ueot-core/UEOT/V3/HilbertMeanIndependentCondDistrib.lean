import Mathlib.Probability.HasLaw
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Tactic

/-!
# P-STAT-06 — independent future blocks have constant conditional law

For the canonical product-space Doob construction, the coordinates not yet
revealed are independent of the revealed past.  This file isolates the key
regular-conditional-distribution fact: if a future block `Y` is independent of
a past block `X`, and their laws are `ξ` and `ν`, then the conditional law of
`Y` given `X` is almost everywhere the constant kernel with value `ξ`.

This is the structural bridge needed to identify abstract conditional
expectations with explicit continuation integrals over the unrevealed product
law.
-/

namespace UEOT.V3.HilbertMeanIndependentCondDistrib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe uΩ uβ uγ

variable {Ω : Type uΩ} {β : Type uβ} {γ : Type uγ}
variable [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
variable [StandardBorelSpace γ] [Nonempty γ]

/-- Independence plus the two marginal laws identifies the regular conditional
law of the future block as the constant future law. -/
theorem condDistrib_eq_const_of_indep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (ξ : Measure γ) [IsProbabilityMeasure ξ]
    (X : Ω → β) (Y : Ω → γ)
    (hXm : Measurable X)
    (hXlaw : HasLaw X ν μ)
    (hYlaw : HasLaw Y ξ μ)
    (hXY : IndepFun X Y μ) :
    condDistrib Y X μ =ᵐ[ν] Kernel.const β ξ := by
  rw [← hXlaw.map_eq]
  apply condDistrib_ae_eq_of_measure_eq_compProd X hYlaw.aemeasurable
  calc
    μ.map (fun ω => (X ω, Y ω)) = ν.prod ξ :=
      (hXY.hasLaw_prod hXlaw hYlaw).map_eq
    _ = μ.map X ⊗ₘ Kernel.const β ξ := by
      rw [hXlaw.map_eq]
      simp

end UEOT.V3.HilbertMeanIndependentCondDistrib
