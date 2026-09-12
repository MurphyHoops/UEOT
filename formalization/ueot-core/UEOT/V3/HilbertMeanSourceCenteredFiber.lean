import UEOT.V3.HilbertMeanSourceContinuationWidth
import UEOT.V3.HilbertMeanUnitClip

/-!
# P-STAT-06 — source active-coordinate centered fibers

This module packages the actual active-coordinate continuation section used by
the Doob increment.  The source bounded-difference theorem gives an exact
`2/N` oscillation bound on unit-ball arguments.  Unit-ball clipping upgrades
that source-faithful a.e. support statement to a global oscillation bound
without strengthening the frozen assumptions.
-/

namespace UEOT.V3.HilbertMeanSourceCenteredFiber

open MeasureTheory ProbabilityTheory
open scoped NNReal
open UEOT.V3.HilbertMeanDoobStatisticBridge
open UEOT.V3.HilbertMeanSourceContinuationWidth
open UEOT.V3.HilbertMeanUnitClip

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- The active-coordinate continuation section at sample `ω` and index `i`.
Only coordinate `i` is replaced; the strict future has already been averaged
out inside `sourceContinuation`. -/
noncomputable def sourceActiveSection {N : ℕ}
    (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (ω : Fin N → H) (a : H) : ℝ :=
  sourceContinuation μ i μH (Function.update ω i a)

/-- On source-admissible unit-ball values, the active section has the exact
bounded-difference oscillation `2/N`. -/
theorem sourceActiveSection_pairwise_le_two_div_of_unit
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (hω : ∀ j, ‖ω j‖ ≤ 1)
    (i : Fin N) (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    ∀ a b, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      |sourceActiveSection μ i μH ω a - sourceActiveSection μ i μH ω b| ≤
        2 / (N : ℝ) := by
  intro a b ha hb
  exact sourceContinuation_update_pairwise_le_two_div_of_unit
    hN μ ω hω i μH hμH a b ha hb hunit

/-- After unit-ball clipping, the source active section has a global exact
`2/N` oscillation bound over the whole Hilbert space. -/
theorem unitClip_sourceActiveSection_pairwise_le_two_div
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (hω : ∀ j, ‖ω j‖ ≤ 1)
    (i : Fin N) (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    ∀ a b,
      |unitClip (sourceActiveSection μ i μH ω) a -
        unitClip (sourceActiveSection μ i μH ω) b| ≤ 2 / (N : ℝ) := by
  exact unitClip_pairwise_abs_sub_le
    (sourceActiveSection μ i μH ω)
    (sourceActiveSection_pairwise_le_two_div_of_unit
      hN μ ω hω i μH hμH hunit)

/-- Hoeffding-ready exact-width statement for the centered clipped source
section.  Integrability of the raw active section is kept as a separate input
here and will be discharged by the following product/Fubini layer. -/
theorem centered_sourceActiveSection_exact_width_nnnorm_le
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (hω : ∀ j, ‖ω j‖ ≤ 1)
    (i : Fin N) (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1)
    (hq : Integrable (sourceActiveSection μ i μH ω) (μ i)) :
    ‖(sSup (Set.range (unitClip (sourceActiveSection μ i μH ω))) -
          ∫ a, unitClip (sourceActiveSection μ i μH ω) a ∂μ i) -
       (sInf (Set.range (unitClip (sourceActiveSection μ i μH ω))) -
          ∫ a, unitClip (sourceActiveSection μ i μH ω) a ∂μ i)‖₊
      ≤ (2 : ℝ≥0) / (N : ℝ≥0) := by
  have hosc : ∀ a b, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      |sourceActiveSection μ i μH ω a - sourceActiveSection μ i μH ω b| ≤
        (((2 : ℝ≥0) / (N : ℝ≥0) : ℝ≥0) : ℝ) := by
    intro a b ha hb
    have h := sourceActiveSection_pairwise_le_two_div_of_unit
      hN μ ω hω i μH hμH hunit a b ha hb
    simpa [NNReal.coe_div] using h
  exact centered_unitClip_exact_interval_nnnorm_le
    (μ i) (sourceActiveSection μ i μH ω) hq (hunit i) hosc

end UEOT.V3.HilbertMeanSourceCenteredFiber
