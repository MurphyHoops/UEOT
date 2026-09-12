import UEOT.V3.HilbertMeanSourceActiveIntegrability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P-STAT-06 — strict-past source fiber

The conditional Hoeffding step conditions only on the strict past.  The source
active-fiber estimates therefore should not require a unit-ball hypothesis on
unrevealed coordinates.  This module records the sharper source-facing form:
unit control on `past i`, together with the marginal a.e. unit-ball hypotheses,
is enough for both exact `2/N` active oscillation and active-section
integrability.
-/

namespace UEOT.V3.HilbertMeanSourcePastFiber

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanPrefixFutureAssembly
open UEOT.V3.HilbertMeanSplitStatistic
open UEOT.V3.HilbertMeanDoobStatisticBridge
open UEOT.V3.HilbertMeanSourceContinuationWidth
open UEOT.V3.HilbertMeanSourceCenteredFiber
open UEOT.V3.HilbertMeanSourceActiveIntegrability

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- Replacing the active coordinate by a unit vector yields a unit revealed
prefix as soon as the strict past is unit.  No assumption on the original
active value or strict future is needed. -/
theorem updated_prefix_norm_le_one_of_past
    {N : ℕ} (ω : Fin N → H) (i : Fin N)
    (hpast : ∀ j : past i, ‖ω (j : Fin N)‖ ≤ 1)
    (a : H) (ha : ‖a‖ ≤ 1) :
    ∀ j : prefixBlock (N := N) i.1,
      ‖blockProjection (prefixBlock (N := N) i.1)
          (Function.update ω i a) j‖ ≤ 1 := by
  intro j
  by_cases hji : (j : Fin N) = i
  · simpa [blockProjection, Function.update, hji] using ha
  · have hjle : (j : Fin N).1 ≤ i.1 := by
      exact (mem_prefixBlock_iff (N := N) i.1 (j : Fin N)).mp j.property
    have hjlt : (j : Fin N).1 < i.1 := by omega
    let jp : past i := ⟨(j : Fin N), (mem_past_iff i (j : Fin N)).2 hjlt⟩
    simpa [blockProjection, Function.update, hji, jp] using hpast jp

/-- Exact source continuation oscillation under strict-past unit control only. -/
theorem sourceContinuation_update_pairwise_le_two_div_of_pastUnit
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (i : Fin N)
    (hpast : ∀ j : past i, ‖ω (j : Fin N)‖ ≤ 1)
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (a b : H) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    |sourceContinuation μ i μH (Function.update ω i a) -
      sourceContinuation μ i μH (Function.update ω i b)| ≤
      2 / (N : ℝ) := by
  apply sourceContinuation_update_pairwise_le_two_div hN μ ω i μH a b ha hb
  · exact integrable_splitMeanError_future_of_unit hN μ i μH hμH
      (blockProjection (prefixBlock (N := N) i.1) (Function.update ω i a))
      (updated_prefix_norm_le_one_of_past ω i hpast a ha) hunit
  · exact integrable_splitMeanError_future_of_unit hN μ i μH hμH
      (blockProjection (prefixBlock (N := N) i.1) (Function.update ω i b))
      (updated_prefix_norm_le_one_of_past ω i hpast b hb) hunit

/-- Joint active/future source statistic is integrable with only strict-past
unit control. -/
theorem integrable_activeFutureMeanError_of_pastUnit
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (i : Fin N)
    (hpast : ∀ j : past i, ‖ω (j : Fin N)‖ ≤ 1)
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    Integrable (activeFutureMeanError ω i μH)
      ((μ i).prod (blockLaw μ (future i))) := by
  letI : IsProbabilityMeasure (blockLaw μ (future i)) :=
    blockLaw_isProbability μ (future i)
  have hy : ∀ᵐ y ∂blockLaw μ (future i), ∀ j, ‖y j‖ ≤ 1 :=
    ae_block_unit_of_marginals μ (future i) hunit
  have hmeas := measurable_activeFutureMeanError (H := H) ω i μH
  refine Integrable.of_bound hmeas.aestronglyMeasurable 2 ?_
  have hset : MeasurableSet
      {z : H × (future i → H) | ‖activeFutureMeanError ω i μH z‖ ≤ 2} :=
    measurableSet_le hmeas.norm measurable_const
  apply (Measure.ae_prod_mem_iff_ae_ae_mem hset).2
  filter_upwards [hunit i] with a ha
  filter_upwards [hy] with y hy
  have hx : ∀ j, ‖activePrefix ω i a j‖ ≤ 1 := by
    exact updated_prefix_norm_le_one_of_past ω i hpast a ha
  have hall : ∀ j, ‖assemblePrefixFuture i (activePrefix ω i a) y j‖ ≤ 1 :=
    assemblePrefixFuture_norm_le_one i (activePrefix ω i a) y hx hy
  have hbound := norm_empiricalMean_sub_le_two hN
    (assemblePrefixFuture i (activePrefix ω i a) y) hall μH hμH
  simpa [activeFutureMeanError, splitMeanError, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hbound

/-- Fubini discharge for the active continuation with only strict-past unit
control. -/
theorem integrable_sourceActiveSection_of_pastUnit
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (i : Fin N)
    (hpast : ∀ j : past i, ‖ω (j : Fin N)‖ ≤ 1)
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    Integrable (sourceActiveSection μ i μH ω) (μ i) := by
  letI : IsProbabilityMeasure (blockLaw μ (future i)) :=
    blockLaw_isProbability μ (future i)
  have hjoint := integrable_activeFutureMeanError_of_pastUnit
    hN μ ω i hpast μH hμH hunit
  have houter := hjoint.integral_prod_left
  change Integrable
    (fun x : H => ∫ y,
      splitMeanError i μH
        (blockProjection (prefixBlock (N := N) i.1) (Function.update ω i x), y)
      ∂blockLaw μ (future i)) (μ i)
  exact houter

end UEOT.V3.HilbertMeanSourcePastFiber
