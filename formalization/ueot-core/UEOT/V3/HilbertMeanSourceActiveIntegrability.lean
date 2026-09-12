import UEOT.V3.HilbertMeanSourceCenteredFiber
import Mathlib.MeasureTheory.Integral.Prod

/-!
# P-STAT-06 — integrability of the source active-coordinate continuation

The active-coordinate continuation is an integral over the strict-future block.
We prove its integrability under the active marginal by first proving joint
integrability on `μ i × futureLaw` and then applying Fubini.  This removes the
last auxiliary integrability assumption from the centered-fiber layer.
-/

namespace UEOT.V3.HilbertMeanSourceActiveIntegrability

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanPrefixFutureAssembly
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanSplitStatistic
open UEOT.V3.HilbertMeanSourceCenteredFiber
open UEOT.V3.HilbertMeanSourceContinuationWidth

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- Revealed prefix obtained after replacing the active coordinate by `a`. -/
def activePrefix {N : ℕ} (ω : Fin N → H) (i : Fin N) (a : H) :
    prefixBlock (N := N) i.1 → H :=
  blockProjection (prefixBlock (N := N) i.1) (Function.update ω i a)

/-- The active-prefix map is measurable for the coordinate product sigma algebra. -/
theorem measurable_activePrefix
    {N : ℕ} (ω : Fin N → H) (i : Fin N) :
    Measurable (activePrefix ω i) := by
  rw [measurable_pi_iff]
  intro j
  by_cases hji : (j : Fin N) = i
  · subst hji
    simpa [activePrefix, blockProjection] using (measurable_id : Measurable (fun a : H => a))
  · simpa [activePrefix, blockProjection, Function.update, hji] using
      (measurable_const : Measurable (fun _ : H => ω (j : Fin N)))

/-- Joint active/future form of the source statistic. -/
noncomputable def activeFutureMeanError {N : ℕ}
    (ω : Fin N → H) (i : Fin N) (μH : H)
    (z : H × (future i → H)) : ℝ :=
  splitMeanError i μH (activePrefix ω i z.1, z.2)

/-- The joint active/future statistic is measurable. -/
theorem measurable_activeFutureMeanError
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (ω : Fin N → H) (i : Fin N) (μH : H) :
    Measurable (activeFutureMeanError ω i μH) := by
  unfold activeFutureMeanError
  exact (measurable_splitMeanError (H := H) i μH).comp
    ((measurable_activePrefix ω i).comp measurable_fst |>.prodMk measurable_snd)

/-- Joint active/future source statistic is integrable under the product of the
active marginal and the strict-future block law. -/
theorem integrable_activeFutureMeanError_of_unit
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (hω : ∀ j, ‖ω j‖ ≤ 1)
    (i : Fin N) (μH : H) (hμH : ‖μH‖ ≤ 1)
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
    hmeas.norm.le measurable_const
  apply (ae_prod_iff_ae_ae hset).2
  filter_upwards [hunit i] with a ha
  filter_upwards [hy] with y hy
  have hx : ∀ j, ‖activePrefix ω i a j‖ ≤ 1 := by
    exact updated_prefix_norm_le_one ω hω i a ha
  have hall : ∀ j, ‖assemblePrefixFuture i (activePrefix ω i a) y j‖ ≤ 1 :=
    assemblePrefixFuture_norm_le_one i (activePrefix ω i a) y hx hy
  have hbound := norm_empiricalMean_sub_le_two hN
    (assemblePrefixFuture i (activePrefix ω i a) y) hall μH hμH
  simpa [activeFutureMeanError, splitMeanError, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hbound

/-- The source active-coordinate continuation section is integrable under its
active marginal.  This is the Fubini discharge needed by the centered-fiber
Hoeffding adapter. -/
theorem integrable_sourceActiveSection_of_unit
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (hω : ∀ j, ‖ω j‖ ≤ 1)
    (i : Fin N) (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    Integrable (sourceActiveSection μ i μH ω) (μ i) := by
  letI : IsProbabilityMeasure (blockLaw μ (future i)) :=
    blockLaw_isProbability μ (future i)
  have hjoint := integrable_activeFutureMeanError_of_unit
    hN μ ω hω i μH hμH hunit
  have houter := hjoint.integral_prod_left
  simpa [sourceActiveSection, UEOT.V3.HilbertMeanDoobStatisticBridge.sourceContinuation,
    activeFutureMeanError, activePrefix] using houter

/-- Fully source-facing exact centered width: no auxiliary integrability input. -/
theorem centered_sourceActiveSection_exact_width_nnnorm_le_of_unit
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (hω : ∀ j, ‖ω j‖ ≤ 1)
    (i : Fin N) (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    ‖(sSup (Set.range (UEOT.V3.HilbertMeanUnitClip.unitClip
          (sourceActiveSection μ i μH ω))) -
          ∫ a, UEOT.V3.HilbertMeanUnitClip.unitClip
            (sourceActiveSection μ i μH ω) a ∂μ i) -
       (sInf (Set.range (UEOT.V3.HilbertMeanUnitClip.unitClip
          (sourceActiveSection μ i μH ω))) -
          ∫ a, UEOT.V3.HilbertMeanUnitClip.unitClip
            (sourceActiveSection μ i μH ω) a ∂μ i)‖₊
      ≤ (2 : ℝ≥0) / (N : ℝ≥0) := by
  exact centered_sourceActiveSection_exact_width_nnnorm_le
    hN μ ω hω i μH hμH hunit
    (integrable_sourceActiveSection_of_unit hN μ ω hω i μH hμH hunit)

end UEOT.V3.HilbertMeanSourceActiveIntegrability
