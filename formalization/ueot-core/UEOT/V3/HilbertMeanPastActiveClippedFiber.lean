import UEOT.V3.HilbertMeanPastActiveContinuation
import UEOT.V3.HilbertMeanSourceFiberHoeffding
import UEOT.V3.HilbertMeanUnitClip
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P-STAT-06 — filtration-native centered clipped active fiber

The conditional-MGF argument should be expressed directly on the strict-past
block and the active coordinate.  This module packages that representation.
The future has already been averaged out by `pastActiveContinuation`; clipping
acts only on the active coordinate and is therefore compatible with the
source marginal unit-ball support assumption.
-/

namespace UEOT.V3.HilbertMeanPastActiveClippedFiber

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanPastActiveContinuation
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanSourceCenteredFiber
open UEOT.V3.HilbertMeanSourceFiberHoeffding
open UEOT.V3.HilbertMeanUnitClip

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- The strict-past/active continuation clipped only in the active coordinate. -/
noncomputable def pastActiveClippedContinuation {N : ℕ}
    (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (z : (past i → H) × H) : ℝ :=
  if ‖z.2‖ ≤ 1 then
    pastActiveContinuation μ i μH z
  else
    pastActiveContinuation μ i μH (z.1, 0)

/-- The clipped continuation is strongly measurable on strict-past × active. -/
theorem stronglyMeasurable_pastActiveClippedContinuation
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H) :
    StronglyMeasurable (pastActiveClippedContinuation μ i μH) := by
  have hbase := stronglyMeasurable_pastActiveContinuation μ i μH
  have hset : MeasurableSet {z : (past i → H) × H | ‖z.2‖ ≤ 1} := by
    exact measurableSet_le (measurable_snd.norm) measurable_const
  have hzero : StronglyMeasurable
      (fun z : (past i → H) × H =>
        pastActiveContinuation μ i μH (z.1, 0)) := by
    exact hbase.comp_measurable
      (Measurable.prodMk measurable_fst measurable_const)
  have hpiece : StronglyMeasurable
      ({z : (past i → H) × H | ‖z.2‖ ≤ 1}.piecewise
        (pastActiveContinuation μ i μH)
        (fun z => pastActiveContinuation μ i μH (z.1, 0))) :=
    hbase.piecewise hset hzero
  rw [show pastActiveClippedContinuation μ i μH =
      {z : (past i → H) × H | ‖z.2‖ ≤ 1}.piecewise
        (pastActiveContinuation μ i μH)
        (fun z => pastActiveContinuation μ i μH (z.1, 0)) by
      funext z
      simp [pastActiveClippedContinuation, Set.piecewise]]
  exact hpiece

/-- Center the clipped active continuation by its active-marginal mean, keeping
strict past fixed. -/
noncomputable def pastCenteredClippedActiveSection {N : ℕ}
    (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (z : (past i → H) × H) : ℝ :=
  pastActiveClippedContinuation μ i μH z -
    ∫ b, pastActiveClippedContinuation μ i μH (z.1, b) ∂μ i

/-- The centered clipped past-active fiber is strongly measurable. -/
theorem stronglyMeasurable_pastCenteredClippedActiveSection
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H) :
    StronglyMeasurable (pastCenteredClippedActiveSection μ i μH) := by
  have hclip := stronglyMeasurable_pastActiveClippedContinuation μ i μH
  have hmean : StronglyMeasurable
      (fun x : past i → H =>
        ∫ b, pastActiveClippedContinuation μ i μH (x, b) ∂μ i) := by
    exact hclip.integral_prod_right'
  exact hclip.sub (hmean.comp_measurable measurable_fst)

/-- For a full sample, the filtration-native clipped fiber is exactly the
previous full-sample centered clipped active section. -/
theorem pastCenteredClippedActiveSection_blockProjection
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H) (ω : Fin N → H) :
    pastCenteredClippedActiveSection μ i μH
        (blockProjection (past i) ω, ω i) =
      centeredClippedActiveSection μ i μH ω (ω i) := by
  have hpoint (a : H) :
      pastActiveClippedContinuation μ i μH
          (blockProjection (past i) ω, a) =
        unitClip (sourceActiveSection μ i μH ω) a := by
    by_cases ha : ‖a‖ ≤ 1
    · simp [pastActiveClippedContinuation, unitClip, ha,
        sourceActiveSection, pastActiveContinuation_blockProjection_update]
    · simp [pastActiveClippedContinuation, unitClip, ha,
        sourceActiveSection, pastActiveContinuation_blockProjection_update]
  unfold pastCenteredClippedActiveSection centeredClippedActiveSection
  rw [hpoint (ω i)]
  congr 1
  apply integral_congr_ae
  filter_upwards with a
  exact hpoint a

end UEOT.V3.HilbertMeanPastActiveClippedFiber
