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
open UEOT.V3.HilbertMeanAzuma
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

/-- The filtration-native fiber agrees with the full-sample centered clipped
section at every active value, once the same strict past is fixed. -/
theorem pastCenteredClippedActiveSection_blockProjection_apply
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H) (ω : Fin N → H) (a : H) :
    pastCenteredClippedActiveSection μ i μH
        (blockProjection (past i) ω, a) =
      centeredClippedActiveSection μ i μH ω a := by
  have hpoint (b : H) :
      pastActiveClippedContinuation μ i μH
          (blockProjection (past i) ω, b) =
        unitClip (sourceActiveSection μ i μH ω) b := by
    by_cases hb : ‖b‖ ≤ 1
    · simp [pastActiveClippedContinuation, unitClip, hb,
        sourceActiveSection, pastActiveContinuation_blockProjection_update]
    · simp [pastActiveClippedContinuation, unitClip, hb,
        sourceActiveSection, pastActiveContinuation_blockProjection_update]
  unfold pastCenteredClippedActiveSection centeredClippedActiveSection
  rw [hpoint a]
  congr 1
  apply integral_congr_ae
  filter_upwards with b
  exact hpoint b

/-- The observed active coordinate is the previous special case. -/
theorem pastCenteredClippedActiveSection_blockProjection
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H) (ω : Fin N → H) :
    pastCenteredClippedActiveSection μ i μH
        (blockProjection (past i) ω, ω i) =
      centeredClippedActiveSection μ i μH ω (ω i) :=
  pastCenteredClippedActiveSection_blockProjection_apply μ i μH ω (ω i)

/-- Canonically extend a strict-past block to a full sample by filling all
unrevealed coordinates with zero.  Only the past projection matters below. -/
def pastExtension {N : ℕ} (i : Fin N) (x : past i → H) : Fin N → H :=
  fun j => if h : j ∈ past i then x ⟨j, h⟩ else 0

@[simp] theorem blockProjection_pastExtension
    {N : ℕ} (i : Fin N) (x : past i → H) :
    blockProjection (past i) (pastExtension i x) = x := by
  funext j
  simp [blockProjection, pastExtension, j.2]

/-- A unit strict-past block gives an exact `1/N²` ordinary sub-Gaussian active
fiber, now stated entirely in filtration-native coordinates. -/
theorem hasSubgaussianMGF_pastCenteredClippedActiveSection_invSqParam
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (x : past i → H)
    (hx : ∀ j, ‖x j‖ ≤ 1)
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    HasSubgaussianMGF
      (fun a => pastCenteredClippedActiveSection μ i μH (x, a))
      (invSqParam N)
      (μ i) := by
  let ω : Fin N → H := pastExtension i x
  have hpast : ∀ j : past i, ‖ω (j : Fin N)‖ ≤ 1 := by
    intro j
    simpa [ω, pastExtension, j.2] using hx j
  have hsg :=
    hasSubgaussianMGF_centeredClippedActiveSection_invSqParam_of_pastUnit
      hN μ ω i hpast μH hμH hunit
  have heq :
      (fun a => pastCenteredClippedActiveSection μ i μH (x, a)) =
        centeredClippedActiveSection μ i μH ω := by
    funext a
    rw [← blockProjection_pastExtension i x]
    exact pastCenteredClippedActiveSection_blockProjection_apply μ i μH ω a
  rw [heq]
  exact hsg

end UEOT.V3.HilbertMeanPastActiveClippedFiber
