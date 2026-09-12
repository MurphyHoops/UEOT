import UEOT.V3.HilbertMeanSourceFiberHoeffding
import UEOT.V3.HilbertMeanSplitStatistic

/-!
# P-STAT-06 — clipped/raw source fiber transfer

The clipping device is only an analytic adapter for global range bounds.  On
the canonical product law the observed active coordinate is in the unit ball
almost everywhere, and the active marginal is supported there almost
everywhere.  Hence the observed centered clipped fiber agrees almost everywhere
with the raw centered active section that identifies the actual Doob increment.
-/

namespace UEOT.V3.HilbertMeanSourceClipTransfer

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanDoobStatisticBridge
open UEOT.V3.HilbertMeanSourceCenteredFiber
open UEOT.V3.HilbertMeanSourceFiberHoeffding
open UEOT.V3.HilbertMeanSplitStatistic
open UEOT.V3.HilbertMeanUnitClip

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- The centered clipped active fiber evaluated at the observed active sample. -/
noncomputable def observedCenteredClippedActiveSection {N : ℕ}
    (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (ω : Fin N → H) : ℝ :=
  centeredClippedActiveSection μ i μH ω (ω i)

/-- The raw centered active section appearing in the exact Doob-increment
identification. -/
noncomputable def observedCenteredRawActiveSection {N : ℕ}
    (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (ω : Fin N → H) : ℝ :=
  sourceContinuation μ i μH ω -
    ∫ a, sourceActiveSection μ i μH ω a ∂μ i

/-- Under the frozen marginal unit-ball support assumption, clipping is exactly
an almost-everywhere no-op on the observed centered source fiber. -/
theorem observedCenteredClippedActiveSection_ae_eq_raw
    [BorelSpace H]
    {N : ℕ}
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    observedCenteredClippedActiveSection μ i μH =ᵐ[Measure.pi μ]
      observedCenteredRawActiveSection μ i μH := by
  have hall : ∀ᵐ ω ∂Measure.pi μ, ∀ j, ‖ω j‖ ≤ 1 :=
    ae_unit_all_of_marginals μ hunit
  filter_upwards [hall] with ω hω
  have hclipObs :
      unitClip (sourceActiveSection μ i μH ω) (ω i) =
        sourceActiveSection μ i μH ω (ω i) :=
    unitClip_eq_of_norm_le _ (hω i)
  have hclipInt :
      (∫ a, unitClip (sourceActiveSection μ i μH ω) a ∂μ i) =
        ∫ a, sourceActiveSection μ i μH ω a ∂μ i :=
    integral_unitClip_eq (μ i) (sourceActiveSection μ i μH ω) (hunit i)
  unfold observedCenteredClippedActiveSection
    observedCenteredRawActiveSection centeredClippedActiveSection
  rw [hclipObs, hclipInt]
  simp [sourceActiveSection]

end UEOT.V3.HilbertMeanSourceClipTransfer
