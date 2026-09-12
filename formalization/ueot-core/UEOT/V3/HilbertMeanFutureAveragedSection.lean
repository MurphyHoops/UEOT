import UEOT.V3.HilbertMeanCoordinateSection
import UEOT.V3.HilbertMeanContinuationWidth

/-!
# P-STAT-06 — future-averaged active-coordinate sections

A Doob continuation value fixes the revealed past and the active coordinate,
then averages the RKHS empirical-mean error statistic over all unrevealed
future coordinates.  This file connects the source `2/N` one-coordinate
sensitivity directly to that continuation value: probability averaging over an
arbitrary future law cannot enlarge the active-coordinate oscillation.
-/

namespace UEOT.V3.HilbertMeanFutureAveragedSection

open MeasureTheory
open UEOT.V3.HilbertMeanCoordinateSection

universe uH uA uB

variable {H : Type uH} {A : Type uA} {B : Type uB}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace A]

/-- The active-coordinate continuation value obtained after averaging over a
future probability law.  `base z` contains the fixed past together with one
realization `z` of the still-unrevealed coordinates; the active coordinate is
then overwritten by `φ v`. -/
noncomputable def futureAveragedSection {N : ℕ}
    (ξ : Measure A)
    (base : A → Fin N → H) (i : Fin N) (μH : H)
    (φ : B → H) (v : B) : ℝ :=
  ∫ z, coordinateErrorSection (base z) i μH (φ v) ∂ξ

/-- Exact continuation sensitivity: if every active feature vector has norm at
most one, integrating all future coordinates preserves the source `2/N`
pairwise oscillation bound. -/
theorem futureAveragedSection_pairwise_le_two_div
    {N : ℕ} (hN : 0 < N)
    (ξ : Measure A) [IsProbabilityMeasure ξ]
    (base : A → Fin N → H) (i : Fin N) (μH : H)
    (φ : B → H) (hφ : ∀ v, ‖φ v‖ ≤ 1)
    (hint : ∀ v, Integrable
      (fun z => coordinateErrorSection (base z) i μH (φ v)) ξ) :
    ∀ v w : B,
      |futureAveragedSection ξ base i μH φ v -
        futureAveragedSection ξ base i μH φ w| ≤ 2 / (N : ℝ) := by
  unfold futureAveragedSection
  apply UEOT.V3.HilbertMeanContinuationWidth.continuation_pairwise_abs_sub_le
      ξ (fun v z => coordinateErrorSection (base z) i μH (φ v)) hint
  intro v w
  filter_upwards with z
  exact coordinateErrorSection_pairwise_le_two_div
    hN (base z) i μH (φ v) (φ w) (hφ v) (hφ w)

/-- Centering the future-averaged continuation values by any common
past-dependent scalar does not enlarge their exact support interval: its width
remains at most `2/N`. -/
theorem futureAveragedSection_centered_interval_width_le
    [Nonempty B]
    {N : ℕ} (hN : 0 < N)
    (ξ : Measure A) [IsProbabilityMeasure ξ]
    (base : A → Fin N → H) (i : Fin N) (μH : H)
    (φ : B → H) (hφ : ∀ v, ‖φ v‖ ≤ 1)
    (hint : ∀ v, Integrable
      (fun z => coordinateErrorSection (base z) i μH (φ v)) ξ)
    (center : ℝ) :
    (sSup (Set.range (futureAveragedSection ξ base i μH φ)) - center) -
      (sInf (Set.range (futureAveragedSection ξ base i μH φ)) - center) ≤
        2 / (N : ℝ) := by
  apply UEOT.V3.HilbertMeanRangeWidth.centered_interval_width_le
    (futureAveragedSection ξ base i μH φ)
  exact futureAveragedSection_pairwise_le_two_div
    hN ξ base i μH φ hφ hint

end UEOT.V3.HilbertMeanFutureAveragedSection
