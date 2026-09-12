import UEOT.V3.HilbertMeanDoobStatisticBridge
import UEOT.V3.HilbertMeanContinuationWidth

/-!
# P-STAT-06 — exact active-coordinate width of the source continuation

For fixed revealed past and a fixed future realization, changing the active
coordinate changes the assembled full sample at exactly one coordinate.  The
source `2/N` deterministic sensitivity therefore holds pointwise in the future,
and probability averaging preserves that exact width.
-/

namespace UEOT.V3.HilbertMeanSourceContinuationWidth

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanPrefixFutureAssembly
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanSplitStatistic
open UEOT.V3.HilbertMeanDoobStatisticBridge
open UEOT.V3.HilbertMeanContinuationWidth

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- With the same strict-future realization, two active-coordinate values
produce assembled samples that agree off the active coordinate. -/
theorem assembled_updatedPrefix_eq_off
    {N : ℕ} (ω : Fin N → H) (i : Fin N) (a b : H)
    (y : future i → H) :
    ∀ j, j ≠ i →
      assemblePrefixFuture i
          (blockProjection (prefixBlock i.1) (Function.update ω i a)) y j =
        assemblePrefixFuture i
          (blockProjection (prefixBlock i.1) (Function.update ω i b)) y j := by
  intro j hji
  unfold assemblePrefixFuture blockProjection
  split
  · simp [Function.update, hji]
  · rfl

/-- The assembled active coordinate is exactly the value used to update the
revealed prefix. -/
@[simp] theorem assembled_updatedPrefix_active
    {N : ℕ} (ω : Fin N → H) (i : Fin N) (a : H)
    (y : future i → H) :
    assemblePrefixFuture i
      (blockProjection (prefixBlock i.1) (Function.update ω i a)) y i = a := by
  unfold assemblePrefixFuture blockProjection
  simp

/-- Pointwise-in-future source sensitivity for the split statistic. -/
theorem splitMeanError_updatedPrefix_pairwise_le_two_div
    {N : ℕ} (hN : 0 < N)
    (ω : Fin N → H) (i : Fin N) (μH : H)
    (a b : H) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (y : future i → H) :
    |splitMeanError i μH
        (blockProjection (prefixBlock i.1) (Function.update ω i a), y) -
      splitMeanError i μH
        (blockProjection (prefixBlock i.1) (Function.update ω i b), y)| ≤
      2 / (N : ℝ) := by
  unfold splitMeanError
  apply abs_norm_sub_mean_diff_le_two_div hN _ _ i
  · exact assembled_updatedPrefix_eq_off ω i a b y
  · simpa using ha
  · simpa using hb

/-- Exact `2/N` active-coordinate oscillation of the explicit source
continuation.  Integrability of each future section is kept explicit here and
will be discharged separately from the source unit-ball support. -/
theorem sourceContinuation_update_pairwise_le_two_div
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (i : Fin N) (μH : H)
    (a b : H) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hint : ∀ v : H, Integrable
      (fun y => splitMeanError i μH
        (blockProjection (prefixBlock i.1) (Function.update ω i v), y))
      (blockLaw μ (future i))) :
    |sourceContinuation μ i μH (Function.update ω i a) -
      sourceContinuation μ i μH (Function.update ω i b)| ≤
      2 / (N : ℝ) := by
  unfold sourceContinuation
  apply continuation_pairwise_abs_sub_le
    (blockLaw μ (future i))
    (fun v y => splitMeanError i μH
      (blockProjection (prefixBlock i.1) (Function.update ω i v), y)) hint
  intro v w
  filter_upwards with y
  exact splitMeanError_updatedPrefix_pairwise_le_two_div
    hN ω i μH v w (by assumption) (by assumption) y

end UEOT.V3.HilbertMeanSourceContinuationWidth
