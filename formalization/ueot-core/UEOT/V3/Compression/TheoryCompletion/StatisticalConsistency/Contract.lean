import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real

/-!
# P3.0 — changing-sample-space statistical consistency contract

The contract deliberately contains only confidence/failure schedules.  It does
not package a sample space `Ω`, so different sample sizes may use different
probability spaces.  Concrete finite-sample theorems provide their own measure
spaces; P3 composes them through the shared numerical schedules instead of
silently assuming one common probability space.
-/

namespace UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency

open Filter Topology MeasureTheory

/-- A sample-size indexed high-probability consistency schedule.

`failure n` is the finite-sample failure bound and `radius n` is the associated
estimation radius.  Both vanish asymptotically.  The object is intentionally
sample-space agnostic. -/
structure ConfidenceSchedule where
  failure : ℕ → ℝ
  radius : ℕ → ℝ
  failure_pos : ∀ n, 0 < failure n
  failure_le_one : ∀ n, failure n ≤ 1
  radius_nonneg : ∀ n, 0 ≤ radius n
  failure_tendsto_zero : Tendsto failure atTop (𝓝 0)
  radius_tendsto_zero : Tendsto radius atTop (𝓝 0)

namespace ConfidenceSchedule

/-- Every positive tolerance eventually dominates the certified radius. -/
theorem eventually_radius_lt (C : ConfidenceSchedule)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, C.radius n < ε :=
  (tendsto_order.mp C.radius_tendsto_zero).2 ε hε

/-- Every positive tolerance eventually dominates the finite-sample failure
bound. -/
theorem eventually_failure_lt (C : ConfidenceSchedule)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, C.failure n < ε :=
  (tendsto_order.mp C.failure_tendsto_zero).2 ε hε

end ConfidenceSchedule

universe uΩ

/-- A high-probability event contract whose sample space may genuinely change
with sample size.  No identification between `Ω n` and `Ω m` is assumed. -/
structure ChangingSampleEventContract
    (Ω : ℕ → Type uΩ) [∀ n, MeasurableSpace (Ω n)] where
  schedule : ConfidenceSchedule
  μ : ∀ n, Measure (Ω n)
  probability : ∀ n, IsProbabilityMeasure (μ n)
  good : ∀ n, Set (Ω n)
  bad_le_failure : ∀ n, (μ n).real ((good n)ᶜ) ≤ schedule.failure n

namespace ChangingSampleEventContract

/-- A vanishing certified failure schedule forces the actual bad-event
probabilities to vanish, without placing all experiments on one probability
space. -/
theorem bad_probability_tendsto_zero
    {Ω : ℕ → Type uΩ} [∀ n, MeasurableSpace (Ω n)]
    (C : ChangingSampleEventContract Ω) :
    Tendsto (fun n => (C.μ n).real ((C.good n)ᶜ)) atTop (𝓝 0) := by
  exact squeeze_zero
    (fun _ => measureReal_nonneg)
    C.bad_le_failure
    C.schedule.failure_tendsto_zero

end ChangingSampleEventContract

end UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency
