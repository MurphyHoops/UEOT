import UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency.Contract
import UEOT.V3.PredictiveClassRecovery
import Mathlib.Tactic.Linarith

/-!
# P3.2 — predictive-class consistency

This module does not reprove P-STAT-05.  It supplies the asymptotic bridge:
vanishing response-TV error plus a positive true predictive separation margin
eventually satisfies the finite-sample P-STAT-05 gap condition, hence every
realized estimator sequence obeying those response bounds eventually recovers
exactly the true predictive relation.
-/

namespace UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency

open Filter Topology MeasureTheory
open UEOT.V3.TotalVariation
open UEOT.V3.PredictiveClassRecovery

universe uH uI uY

variable {H : Type uH} {I : Type uI} {Y : Type uY}
variable [MeasurableSpace Y]

/-- Any vanishing response radius eventually satisfies the exact P-STAT-05
margin inequality for a fixed positive predictive gap. -/
theorem eventually_two_mul_lt_half
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ n in atTop, 2 * η n < γ / 2 := by
  have hmul : Tendsto (fun n => 2 * η n) atTop (𝓝 0) := by
    simpa using hη.const_mul (2 : ℝ)
  exact (tendsto_order.mp hmul).2 (γ / 2) (by linarith)

/-- Deterministic realized-sequence closure of P-STAT-05.

The probabilistic finite-sample theorem supplies `hresp` on its good event.
This theorem intentionally does not impose one common sample space across `n`.
-/
theorem eventually_exact_predictive_recovery
    [Fintype H] [Fintype I] [Nonempty I]
    (p : H → I → Measure Y)
    (pHat : ℕ → H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (hpHat : ∀ n h i, IsProbabilityMeasure (pHat n h i))
    (η : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (hresp : ∀ n h i, tvDist (p h i) (pHat n h i) ≤ η n)
    (γ : ℝ) (hγ : 0 < γ)
    (hsep : ∀ h h', ¬ trueEquivalent p h h' →
      γ ≤ protocolDistance p h h') :
    ∀ᶠ n in atTop, ∀ h h' : H,
      protocolDistance (pHat n) h h' ≤ γ / 2 ↔ trueEquivalent p h h' := by
  filter_upwards [eventually_two_mul_lt_half hη hγ] with n hgap
  exact p_stat_05 p (pHat n) hp (hpHat n) (η n) γ
    (hresp n) hsep hgap

end UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency
