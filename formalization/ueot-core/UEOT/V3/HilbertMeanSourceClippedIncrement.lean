import UEOT.V3.HilbertMeanPastActiveClippedFiber
import UEOT.V3.HilbertMeanSplitStatistic
import Mathlib.Tactic

/-!
# P-STAT-06 — observed filtration-native clipped increment

This module turns the strict-past/active centered clipped fiber into an actual
random variable on the canonical product sample space.  Its exact `2/N`
envelope implies global exponential integrability, which is the analytic input
needed by the rational conditional-MGF lift.
-/

namespace UEOT.V3.HilbertMeanSourceClippedIncrement

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanPastActiveClippedFiber
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanSplitStatistic

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- The centered clipped active fiber observed at the strict-past block and the
actual active coordinate. -/
noncomputable def sourceClippedIncrement {N : ℕ}
    (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (ω : Fin N → H) : ℝ :=
  pastCenteredClippedActiveSection μ i μH
    (blockProjection (past i) ω, ω i)

/-- The observed clipped increment is strongly measurable. -/
theorem stronglyMeasurable_sourceClippedIncrement
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H) :
    StronglyMeasurable (sourceClippedIncrement μ i μH) := by
  have hG := stronglyMeasurable_pastCenteredClippedActiveSection μ i μH
  exact hG.comp_measurable
    (Measurable.prodMk
      (measurable_blockProjection (H := H) (past i))
      (measurable_pi_apply i))

/-- Under marginal unit-ball support, the observed clipped increment is almost
everywhere bounded by the exact McDiarmid envelope `2/N`. -/
theorem ae_abs_sourceClippedIncrement_le_two_div
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    ∀ᵐ ω ∂Measure.pi μ,
      |sourceClippedIncrement μ i μH ω| ≤ 2 / (N : ℝ) := by
  have hall : ∀ᵐ ω ∂Measure.pi μ, ∀ j, ‖ω j‖ ≤ 1 :=
    ae_unit_all_of_marginals μ hunit
  filter_upwards [hall] with ω hω
  have hpast : ∀ j : past i,
      ‖blockProjection (past i) ω j‖ ≤ 1 := by
    intro j
    simpa [blockProjection] using hω (j : Fin N)
  exact abs_pastCenteredClippedActiveSection_le_two_div
    hN μ i (blockProjection (past i) ω) hpast μH hμH hunit (ω i)

/-- Every real exponential moment of the observed clipped increment is
integrable under the finite product probability law. -/
theorem integrable_exp_mul_sourceClippedIncrement
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1)
    (t : ℝ) :
    Integrable
      (fun ω => exp (t * sourceClippedIncrement μ i μH ω))
      (Measure.pi μ) := by
  letI : IsProbabilityMeasure (Measure.pi μ) := Measure.pi.isProbabilityMeasure
  have hX := stronglyMeasurable_sourceClippedIncrement μ i μH
  have hmeas : Measurable
      (fun ω => exp (t * sourceClippedIncrement μ i μH ω)) :=
    Real.measurable_exp.comp
      (measurable_const.mul hX.measurable)
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (exp (|t| * (2 / (N : ℝ)))) ?_
  filter_upwards [ae_abs_sourceClippedIncrement_le_two_div
    hN μ i μH hμH hunit] with ω hω
  have hmul : t * sourceClippedIncrement μ i μH ω ≤
      |t| * (2 / (N : ℝ)) := by
    calc
      t * sourceClippedIncrement μ i μH ω
          ≤ |t * sourceClippedIncrement μ i μH ω| := le_abs_self _
      _ = |t| * |sourceClippedIncrement μ i μH ω| := abs_mul _ _
      _ ≤ |t| * (2 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hω (abs_nonneg t)
  have hexp := Real.exp_le_exp.mpr hmul
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hexp

end UEOT.V3.HilbertMeanSourceClippedIncrement
