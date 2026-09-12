import UEOT.V3.HilbertMeanConcentration
import UEOT.V3.HilbertMeanPrefixFutureAssembly

/-!
# P-STAT-06 — source Hilbert statistic in prefix/future coordinates

The actual source statistic is the norm error of the empirical Hilbert mean.
This module rewrites that statistic in the canonical prefix/future coordinates
used by the Doob construction and records exact reconstruction on a full sample.
-/

namespace UEOT.V3.HilbertMeanSplitStatistic

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanPrefixFutureAssembly

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Hilbert empirical-mean error written as a function of the revealed prefix
and strict future blocks at a genuine sample index `i`. -/
noncomputable def splitMeanError {N : ℕ} (i : Fin N) (μH : H)
    (xy : (prefixBlock i.1 → H) × (future i → H)) : ℝ :=
  ‖empiricalMean (assemblePrefixFuture i xy.1 xy.2) - μH‖

/-- Exact source reconstruction: projecting a full sample into prefix/future
blocks and evaluating the split statistic gives the original Hilbert mean
error, with no almost-everywhere qualification. -/
@[simp] theorem splitMeanError_blockProjections
    {N : ℕ} (i : Fin N) (μH : H) (ω : Fin N → H) :
    splitMeanError i μH
      (blockProjection (prefixBlock i.1) ω, blockProjection (future i) ω) =
      ‖empiricalMean ω - μH‖ := by
  unfold splitMeanError
  rw [assemblePrefixFuture_blockProjections]

/-- The finite Hilbert empirical mean is measurable for the canonical product
Borel structure. -/
theorem measurable_empiricalMean
    [MeasurableSpace H] [BorelSpace H] {N : ℕ} :
    Measurable (empiricalMean : (Fin N → H) → H) := by
  unfold empiricalMean
  fun_prop

/-- The source mean-error statistic is measurable. -/
theorem measurable_meanError
    [MeasurableSpace H] [BorelSpace H]
    {N : ℕ} (μH : H) :
    Measurable (fun ω : Fin N → H => ‖empiricalMean ω - μH‖) := by
  exact ((measurable_empiricalMean (H := H)).sub measurable_const).norm

/-- The source split statistic is measurable. -/
theorem measurable_splitMeanError
    [MeasurableSpace H] [BorelSpace H]
    {N : ℕ} (i : Fin N) (μH : H) :
    Measurable (splitMeanError i μH) := by
  unfold splitMeanError
  have ha := measurable_assemblePrefixFuture (H := H) i
  have hm : Measurable (empiricalMean : (Fin N → H) → H) :=
    measurable_empiricalMean (H := H)
  exact ((hm.comp ha).sub measurable_const).norm

/-- Since the codomain is real, measurability upgrades directly to strong
measurability.  This discharges the analytic measurability hypothesis of the
source Doob continuation bridge. -/
theorem stronglyMeasurable_splitMeanError
    [MeasurableSpace H] [BorelSpace H]
    {N : ℕ} (i : Fin N) (μH : H) :
    StronglyMeasurable (splitMeanError i μH) := by
  exact (measurable_splitMeanError (H := H) i μH).stronglyMeasurable

/-- Under the source unit-ball assumptions, the Hilbert mean-error statistic is
integrable on the canonical product law.  The only probabilistic support input
needed is the simultaneous almost-everywhere unit bound on all coordinates. -/
theorem integrable_meanError_of_ae_unit
    [MeasurableSpace H] [BorelSpace H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ᵐ ω ∂Measure.pi μ, ∀ i, ‖ω i‖ ≤ 1) :
    Integrable (fun ω : Fin N → H => ‖empiricalMean ω - μH‖) (Measure.pi μ) := by
  refine Integrable.of_bound
    (measurable_meanError (H := H) μH).aestronglyMeasurable 2 ?_
  filter_upwards [hunit] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_empiricalMean_sub_le_two hN ω hω μH hμH

end UEOT.V3.HilbertMeanSplitStatistic
