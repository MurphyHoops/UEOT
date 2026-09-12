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
    (xy : (prefixBlock (N := N) i.1 → H) × (future i → H)) : ℝ :=
  ‖empiricalMean (assemblePrefixFuture i xy.1 xy.2) - μH‖

/-- Exact source reconstruction: projecting a full sample into prefix/future
blocks and evaluating the split statistic gives the original Hilbert mean
error, with no almost-everywhere qualification. -/
@[simp] theorem splitMeanError_blockProjections
    {N : ℕ} (i : Fin N) (μH : H) (ω : Fin N → H) :
    splitMeanError i μH
      (blockProjection (prefixBlock (N := N) i.1) ω, blockProjection (future i) ω) =
      ‖empiricalMean ω - μH‖ := by
  unfold splitMeanError
  rw [assemblePrefixFuture_blockProjections]

/-- The finite Hilbert empirical mean is continuous for the product topology. -/
theorem continuous_empiricalMean {N : ℕ} :
    Continuous (empiricalMean : (Fin N → H) → H) := by
  unfold empiricalMean
  have hsum : Continuous (fun x : Fin N → H => ∑ i, x i) := by
    exact continuous_finsetSum Finset.univ (fun i _ => continuous_apply i)
  exact hsum.const_smul ((N : ℝ)⁻¹)

/-- The finite Hilbert empirical mean is measurable for the canonical product
Borel structure. -/
theorem measurable_empiricalMean
    [MeasurableSpace H] [BorelSpace H] {N : ℕ} :
    Measurable (empiricalMean : (Fin N → H) → H) := by
  exact (continuous_empiricalMean (H := H) (N := N)).measurable

/-- The source mean-error statistic is measurable. -/
theorem measurable_meanError
    [MeasurableSpace H] [BorelSpace H]
    {N : ℕ} (μH : H) :
    Measurable (fun ω : Fin N → H => ‖empiricalMean ω - μH‖) := by
  exact (((continuous_empiricalMean (H := H) (N := N)).sub continuous_const).norm).measurable

/-- The source split statistic is measurable. -/
theorem measurable_splitMeanError
    [MeasurableSpace H] [BorelSpace H]
    {N : ℕ} (i : Fin N) (μH : H) :
    Measurable (splitMeanError i μH) := by
  have h := (measurable_meanError (H := H) (N := N) μH).comp
    (measurable_assemblePrefixFuture (H := H) i)
  simpa [splitMeanError] using h

/-- Since the codomain is real, measurability upgrades directly to strong
measurability. -/
theorem stronglyMeasurable_splitMeanError
    [MeasurableSpace H] [BorelSpace H]
    {N : ℕ} (i : Fin N) (μH : H) :
    StronglyMeasurable (splitMeanError i μH) := by
  exact (measurable_splitMeanError (H := H) i μH).stronglyMeasurable

/-- Marginal almost-everywhere unit-ball support lifts to simultaneous
unit-ball support under the canonical finite product law. -/
theorem ae_unit_all_of_marginals
    [MeasurableSpace H] [BorelSpace H]
    {N : ℕ}
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (hunit : ∀ i, ∀ᵐ x ∂μ i, ‖x‖ ≤ 1) :
    ∀ᵐ ω ∂Measure.pi μ, ∀ i, ‖ω i‖ ≤ 1 := by
  apply ae_all_iff.2
  intro i
  have hLaw : HasLaw (fun ω : Fin N → H => ω i) (μ i) (Measure.pi μ) :=
    (measurePreserving_eval μ i).hasLaw
  exact (hLaw.ae_iff (by fun_prop)).2 (hunit i)

/-- Every finite coordinate-block law inherits the marginal unit-ball support. -/
theorem ae_block_unit_of_marginals
    [MeasurableSpace H] [BorelSpace H]
    {N : ℕ}
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (S : Finset (Fin N))
    (hunit : ∀ i, ∀ᵐ x ∂μ i, ‖x‖ ≤ 1) :
    ∀ᵐ y ∂blockLaw μ S, ∀ j, ‖y j‖ ≤ 1 := by
  apply ae_all_iff.2
  intro j
  have hLaw := block_hasLaw μ S
  have hfull : ∀ᵐ ω ∂Measure.pi μ, ‖blockProjection S ω j‖ ≤ 1 := by
    have hcoord : HasLaw (fun ω : Fin N → H => ω (j : Fin N))
        (μ (j : Fin N)) (Measure.pi μ) :=
      (measurePreserving_eval μ (j : Fin N)).hasLaw
    exact (hcoord.ae_iff (by fun_prop)).2 (hunit (j : Fin N))
  exact (hLaw.ae_iff (by fun_prop)).1 hfull

/-- Under simultaneous unit-ball support, the full source statistic is
integrable on the canonical product law. -/
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

/-- Marginal source support is enough to obtain integrability of the full
Hilbert mean-error statistic; no extra joint-support assumption is required. -/
theorem integrable_meanError_of_marginal_ae_unit
    [MeasurableSpace H] [BorelSpace H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ i, ∀ᵐ x ∂μ i, ‖x‖ ≤ 1) :
    Integrable (fun ω : Fin N → H => ‖empiricalMean ω - μH‖) (Measure.pi μ) := by
  exact integrable_meanError_of_ae_unit hN μ μH hμH
    (ae_unit_all_of_marginals μ hunit)

/-- For any fixed unit-ball prefix, the source split statistic is integrable
over the strict-future block law. -/
theorem integrable_splitMeanError_future_of_unit
    [MeasurableSpace H] [BorelSpace H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H) (hμH : ‖μH‖ ≤ 1)
    (x : prefixBlock (N := N) i.1 → H) (hx : ∀ j, ‖x j‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    Integrable (fun y : future i → H => splitMeanError i μH (x, y))
      (blockLaw μ (future i)) := by
  letI : IsProbabilityMeasure (blockLaw μ (future i)) :=
    blockLaw_isProbability μ (future i)
  have hy := ae_block_unit_of_marginals μ (future i) hunit
  have hmeas : Measurable (fun y : future i → H => splitMeanError i μH (x, y)) := by
    exact (measurable_splitMeanError (H := H) i μH).comp
      (measurable_const.prod_mk measurable_id)
  refine Integrable.of_bound hmeas.aestronglyMeasurable 2 ?_
  filter_upwards [hy] with y hy
  have hall : ∀ j, ‖assemblePrefixFuture i x y j‖ ≤ 1 :=
    assemblePrefixFuture_norm_le_one i x y hx hy
  simpa [splitMeanError, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_empiricalMean_sub_le_two hN (assemblePrefixFuture i x y) hall μH hμH

end UEOT.V3.HilbertMeanSplitStatistic
