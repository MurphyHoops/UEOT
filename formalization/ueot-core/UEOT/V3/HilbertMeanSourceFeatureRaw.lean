import UEOT.V3.HilbertMeanSourceFeaturePullback
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# P-STAT-06 — raw feature assumptions

This wrapper derives the pushed-forward Hilbert marginal hypotheses from the
source-natural assumptions on the raw feature map: Bochner integrability,
correct feature mean, and almost-everywhere unit-ball support.
-/

namespace UEOT.V3.HilbertMeanSourceFeatureRaw

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanSourceFeaturePullback
open UEOT.V3.HilbertMeanSourceRadius

universe uY uH

variable {Y : Type uY} {H : Type uH}
variable [MeasurableSpace Y]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- Exact one-channel raw-sample radius bound under source-natural feature
assumptions. -/
theorem source_feature_tail_exact_radius_raw_assumptions
    [BorelSpace H] [StandardBorelSpace H] [CompleteSpace H]
    [MeasurableAdd₂ H] [MeasurableSub H] [Nonempty H]
    {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (ν : Fin N → Measure Y) [∀ i, IsProbabilityMeasure (ν i)]
    (φ : Y → H) (hφ : Measurable φ)
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hInt : ∀ i, Integrable φ (ν i))
    (hmean : ∀ i, (∫ y, φ y ∂ν i) = μH)
    (hunit : ∀ i, ∀ᵐ y ∂ν i, ‖φ y‖ ≤ 1) :
    (Measure.pi ν).real
      ((fun y : Fin N → Y => fun i => φ (y i)) ⁻¹'
        {ω : Fin N → H |
          pStat06SourceRadius N L alpha ≤ ‖empiricalMean ω - μH‖})
      ≤ alpha / (L : ℝ) := by
  have hid : ∀ i, AEStronglyMeasurable (fun x : H => x) ((ν i).map φ) := by
    intro i
    simpa only [id_eq] using (hInt i).aestronglyMeasurable.aestronglyMeasurable_id_map
  have hIntMap : ∀ i, Integrable (fun x : H => x) ((ν i).map φ) := by
    intro i
    apply (integrable_map_measure (hid i) hφ.aemeasurable).2
    change Integrable φ (ν i)
    exact hInt i
  have hmeanMap : ∀ i, (∫ x : H, x ∂((ν i).map φ)) = μH := by
    intro i
    rw [integral_map hφ.aemeasurable (hid i)]
    change (∫ y, φ y ∂ν i) = μH
    exact hmean i
  have hunitMap : ∀ i, ∀ᵐ x ∂((ν i).map φ), ‖x‖ ≤ 1 := by
    intro i
    have hs : MeasurableSet {x : H | ‖x‖ ≤ 1} :=
      measurableSet_le (by fun_prop) measurable_const
    exact (ae_map_iff hφ.aemeasurable hs).2 (hunit i)
  exact source_feature_tail_exact_radius_raw
    hN hL halpha0 halpha1 ν φ hφ μH hμH hIntMap hmeanMap hunitMap

end UEOT.V3.HilbertMeanSourceFeatureRaw
