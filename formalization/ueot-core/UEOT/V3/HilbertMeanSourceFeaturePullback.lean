import UEOT.V3.HilbertMeanSourceRadius
import UEOT.V3.HilbertMeanFeatureProductBridge
import UEOT.V3.HilbertMeanCommonSampleUnion
import UEOT.V3.HilbertMeanSplitStatistic

/-!
# P-STAT-06 — one-channel raw-sample pullback

A measurable feature map is applied coordinatewise to one common raw product
sample.  The exact Hilbert-space P-STAT-06 radius bound is transported back to
the raw sample law by the measure-preserving feature-product map.
-/

namespace UEOT.V3.HilbertMeanSourceFeaturePullback

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanFeatureProductBridge
open UEOT.V3.HilbertMeanCommonSampleUnion
open UEOT.V3.HilbertMeanSourceRadius
open UEOT.V3.HilbertMeanSplitStatistic

universe uY uH

variable {Y : Type uY} {H : Type uH}
variable [MeasurableSpace Y]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- The exact-radius Hilbert bad event is measurable. -/
theorem measurableSet_sourceRadiusBad
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N L : ℕ} (alpha : ℝ) (μH : H) :
    MeasurableSet
      {ω : Fin N → H |
        pStat06SourceRadius N L alpha ≤ ‖empiricalMean ω - μH‖} := by
  exact measurableSet_le measurable_const
    (measurable_meanError (H := H) (N := N) μH)

/-- One source channel pulled back to the common raw sample law.  The marginal
Hilbert assumptions are stated on the pushed-forward laws. -/
theorem source_feature_tail_exact_radius_raw
    [BorelSpace H] [StandardBorelSpace H] [CompleteSpace H]
    [MeasurableAdd₂ H] [MeasurableSub H] [Nonempty H]
    {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (ν : Fin N → Measure Y) [∀ i, IsProbabilityMeasure (ν i)]
    (φ : Y → H) (hφ : Measurable φ)
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hInt : ∀ i, Integrable (fun x : H => x) ((ν i).map φ))
    (hmean : ∀ i, (∫ x : H, x ∂((ν i).map φ)) = μH)
    (hunit : ∀ i, ∀ᵐ x ∂((ν i).map φ), ‖x‖ ≤ 1) :
    (Measure.pi ν).real
      ((fun y : Fin N → Y => fun i => φ (y i)) ⁻¹'
        {ω : Fin N → H |
          pStat06SourceRadius N L alpha ≤ ‖empiricalMean ω - μH‖})
      ≤ alpha / (L : ℝ) := by
  let μ : Fin N → Measure H := fun i => (ν i).map φ
  letI (i : Fin N) : IsProbabilityMeasure (μ i) :=
    Measure.isProbabilityMeasure_map hφ.aemeasurable
  have htarget :
      (Measure.pi μ).real
        {ω : Fin N → H |
          pStat06SourceRadius N L alpha ≤ ‖empiricalMean ω - μH‖}
        ≤ alpha / (L : ℝ) := by
    exact source_meanError_tail_exact_radius
      hN hL halpha0 halpha1 μ μH hμH
      (by simpa [μ] using hInt)
      (by simpa [μ] using hmean)
      (by simpa [μ] using hunit)
  have hpres :
      MeasurePreserving
        (fun y : Fin N → Y => fun i => φ (y i))
        (Measure.pi ν) (Measure.pi μ) := by
    simpa [μ] using
      (measurePreserving_featureProduct_probability (ν := ν) (φ := φ) hφ)
  have hbad : NullMeasurableSet
      {ω : Fin N → H |
        pStat06SourceRadius N L alpha ≤ ‖empiricalMean ω - μH‖}
      (Measure.pi μ) :=
    (measurableSet_sourceRadiusBad (H := H) (N := N) (L := L) alpha μH).nullMeasurableSet
  rw [measureReal_preimage_eq_of_measurePreserving
    (Measure.pi ν) (Measure.pi μ)
    (fun y : Fin N → Y => fun i => φ (y i)) hpres _ hbad]
  exact htarget

/-- Source-facing form in which the feature mean and unit-ball support are
stated on the raw observation law.  Only Bochner integrability of the identity
under the pushed-forward feature law is kept explicit; this is exactly the
mean-embedding domain condition and avoids imposing separability on `H` merely
for a transport lemma. -/
theorem source_feature_tail_exact_radius_of_raw_mean_support
    [BorelSpace H] [StandardBorelSpace H] [CompleteSpace H]
    [MeasurableAdd₂ H] [MeasurableSub H] [Nonempty H]
    {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (ν : Fin N → Measure Y) [∀ i, IsProbabilityMeasure (ν i)]
    (φ : Y → H) (hφ : Measurable φ)
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hInt : ∀ i, Integrable (fun x : H => x) ((ν i).map φ))
    (hmeanRaw : ∀ i, (∫ y : Y, φ y ∂ν i) = μH)
    (hunitRaw : ∀ i, ∀ᵐ y ∂ν i, ‖φ y‖ ≤ 1) :
    (Measure.pi ν).real
      ((fun y : Fin N → Y => fun i => φ (y i)) ⁻¹'
        {ω : Fin N → H |
          pStat06SourceRadius N L alpha ≤ ‖empiricalMean ω - μH‖})
      ≤ alpha / (L : ℝ) := by
  have hmean : ∀ i, (∫ x : H, x ∂((ν i).map φ)) = μH := by
    intro i
    calc
      (∫ x : H, x ∂((ν i).map φ)) = ∫ y : Y, φ y ∂ν i := by
        simpa using
          (MeasureTheory.integral_map hφ.aemeasurable (hInt i).aestronglyMeasurable)
      _ = μH := hmeanRaw i
  have hunit : ∀ i, ∀ᵐ x ∂((ν i).map φ), ‖x‖ ≤ 1 := by
    intro i
    exact (ae_map_iff hφ.aemeasurable
      (measurableSet_le measurable_id.norm measurable_const)).2 (hunitRaw i)
  exact source_feature_tail_exact_radius_raw
    hN hL halpha0 halpha1 ν φ hφ μH hμH hInt hmean hunit

end UEOT.V3.HilbertMeanSourceFeaturePullback
