import UEOT.V3.HilbertMeanSourceFeatureRaw
import UEOT.V3.MMDTransport

/-!
# P-STAT-06 — RKHS mean-embedding source wrapper

The empirical MMD statistic is represented directly in the source's Hilbert
mean-embedding semantics as the distance between the empirical feature mean
and the population Bochner mean embedding.
-/

namespace UEOT.V3.HilbertMeanMMDSource

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanSourceFeatureRaw
open UEOT.V3.HilbertMeanSourceRadius
open UEOT.V3.MMDTransport

universe uY uH

variable {Y : Type uY} {H : Type uH}
variable [MeasurableSpace Y]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- One iid RKHS/source channel satisfies the exact frozen P-STAT-06 radius. -/
theorem source_featureMMD_tail_exact_radius
    [BorelSpace H] [StandardBorelSpace H] [CompleteSpace H]
    [MeasurableAdd₂ H] [MeasurableSub H] [Nonempty H]
    {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (P : Measure Y) [IsProbabilityMeasure P]
    (φ : Y → H) (hφ : Measurable φ)
    (hInt : Integrable φ P)
    (hunit : ∀ᵐ y ∂P, ‖φ y‖ ≤ 1) :
    (Measure.pi (fun _ : Fin N => P)).real
      {y : Fin N → Y |
        pStat06SourceRadius N L alpha ≤
          ‖empiricalMean (fun i => φ (y i)) - meanEmbedding φ P‖}
      ≤ alpha / (L : ℝ) := by
  have hmeanUnit : ‖meanEmbedding φ P‖ ≤ 1 := by
    unfold meanEmbedding
    simpa using (norm_integral_le_of_norm_le_const (μ := P) hunit)
  let ν : Fin N → Measure Y := fun _ => P
  have hraw := source_feature_tail_exact_radius_raw_assumptions
    (Y := Y) (H := H)
    hN hL halpha0 halpha1 ν φ hφ (meanEmbedding φ P) hmeanUnit
    (fun _ => by simpa [ν] using hInt)
    (fun _ => by rfl)
    (fun _ => by simpa [ν] using hunit)
  simpa [ν, Function.comp_def] using hraw

end UEOT.V3.HilbertMeanMMDSource
