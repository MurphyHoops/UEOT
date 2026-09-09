import UEOT.V3.TVSpan
import Mathlib.Probability.Kernel.Composition.CompNotation

/-!
# P-MET-01 — Markov-kernel contraction in total variation

This module completes the stochastic-channel half of the source statement

  D_TV(PK, QK) ≤ D_TV(P, Q)

for probability measures P,Q and a Markov kernel K.  The proof deliberately
reuses the source event-supremum TV definition and the already verified
P-MET-02 bounded-observable span estimate.
-/

namespace UEOT.V3.TVKernel

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe uX uY

variable {X : Type uX} {Y : Type uY}
variable [MeasurableSpace X] [MeasurableSpace Y]

theorem comp_real_apply_eq_integral
    (μ : Measure X) [IsProbabilityMeasure μ]
    (K : Kernel X Y) [IsMarkovKernel K]
    (B : Set Y) (hB : MeasurableSet B) :
    (K ∘ₘ μ).real B = ∫ x, (K x B).toReal ∂μ := by
  rw [measureReal_def, Measure.bind_apply hB K.aemeasurable]
  symm
  rw [integral_toReal (Kernel.measurable_coe K hB).aemeasurable]
  filter_upwards with x
  exact measure_lt_top (K x) B

theorem tvDist_comp_le
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Kernel X Y) [IsMarkovKernel K] :
    UEOT.V3.TotalVariation.tvDist (K ∘ₘ μ) (K ∘ₘ ν) ≤
      UEOT.V3.TotalVariation.tvDist μ ν := by
  letI : IsProbabilityMeasure (K ∘ₘ μ) := by infer_instance
  letI : IsProbabilityMeasure (K ∘ₘ ν) := by infer_instance
  unfold UEOT.V3.TotalVariation.tvDist
  refine csSup_le
    (UEOT.V3.TotalVariation.tvEventSet_nonempty (K ∘ₘ μ) (K ∘ₘ ν)) ?_
  intro r hr
  rcases hr with ⟨B, hB, rfl⟩
  rw [comp_real_apply_eq_integral μ K B hB,
      comp_real_apply_eq_integral ν K B hB]
  have hspan :=
    UEOT.V3.TVSpan.abs_integral_sub_le_span_tvDist
      μ ν
      (fun x => (K x B).toReal)
      (ENNReal.measurable_toReal.comp (Kernel.measurable_coe K hB))
      0 1 zero_le_one
      (fun x => ENNReal.toReal_nonneg)
      (fun x => by
        have hle : (K x).real B ≤ 1 := measureReal_le_one
        simpa [measureReal_def] using hle)
  simpa using hspan

end UEOT.V3.TVKernel
