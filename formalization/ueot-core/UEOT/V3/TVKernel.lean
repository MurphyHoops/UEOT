import UEOT.V3.TVSpan
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Integral

/-!
# P-MET-01 — Markov-kernel total-variation contraction

This module closes the second data-processing clause of P-MET-01:
post-processing two probability measures through the same Markov kernel
cannot increase the event-supremum total-variation distance defined in
`UEOT.V3.TotalVariation`.
-/

namespace UEOT.V3.TVKernel

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe uX uY
variable {X : Type uX} {Y : Type uY}
variable [MeasurableSpace X] [MeasurableSpace Y]

theorem comp_measureReal_eq_integral
    (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (B : Set Y) (hB : MeasurableSet B) :
    (κ ∘ₘ μ).real B = ∫ x, (κ x).real B ∂μ := by
  rw [measureReal_def, Measure.bind_apply hB κ.aemeasurable]
  simp_rw [measureReal_def]
  symm
  exact integral_toReal
    (κ.measurable_coe hB).aemeasurable
    (ae_of_all μ fun x => measure_lt_top (κ x) B)

theorem tvDist_comp_le
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    UEOT.V3.TotalVariation.tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤
      UEOT.V3.TotalVariation.tvDist μ ν := by
  change sSup
      (UEOT.V3.TotalVariation.tvEventSet (κ ∘ₘ μ) (κ ∘ₘ ν)) ≤
    UEOT.V3.TotalVariation.tvDist μ ν
  refine csSup_le
    (UEOT.V3.TotalVariation.tvEventSet_nonempty (κ ∘ₘ μ) (κ ∘ₘ ν)) ?_
  intro r hr
  rcases hr with ⟨B, hB, rfl⟩
  let g : X → ℝ := fun x => (κ x).real B
  have hg : Measurable g := (κ.measurable_coe hB).ennreal_toReal
  have h0 : ∀ x, (0 : ℝ) ≤ g x := fun _ => measureReal_nonneg
  have h1 : ∀ x, g x ≤ (1 : ℝ) := fun _ => measureReal_le_one
  have hspan :=
    UEOT.V3.TVSpan.abs_integral_sub_le_span_tvDist
      μ ν g hg 0 1 (by norm_num) h0 h1
  rw [comp_measureReal_eq_integral μ κ B hB,
      comp_measureReal_eq_integral ν κ B hB]
  simpa using hspan

end UEOT.V3.TVKernel
