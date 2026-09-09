import UEOT.V3.TotalVariation
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# P-MET-01 / P-MET-02 — signed-measure bridge

This module connects the source event-supremum definition of total variation
used by UEOT to Mathlib's signed/vector measure infrastructure.

No P-ID promotion is claimed here.  The eventual target is to identify the
probability-measure TV distance with one half of the variation mass of
`μ.toSignedMeasure - ν.toSignedMeasure`, then reuse Mathlib's variation
integral bounds.
-/

namespace UEOT.V3.VariationBridge

open MeasureTheory

universe uX

variable {X : Type uX} [MeasurableSpace X]

noncomputable def signedDiff
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    SignedMeasure X :=
  μ.toSignedMeasure - ν.toSignedMeasure

theorem signedDiff_apply
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Set X) (hA : MeasurableSet A) :
    signedDiff μ ν A = μ.real A - ν.real A := by
  unfold signedDiff
  exact Measure.toSignedMeasure_sub_apply hA

theorem abs_signedDiff_apply_eq_tvEvent
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Set X) (hA : MeasurableSet A) :
    |signedDiff μ ν A| = |μ.real A - ν.real A| := by
  rw [signedDiff_apply μ ν A hA]

theorem signedDiff_univ_eq_zero
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    signedDiff μ ν Set.univ = 0 := by
  rw [signedDiff_apply μ ν Set.univ MeasurableSet.univ]
  simp

theorem tvEvent_le_norm_signedDiff
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set X) (hA : MeasurableSet A) :
    |signedDiff μ ν A| ≤ UEOT.V3.TotalVariation.tvDist μ ν := by
  simpa [abs_signedDiff_apply_eq_tvEvent μ ν A hA] using
    UEOT.V3.TotalVariation.tvEvent_le μ ν A hA

end UEOT.V3.VariationBridge
