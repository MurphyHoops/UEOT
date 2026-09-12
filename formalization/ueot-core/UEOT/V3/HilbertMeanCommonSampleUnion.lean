import UEOT.V3.HilbertMeanUnion
import UEOT.V3.HilbertMeanFeatureProductBridge
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# P-STAT-06 — common-sample simultaneous union transport

This module keeps the finite-family union on one common raw probability space.
Each channel may use its own measure-preserving feature-product map and its own
target bad event. The bad event is pulled back to the shared raw sample law,
and only then is the finite union bound applied.
-/

namespace UEOT.V3.HilbertMeanCommonSampleUnion

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanUnion

universe uΩ uΞ

variable {Ω : Type uΩ} {Ξ : Type uΞ}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ]

/-- A measure-preserving map preserves the real-valued probability of any
null-measurable target event after pullback. -/
theorem measureReal_preimage_eq_of_measurePreserving
    (μ : Measure Ω) (ν : Measure Ξ) (f : Ω → Ξ)
    (hf : MeasurePreserving f μ ν)
    (s : Set Ξ) (hs : NullMeasurableSet s ν) :
    μ.real (f ⁻¹' s) = ν.real s := by
  exact congrArg ENNReal.toReal (hf.measure_preimage hs)

/-- Common-sample finite-family union bound. Each channel can have a different
target probability space and map, but all pulled-back bad events live on the
same raw measure `μ`. -/
theorem measure_exists_preimage_bad_le_alpha
    {L : ℕ} (hL : 0 < L)
    (μ : Measure Ω)
    (ν : Fin L → Measure Ξ)
    (f : Fin L → Ω → Ξ)
    (bad : Fin L → Set Ξ)
    (alpha : ℝ)
    (hpres : ∀ j, MeasurePreserving (f j) μ (ν j))
    (hbad : ∀ j, NullMeasurableSet (bad j) (ν j))
    (h_each : ∀ j, (ν j).real (bad j) ≤ alpha / (L : ℝ)) :
    μ.real (⋃ j : Fin L, f j ⁻¹' bad j) ≤ alpha := by
  apply measure_exists_bad_le_alpha hL μ (fun j => f j ⁻¹' bad j) alpha
  intro j
  rw [measureReal_preimage_eq_of_measurePreserving μ (ν j) (f j)
    (hpres j) (bad j) (hbad j)]
  exact h_each j

end UEOT.V3.HilbertMeanCommonSampleUnion
