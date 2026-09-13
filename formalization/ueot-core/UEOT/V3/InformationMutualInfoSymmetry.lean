import UEOT.V3.InformationStatistic
import UEOT.V3.InformationMemoryBound
import Mathlib.MeasureTheory.Measure.Prod

/-!
# P-INFO-03 — mutual-information symmetry under coordinate swap

The zero-distortion achievability proof uses a countable core `C` as the second
coordinate of a conditional law on `H × C`, while the existing entropy upper
bound is stated for a countable first coordinate.  This module closes that
orientation gap by proving directly from the KL definition that swapping the
two coordinates preserves mutual information.
-/

namespace UEOT.V3.InformationMutualInfoSymmetry

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationCore
open UEOT.V3.InformationStatistic
open UEOT.V3.InformationDiscreteEntropy
open UEOT.V3.InformationMemoryBound

universe uX uY

variable {X : Type uX} {Y : Type uY}
variable [MeasurableSpace X] [MeasurableSpace Y]

lemma map_swap_fst
    (μ : Measure (X × Y)) :
    (μ.map Prod.swap).fst = μ.snd := by
  unfold Measure.fst Measure.snd
  rw [Measure.map_map measurable_fst measurable_swap]
  apply Measure.map_congr
  filter_upwards with z
  rfl

lemma map_swap_snd
    (μ : Measure (X × Y)) :
    (μ.map Prod.swap).snd = μ.fst := by
  unfold Measure.fst Measure.snd
  rw [Measure.map_map measurable_snd measurable_swap]
  apply Measure.map_congr
  filter_upwards with z
  rfl

/-- Mutual information is invariant under exchanging the two coordinates. -/
theorem mutualInfo_map_swap
    (μ : Measure (X × Y)) [IsProbabilityMeasure μ] :
    mutualInfo (μ.map Prod.swap) = mutualInfo μ := by
  unfold mutualInfo
  rw [map_swap_fst μ, map_swap_snd μ]
  rw [← Measure.prod_swap]
  exact klDiv_map_eq_of_measurable_leftInverse
    μ (μ.fst.prod μ.snd)
    Prod.swap Prod.swap
    measurable_swap measurable_swap
    (by intro z; cases z; rfl)

/-- Entropy upper bound for a countable **second** coordinate.  This is the
coordinate-swapped form of UEOT's already machine-checked bound
`I(C;X) ≤ H(C)`. -/
theorem mutualInfo_le_discreteShannonEntropy_snd
    [Countable Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace X] [Nonempty X]
    (μ : Measure (X × Y)) [IsProbabilityMeasure μ] :
    mutualInfo μ ≤ discreteShannonEntropy μ.snd := by
  letI : IsProbabilityMeasure (μ.map Prod.swap) :=
    (Measure.isProbabilityMeasure_map_iff measurable_swap.aemeasurable).2 inferInstance
  have h := mutualInfo_le_discreteShannonEntropy (μ.map Prod.swap)
  rw [mutualInfo_map_swap μ, map_swap_fst μ] at h
  exact h

end

end UEOT.V3.InformationMutualInfoSymmetry
