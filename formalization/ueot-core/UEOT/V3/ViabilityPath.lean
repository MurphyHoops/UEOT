import UEOT.V3.ViabilityKernel
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# P-PER-03 path event bridge

The finite viability recursion already supplies a stationary policy whose every
finite-time state marginal assigns probability one to the fixed kernel.  This
module isolates the standard measure-theoretic bridge needed by the source:
countably many measurable coordinate-safety events, each of probability one,
have a probability-one intersection.

This does not construct a path law.  Existence/consistency of the controlled
path measure remains a separate process-theory obligation; once such a path law
has the verified finite-time marginals, the theorem below gives the exact
"never exits at any discrete time" event.
-/

namespace UEOT.V3.ViabilityPath

open Set MeasureTheory

universe uOmega

variable {Ω : Type uOmega} [MeasurableSpace Ω]

/-- Countable probability-one intersection.  This is the exact generic bridge
from all finite-time safety events to the all-time nonexit event. -/
theorem measure_iInter_eq_one_of_measure_eq_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n))
    (hone : ∀ n, μ (A n) = 1) :
    μ (⋂ n, A n) = 1 := by
  have hmeas : MeasurableSet (⋂ n, A n) :=
    MeasurableSet.iInter hA
  apply (prob_compl_eq_zero_iff hmeas).mp
  rw [compl_iInter, measure_iUnion_null_iff]
  intro n
  exact (prob_compl_eq_zero_iff (hA n)).mpr (hone n)

/-- A coordinate formulation convenient for a discrete-time path law.  The
coordinate maps are kept abstract here so the lemma works for any process-space
construction used by the v3 process layer. -/
theorem all_times_safe_eq_one
    {X : Type*} [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → X)
    (K : Set X) (hK : MeasurableSet K)
    (hXn : ∀ n, Measurable (Xn n))
    (hone : ∀ n, μ {ω | Xn n ω ∈ K} = 1) :
    μ {ω | ∀ n, Xn n ω ∈ K} = 1 := by
  let A : ℕ → Set Ω := fun n => {ω | Xn n ω ∈ K}
  have hA : ∀ n, MeasurableSet (A n) := by
    intro n
    exact hK.preimage (hXn n)
  have hi : (⋂ n, A n) = {ω | ∀ n, Xn n ω ∈ K} := by
    ext ω
    simp [A]
  rw [← hi]
  exact measure_iInter_eq_one_of_measure_eq_one μ A hA hone

end UEOT.V3.ViabilityPath
