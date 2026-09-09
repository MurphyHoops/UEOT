import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-!
# P-MET-01 / P-MET-02 foundation — source total variation

This module starts from the source definition

  D_TV(μ,ν) = sup { |μ(A)-ν(A)| : A measurable }.

The first completed layer proves deterministic measurable data processing:
a measurable readout cannot increase total variation.

The stronger Markov-kernel contraction and the span/expectation inequality are
kept as separate obligations; this file must not be used to claim all of
P-MET-01 or P-MET-02 until those layers are machine checked.
-/

namespace UEOT.V3.TotalVariation

open MeasureTheory

universe uX uY

variable {X : Type uX} {Y : Type uY}
variable [MeasurableSpace X] [MeasurableSpace Y]

def tvEventSet (μ ν : Measure X) : Set ℝ :=
  {r | ∃ A : Set X, MeasurableSet A ∧
      r = |μ.real A - ν.real A|}

noncomputable def tvDist (μ ν : Measure X) : ℝ :=
  sSup (tvEventSet μ ν)

theorem tvEventSet_nonempty (μ ν : Measure X) :
    (tvEventSet μ ν).Nonempty := by
  refine ⟨0, ∅, MeasurableSet.empty, ?_⟩
  simp

theorem tvEventSet_bddAbove
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove (tvEventSet μ ν) := by
  refine ⟨1, ?_⟩
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  have hμ0 : 0 ≤ μ.real A := measureReal_nonneg
  have hν0 : 0 ≤ ν.real A := measureReal_nonneg
  have hμ1 : μ.real A ≤ 1 := measureReal_le_one
  have hν1 : ν.real A ≤ 1 := measureReal_le_one
  rw [abs_le]
  constructor <;> linarith

theorem tvEvent_le
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set X) (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ tvDist μ ν := by
  unfold tvDist
  exact le_csSup (tvEventSet_bddAbove μ ν) ⟨A, hA, rfl⟩

theorem tvDist_nonneg
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ tvDist μ ν := by
  have h := tvEvent_le μ ν (∅ : Set X) MeasurableSet.empty
  simpa using h

theorem tvDist_le_one
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ 1 := by
  unfold tvDist
  refine csSup_le (tvEventSet_nonempty μ ν) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  have hμ0 : 0 ≤ μ.real A := measureReal_nonneg
  have hν0 : 0 ≤ ν.real A := measureReal_nonneg
  have hμ1 : μ.real A ≤ 1 := measureReal_le_one
  have hν1 : ν.real A ≤ 1 := measureReal_le_one
  rw [abs_le]
  constructor <;> linarith

theorem tvDist_map_le
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → Y) (hf : Measurable f) :
    tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν := by
  change sSup (tvEventSet (μ.map f) (ν.map f)) ≤ tvDist μ ν
  refine csSup_le (tvEventSet_nonempty (μ.map f) (ν.map f)) ?_
  intro r hr
  rcases hr with ⟨B, hB, rfl⟩
  have hpre : MeasurableSet (f ⁻¹' B) := hf hB
  have hle := tvEvent_le μ ν (f ⁻¹' B) hpre
  simpa [measureReal_def, Measure.map_apply hf hB] using hle

end UEOT.V3.TotalVariation
