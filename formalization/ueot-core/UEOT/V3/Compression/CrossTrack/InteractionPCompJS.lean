import UEOT.V3.Compression.CrossTrack.InteractionBindingIsolation
import UEOT.V3.CompositionInterventionJS

/-!
# Interaction identifiability from P-COMP-02 JS separation

P-COMP-02 already proves that Jensen--Shannon divergence vanishes exactly when
the compared response laws are equal.  Therefore a finite probe family that
has positive JS separation for every distinct assembly pair automatically
generates positive interaction binding isolation.
-/

namespace UEOT.V3.Compression.CrossTrack

open MeasureTheory
open UEOT.V3
open UEOT.V3.CompositionInterventionJS

universe uA uI uY

noncomputable section

variable {A : Type uA} {I : Type uI} {Y : Type uY}
variable [MeasurableSpace Y]

/-- Every distinct parent-assembly pair can be separated by at least one
selected probe with strictly positive Jensen--Shannon divergence. -/
def PairwiseJSSeparating
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) : Prop :=
  ∀ ⦃a b : A⦄, a ≠ b →
    ∃ i ∈ probes, 0 < jsDiv (F.response a i) (F.response b i)

theorem pairwiseInteractionSeparating_of_pairwiseJS
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I)
    (hjs : PairwiseJSSeparating F probes) :
    PairwiseInteractionSeparating F probes := by
  intro a b hab
  rcases hjs hab with ⟨i, hi, hpos⟩
  refine ⟨i, hi, ?_⟩
  intro heq
  let _ : IsProbabilityMeasure (F.response a i) := F.probability a i
  let _ : IsProbabilityMeasure (F.response b i) := F.probability b i
  have hzero : jsDiv (F.response a i) (F.response b i) = 0 :=
    (jsDiv_eq_zero_iff _ _).2 heq
  exact (ne_of_gt hpos) hzero

variable [Fintype A] [Nontrivial A] [MetricSpace A]

/-- **P-COMP-02 -> positive interaction isolation.**

Strict JS distinguishability under a finite nonempty intervention family is a
source-facing sufficient condition for positive canonical binding isolation. -/
theorem interactionIsolationConorm_pos_of_pairwiseJS
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (hjs : PairwiseJSSeparating F probes) :
    0 < interactionIsolationConorm F probes hprobes := by
  exact
    (interactionIsolationConorm_pos_iff_pairwiseSeparating F probes hprobes).2
      (pairwiseInteractionSeparating_of_pairwiseJS F probes hjs)

end

end UEOT.V3.Compression.CrossTrack
