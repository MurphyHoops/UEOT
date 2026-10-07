import UEOT.V3.Compression.CrossTrack.DualIsolationPMetRealization

/-!
# Scientific Closure C3 — parent-binding calibration benchmark

The generic parent-binding constant is domain data.  A reusable positive
mechanism is already canonical in Track X: common Markov realization plus TV
metric domination derives the sharp nonexpansive constant `L = 1` by data
processing.  C3 exposes that mechanism as the binding-calibration benchmark;
it does not claim every parent realization factors this way.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure

open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.CrossTrack

universe uP uA uX uS

noncomputable section

variable {P : Type uP} {A : Type uA} [PseudoMetricSpace A]
variable {X : Type uX} [MeasurableSpace X]
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance c3BindingDecidableEqS : DecidableEq S :=
  Classical.decEq S

/-- **C3-04 positive calibration benchmark.**  The full rowwise binding bound
and its constant are consequences of the independently checkable common-channel
realization certificate. -/
theorem commonMarkov_calibrates_parentBinding
    (repr : P → A)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (real : CommonMarkovParentRealization X repr K hK) :
    (real.toParentBinding repr K hK).L = 1 ∧
      ∀ p q x,
        crossRowTV (K p) (hK p) (K q) (hK q) x ≤
          dist (repr p) (repr q) := by
  refine ⟨rfl, ?_⟩
  intro p q x
  exact real.rowTV_le_assemblyDist repr K hK p q x

end

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure
