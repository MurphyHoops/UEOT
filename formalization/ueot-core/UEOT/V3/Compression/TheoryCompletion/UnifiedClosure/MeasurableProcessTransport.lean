import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BeliefTimingBoundary
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TwoStageFormationTransport
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic

/-!
# UMC-06 — nonfinite measurable deterministic source/quotient square

For arbitrary measurable state spaces, an already established measurable
semiconjugacy of a deterministic process implies a commuting square of
pushforward measures. This theorem is nonfinite, while the measurability
and pointwise closure requirements remain explicit assumptions.

It does NOT construct general regular conditional probabilities, nor
give arbitrary stochastic Markov lumpability, temporally dependent
concentration, physical identities or unknown program sources.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open MeasureTheory
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uX uQ uA

/-- Same-source microscopic/coarse transitions commute for ALL measures
once actual measurable semiconjugacy has been proved on source states. -/
theorem measurable_process_quotient_pushforward_commutes
    {X : Type uX} {Q : Type uQ} {A : Type uA}
    [MeasurableSpace X] [MeasurableSpace Q]
    (step : X → A → X) (q : X → Q) (update : Q → A → Q)
    (hstep : ∀ a, Measurable (fun x => step x a))
    (hq : Measurable q)
    (hupdate : ∀ a, Measurable (fun z => update z a))
    (hcomm : ∀ x a, q (step x a) = update (q x) a)
    (μ : Measure X) (a : A) :
    Measure.map q (Measure.map (fun x => step x a) μ) =
      Measure.map (fun z => update z a) (Measure.map q μ) := by
  calc
    Measure.map q (Measure.map (fun x => step x a) μ) =
        Measure.map (q ∘ fun x => step x a) μ := by
          rw [Measure.map_map hq (hstep a)]
    _ = Measure.map ((fun z => update z a) ∘ q) μ := by
      congr 1
      funext x
      exact hcomm x a
    _ = Measure.map (fun z => update z a) (Measure.map q μ) := by
      rw [Measure.map_map (hupdate a) hq]

/-- A source Dirac point mass also transports exactly under the specified
coarse deterministic update, without claiming unique physical identity. -/
theorem measurable_quotient_dirac_transition
    {X : Type uX} {Q : Type uQ} {A : Type uA}
    [MeasurableSpace X] [MeasurableSpace Q]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Q]
    (step : X → A → X) (q : X → Q) (update : Q → A → Q)
    (hcomm : ∀ x a, q (step x a) = update (q x) a)
    (x : X) (a : A) :
    Measure.map q (Measure.dirac (step x a)) =
      Measure.dirac (update (q x) a) := by
  rw [Measure.map_dirac]
  exact congrArg Measure.dirac (hcomm x a)

/-- The arbitrary stochastic trace-quotient analogue is explicitly
excluded by the previously proven six-state model. -/
theorem generic_stochastic_trace_quotient_cannot_be_forced :
    ¬ StrongLumpability traceCounterexampleKernel stochasticOutputTrace :=
  unrestricted_stochastic_trace_lumping_is_false

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
