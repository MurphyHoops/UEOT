import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeterministicDiracPredictiveBridge
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCStochasticPredictiveIntertwining
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCObservationOrderBridge
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCStochasticTraceNoGo
import Mathlib.Tactic

/-!
# UMC-01.2 — same-source Dirac belief lift and timing guard

No Markov transition is claimed on arbitrary microstate predictive equivalence
classes. The event-updated unnormalized belief always has a lawful
predictive recursion. Its action/observation semantics is explicitly
PRE-action; the P-REF-02 observer's law is POST-action and is linked only
via the existing clock-shift theorem. The general stochastic six-state
nonlumpability countermodel is preserved.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.FiniteBayesBelief

universe uX uA uO

/-- An explicit update equation for the stochastic belief produced by
the very same deterministic world step, not a separately assumed kernel. -/
theorem dirac_belief_event_update_exact
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O] [DecidableEq X]
    (step : X → A → X) (read : X → O)
    (b : X → ℝ) (a : A) (o : O) (y : X) :
    beliefUnnormalizedEventStep (diracControlledKernel step) read b a o y =
      ∑ x : X, b x *
        (if read x = o then
          (if y = step x a then (1 : ℝ) else 0) else 0) := by
  classical
  unfold beliefUnnormalizedEventStep
  apply Finset.sum_congr rfl
  intro x _
  rw [dirac_kernel_mass_exact]

/-- The exact all-future recursive belief identity now holds for the
kernel constructed from a SINGLE deterministic process. This does not
supply any Bayesian *normalization* on a zero-evidence event. -/
theorem dirac_belief_future_intertwining
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (step : X → A → X) (read : X → O)
    (b : X → ℝ) (a : A) (o : O) (word : List (A × O)) :
    beliefFutureResponse (diracControlledKernel step) read
      (beliefUnnormalizedEventStep
        (diracControlledKernel step) read b a o) word =
    beliefFutureResponse (diracControlledKernel step) read b ((a,o)::word) :=
  belief_event_update_intertwines_future_response
    (diracControlledKernel step) read b a o word

/-- The P-REF-02 *post-action* observation is a properly shifted
current-state pre-action emission, not the original unshifted trace. -/
theorem dirac_post_observation_requires_time_shift
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq O]
    (step : X → A → X) (read : X → O)
    (x : X) (a dummyAction : A) (o : O) :
    (observationLaw
      (finiteKernelToBeliefModel (diracControlledKernel step) read)
      (pointSourceBelief x) a).mass o =
    shiftedPreTraceOne (diracControlledKernel step) read
      x a dummyAction o :=
  bayes_post_observation_eq_shifted_pre_trace
    (diracControlledKernel step) read x a dummyAction o

/-- No blanket stochastic extension: a separately normalized 6-state
process has full trace observational equality and *no* stochastic
kernel on those microscopic predictive equivalence classes. -/
theorem unrestricted_stochastic_trace_lumping_is_false :
    ¬ StrongLumpability traceCounterexampleKernel stochasticOutputTrace :=
  all_future_trace_equivalence_not_markov_lumpable

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
