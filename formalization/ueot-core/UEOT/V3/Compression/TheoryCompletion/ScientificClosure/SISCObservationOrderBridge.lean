import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCEmissionTiming
import Mathlib.Tactic

/-!
# SISC N2 — exact, typed time shift between action-observation conventions

The predictive word function `controlledOutputTrace` emits the current
observation before applying its declared action. P-REF-02 instead performs
the action and then emits from the new state. This module gives a concrete
clock-alignment theorem rather than treating equal K/read inputs as proof
of identical observation semantics.

The final current-state read is reached via a one-symbol pre-action trace
whose action argument is an arbitrary *dummy* action, since there is no
observation after that action. This is a one-step bridge only: n-step belief
recursion is a distinct theorem target.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.FiniteBayesBelief

universe uX uA uO

/-- Next-state pre-action readout, averaged using the action which precedes it. -/
noncomputable def shiftedPreTraceOne
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (x : X) (a : A) (dummyAction : A) (o : O) : ℝ :=
  ∑ y : X, K.mass x a y *
    controlledOutputTrace K read y [(dummyAction, o)]

/-- The correct one-time-step index alignment:
the Core belief model's post-action observation is exactly the
transition-weighted *next-state* pre-action trace, for a point-source belief.
The dummy action has no influence on the one-symbol pre-action output. -/
theorem bayes_post_observation_eq_shifted_pre_trace
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (x : X) (a : A) (dummyAction : A) (o : O) :
    (observationLaw (finiteKernelToBeliefModel K read)
      (pointSourceBelief x) a).mass o =
      shiftedPreTraceOne K read x a dummyAction o := by
  rw [point_belief_observes_post_transition]
  unfold shiftedPreTraceOne
  apply Finset.sum_congr rfl
  intro y _
  rw [one_word_trace_is_pre_transition_observation]

/-- A dummy action cannot affect the output which is observed *before* it. -/
theorem shifted_pre_trace_dummy_action_invariant
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (x : X) (a dummyA dummyB : A) (o : O) :
    shiftedPreTraceOne K read x a dummyA o =
      shiftedPreTraceOne K read x a dummyB o := by
  unfold shiftedPreTraceOne
  apply Finset.sum_congr rfl
  intro y _
  rw [one_word_trace_is_pre_transition_observation,
    one_word_trace_is_pre_transition_observation]

/-- The counterexample which prompted the guard has a consistent *shifted*
interpretation: the post-action false-output probability is the next-state
pre-action trace mixture, and both are zero in the two-state flip model. -/
theorem flip_post_matches_shifted_pre :
    shiftedPreTraceOne flipObservationKernel id false () () false = 0 := by
  rw [← bayes_post_observation_eq_shifted_pre_trace]
  exact pre_and_post_emission_are_not_interchangeable.2

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
