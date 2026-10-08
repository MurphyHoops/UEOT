import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCLinearPredictiveLift
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCStochasticBeliefBridge
import Mathlib.Tactic

/-!
# Temporal-semantic audit: emission before versus after action

`controlledOutputTrace` emits `read(currentState)` and then evolves. The
already-existing `FiniteBayesBelief.observationLaw` applies the action first,
then observes the next state. Neither can be substituted for the other
without an explicit time-shift / observation-timing bridge theorem.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.FiniteBayesBelief

universe uX uA uO

/-- One observable symbol of the trace records the current-state emission. -/
theorem one_word_trace_is_pre_transition_observation
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (x : X) (a : A) (o : O) :
    controlledOutputTrace K read x [(a, o)] =
      (if read x = o then 1 else 0) := by
  by_cases h : read x = o
  · simp [controlledOutputTrace, h, K.normalized]
  · simp [controlledOutputTrace, h]

/-- A point mass is a valid normalized latent-state belief. -/
noncomputable def pointSourceBelief {X : Type uX} [Fintype X] (x : X) :
    Belief Unit X := by
  classical
  refine {
    mass := fun _ y => if y = x then 1 else 0
    nonneg := ?_
    sum_one := ?_
  }
  · intro theta y
    split_ifs <;> norm_num
  · simp

/-- The existing Bayes observation pipeline instead registers the emission
after the controlled transition. Its exact evidence expression is the sum
of transition mass times next-state emission, for point-source beliefs. -/
theorem point_belief_observes_post_transition
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (x : X) (a : A) (o : O) :
    (observationLaw (finiteKernelToBeliefModel K read)
        (pointSourceBelief x) a).mass o =
      ∑ y, K.mass x a y * (if read y = o then (1 : ℝ) else 0) := by
  classical
  simp [observationLaw, evidence, jointObservationMass, nextMass,
    finiteKernelToBeliefModel, pointSourceBelief, mul_comm, mul_left_comm,
    mul_assoc]

/-- A normalized two-state chain where the only action flips the state. -/
def flipObservationKernel : FiniteControlledStochasticKernel Bool Unit where
  mass := fun x _ y => if y = !x then 1 else 0
  nonneg := by
    intro x a y
    split_ifs <;> norm_num
  normalized := by
    intro x a
    cases x <;> norm_num

/-- Same micro-kernel and same `read`, yet pre- and post-transition one-step
observation protocols predict opposite outcomes. An explicit timing map is
therefore a necessary bridge when composing trace laws with a Bayes filter. -/
theorem pre_and_post_emission_are_not_interchangeable :
    controlledOutputTrace flipObservationKernel id false [((), false)] = 1 ∧
    (observationLaw
      (finiteKernelToBeliefModel flipObservationKernel id)
      (pointSourceBelief false) ()).mass false = 0 := by
  constructor
  · rw [one_word_trace_is_pre_transition_observation]
    rfl
  · rw [point_belief_observes_post_transition]
    norm_num [flipObservationKernel, Fintype.sum_bool]

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
