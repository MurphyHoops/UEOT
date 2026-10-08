import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCStochasticTraceNoGo
import UEOT.V3.FiniteBayesBelief
import Mathlib.Tactic

/-!
# SISC N1.5: Bayesian belief-state closure when raw predictive quotient fails

A state quotient based only on observed future-output words need not carry a
Markov kernel, even for a finite hidden Markov model (see the exact six-state
no-go). This does NOT mean no predictive controlled state exists: a normalized
belief over hidden states has a mathematically closed one-step Bayes filter
provided the finite transition and emission models are supplied.

This bridge instantiates the pre-existing P-REF-02 finite belief module from
the same `FiniteControlledStochasticKernel` used by N1. No new Bayes axiom,
external objective, physical object identity, or model-learning assumption.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.FiniteBayesBelief

universe uX uA uO

/-- An exact finite hidden-state Markov kernel with deterministic readout is
already a legitimate finite Bayes model, with a trivial latent parameter. -/
noncomputable def finiteKernelToBeliefModel
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O) :
    UEOT.V3.FiniteBayesBelief.Model Unit X A O := by
  classical
  refine {
    transition := fun _ x a y => K.mass x a y
    observation := fun _ y _ o => if read y = o then 1 else 0
    transition_nonneg := fun _ x a y => K.nonneg x a y
    transition_sum_one := fun _ x a => K.normalized x a
    observation_nonneg := ?_
    observation_sum_one := ?_
  }
  · intro theta x a y
    split_ifs <;> norm_num
  · intro theta x a
    simp

/-- Bayes prediction under the same microscopic kernel gives a properly
normalized one-step output law for *every* normalized source belief. -/
theorem lifted_belief_observation_is_normalized
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype O]
    (K : FiniteControlledStochasticKernel X A)
    (read : X → O)
    (belief : Belief Unit X) (action : A) :
    ∑ output : O,
      (observationLaw (finiteKernelToBeliefModel K read) belief action).mass output = 1 :=
  (observationLaw (finiteKernelToBeliefModel K read) belief action).sum_one

/-- The belief update signals a model conflict exactly for impossible
evidence; there is no silent division by a zero-likelihood event. -/
theorem lifted_belief_update_conflict_iff_zero
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (belief : Belief Unit X) (action : A) (output : O) :
    updateResult (finiteKernelToBeliefModel K read) belief action output =
      .modelConflict ↔
    (observationLaw (finiteKernelToBeliefModel K read) belief action).mass output = 0 := by
  exact (beliefStep (finiteKernelToBeliefModel K read) belief action).conflict_iff_zero output

/-- A single concrete system simultaneously defeats a naive output-trace
Markov quotient AND supports a normalized, well-typed belief-state prediction.
This is the precise boundary, not a contradiction between P-ALG and P-REF. -/
theorem trace_noGo_but_belief_filter_well_defined :
    (¬ StrongLumpability traceCounterexampleKernel stochasticOutputTrace) ∧
    ∀ belief : Belief Unit (Fin 6),
      ∑ output : Bool,
        (observationLaw
          (finiteKernelToBeliefModel traceCounterexampleKernel
            (fun i : Fin 6 => decide (i = 5)))
          belief ()).mass output = 1 := by
  exact ⟨all_future_trace_equivalence_not_markov_lumpable,
    fun belief => lifted_belief_observation_is_normalized
      traceCounterexampleKernel (fun i : Fin 6 => decide (i = 5)) belief ()⟩

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
