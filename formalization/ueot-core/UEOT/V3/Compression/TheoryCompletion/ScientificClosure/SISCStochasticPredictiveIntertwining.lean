import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCLinearPredictiveLift
import UEOT.V3.Compression.RecursiveSufficientState
import Mathlib.Tactic

/-!
# N2 — exact intertwinement of finite unnormalized beliefs and future predictions

The microstate trace quotient need not be Markov lumpable, as the exact
six-state counterexample shows. Instead lift to the complete finite
*unnormalized belief vector* and then quotient beliefs by equality of
all action-observation future-word probabilities.

The observation is emitted BEFORE the declared action, consistently with
`controlledOutputTrace`. Normalized filtering and zero-evidence conflict
are separate obligations in the P-REF-02 Bayesian module.

Unlike quotienting microscopic tokens, the all-future quotient of
unnormalized beliefs automatically admits a unique event-recursive update.
This establishes the correct source type for the canonical stochastic
prediction-state construction without assuming strong lumpability.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.RecursiveSufficientState

universe uX uA uO

/-- A complete future-word response from a finite, possibly unnormalized or
signed, microscopic distribution. This is linear in the source weights. -/
noncomputable def beliefFutureResponse
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (b : X → ℝ) (w : List (A × O)) : ℝ :=
  ∑ x : X, b x * controlledOutputTrace K read x w

/-- A linear *unnormalized* forward update after observing o at the current
source state and executing a. A zero-likelihood observation yields the zero
vector, rather than silently dividing by zero. -/
noncomputable def beliefUnnormalizedEventStep
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (b : X → ℝ) (a : A) (o : O) (y : X) : ℝ :=
  ∑ x : X, b x * (if read x = o then K.mass x a y else 0)

/-- THE CENTRAL COMMUTING SQUARE: evolve the unnormalized belief under an
observed action-event and then predict w, or predict the event-prefixed word
directly from the original belief. Both are exactly the same function.

No strong lumpability premise appears; unlike microstate class transitions,
the lifted distributional state retains probabilities of hidden mixtures. -/
theorem belief_event_update_intertwines_future_response
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (b : X → ℝ) (a : A) (o : O) (w : List (A × O)) :
    beliefFutureResponse K read
      (beliefUnnormalizedEventStep K read b a o) w =
      beliefFutureResponse K read b ((a, o) :: w) := by
  classical
  unfold beliefFutureResponse beliefUnnormalizedEventStep
  calc
    (∑ y : X, (∑ x : X, b x *
        (if read x = o then K.mass x a y else 0)) *
        controlledOutputTrace K read y w) =
      ∑ y : X, ∑ x : X, b x *
        (if read x = o then K.mass x a y else 0) *
        controlledOutputTrace K read y w := by
          simp_rw [Finset.sum_mul]
    _ = ∑ x : X, ∑ y : X, b x *
        (if read x = o then K.mass x a y else 0) *
        controlledOutputTrace K read y w := Finset.sum_comm
    _ = ∑ x : X, b x * (∑ y : X,
        (if read x = o then K.mass x a y else 0) *
        controlledOutputTrace K read y w) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = ∑ x : X, b x * controlledOutputTrace K read x ((a,o)::w) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : read x = o
          · simp [controlledOutputTrace, h]
          · simp [controlledOutputTrace, h]

/-- The future-observation equivalence on *beliefs* is automatically stable
under each registered event, even if token-level future-trace equivalence is
NOT strongly lumpable. -/
theorem belief_future_equality_is_event_congruence
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (b c : X → ℝ)
    (h : beliefFutureResponse K read b = beliefFutureResponse K read c)
    (a : A) (o : O) :
    beliefFutureResponse K read
        (beliefUnnormalizedEventStep K read b a o) =
      beliefFutureResponse K read
        (beliefUnnormalizedEventStep K read c a o) := by
  funext w
  rw [belief_event_update_intertwines_future_response,
      belief_event_update_intertwines_future_response]
  exact congrFun h ((a, o) :: w)

/-- Consequently there exists a *unique* recursive event update on the
reachable canonical predictive belief classes. This conclusion was false for
the raw microscopic trace-law quotient in the six-state counterexample. -/
theorem unique_event_update_on_reachable_predictive_beliefs
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O) :
    ∃! update : ReachableState (beliefFutureResponse K read) →
        (A × O) → ReachableState (beliefFutureResponse K read),
      ∀ b a o, update (toReachable (beliefFutureResponse K read) b) (a,o) =
        toReachable (beliefFutureResponse K read)
          (beliefUnnormalizedEventStep K read b a o) := by
  obtain ⟨U, hU, huniq⟩ := existsUnique_reachableUpdate
    (beliefFutureResponse K read)
    (fun (b : X → ℝ) (ev : A × O) => toReachable (beliefFutureResponse K read)
      (beliefUnnormalizedEventStep K read b ev.1 ev.2))
    (by
      intro b c heq ev
      apply Subtype.ext
      exact belief_future_equality_is_event_congruence
        K read b c heq ev.1 ev.2)
  refine ⟨U, ?_, ?_⟩
  · intro b a o
    exact hU b (a,o)
  · intro V hV
    apply huniq V
    intro b ev
    exact hV b ev.1 ev.2

/-- The lifted belief update preserves nonnegativity when input weights are
nonnegative, independent of any quotient construction. -/
theorem belief_event_step_nonnegative
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (b : X → ℝ) (h : ∀ x, 0 ≤ b x)
    (a : A) (o : O) (y : X) :
    0 ≤ beliefUnnormalizedEventStep K read b a o y := by
  classical
  unfold beliefUnnormalizedEventStep
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (h x)
  split_ifs
  · exact K.nonneg x a y
  · exact le_refl 0

/-- The probability mass of the observed event under an unnormalized belief.
For a normalized nonnegative b, this is the pre-transition observation
likelihood; its definition makes the clock-order contract explicit. -/
noncomputable def preEventEvidence
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (b : X → ℝ) (a : A) (o : O) : ℝ :=
  ∑ y : X, beliefUnnormalizedEventStep K read b a o y

/-- The total unnormalized successor mass is precisely the probability of
observing the one-event word. This follows directly from the global
intertwining theorem with the empty future continuation. -/
theorem pre_event_evidence_eq_one_word_response
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (b : X → ℝ) (a : A) (o : O) :
    preEventEvidence K read b a o =
      beliefFutureResponse K read b [(a,o)] := by
  have h := belief_event_update_intertwines_future_response K read b a o []
  simpa [preEventEvidence, beliefFutureResponse, controlledOutputTrace] using h

/-- On *positive-evidence* events, Bayesian normalization is an exact
scaling of the same prefix-response law. With zero evidence we do not
make a fictitious normalized posterior; the unnormalized update remains
well-defined and is the zero-weight prediction when b is nonnegative. -/
theorem normalized_event_predictive_intertwining
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (b : X → ℝ) (a : A) (o : O) (w : List (A × O))
    (he : preEventEvidence K read b a o ≠ 0) :
    beliefFutureResponse K read
      (fun y => beliefUnnormalizedEventStep K read b a o y /
        preEventEvidence K read b a o) w =
      beliefFutureResponse K read b ((a,o)::w) /
        preEventEvidence K read b a o := by
  classical
  have hsum : (∑ y : X,
      beliefUnnormalizedEventStep K read b a o y *
        controlledOutputTrace K read y w) =
      beliefFutureResponse K read b ((a,o)::w) :=
    belief_event_update_intertwines_future_response K read b a o w
  change (∑ y : X, (beliefUnnormalizedEventStep K read b a o y /
    preEventEvidence K read b a o) * controlledOutputTrace K read y w) =
    beliefFutureResponse K read b ((a,o)::w) / preEventEvidence K read b a o
  calc
    (∑ y : X, (beliefUnnormalizedEventStep K read b a o y /
       preEventEvidence K read b a o) * controlledOutputTrace K read y w) =
      (∑ y : X, beliefUnnormalizedEventStep K read b a o y *
        controlledOutputTrace K read y w) / preEventEvidence K read b a o := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = _ := by rw [hsum]

/-- After a nonzero-evidence event, the reweighted response source sums to 1.
This is a normalization of numerical weights, *not* physical-object identity. -/
theorem normalized_event_mass_one
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (b : X → ℝ) (a : A) (o : O)
    (he : preEventEvidence K read b a o ≠ 0) :
    (∑ y : X, beliefUnnormalizedEventStep K read b a o y /
      preEventEvidence K read b a o) = 1 := by
  rw [← Finset.sum_div]
  change preEventEvidence K read b a o /
    preEventEvidence K read b a o = 1
  exact div_self he

/-- For a nonnegative source, a registered event carries nonnegative
unnormalized probability mass. A strictly positive mass is the separate
condition under which the reweighted state is a valid probability law. -/
theorem pre_event_evidence_nonnegative
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (b : X → ℝ) (h : ∀ x, 0 ≤ b x) (a : A) (o : O) :
    0 ≤ preEventEvidence K read b a o := by
  unfold preEventEvidence
  apply Finset.sum_nonneg
  intro y _
  exact belief_event_step_nonnegative K read b h a o y

/-- On strictly positive evidence, the event-updated and renormalized
microscopic weights are all nonnegative, completing the finite probability
certificate together with `normalized_event_mass_one`. -/
theorem normalized_event_weights_nonnegative
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (b : X → ℝ) (h : ∀ x, 0 ≤ b x) (a : A) (o : O)
    (hpos : 0 < preEventEvidence K read b a o) (y : X) :
    0 ≤ beliefUnnormalizedEventStep K read b a o y /
      preEventEvidence K read b a o := by
  exact div_nonneg (belief_event_step_nonnegative K read b h a o y)
    (le_of_lt hpos)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
