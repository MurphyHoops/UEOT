import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictiveOptimalControlLift
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticPersistentHiddenExample
import Mathlib.Tactic

/-!
# UMC object-identity boundary — Markov predictive closure is not goal closure

The SAME stochastic process can have an exact uniquely normalized Markov
predictive quotient and yet fail exact control quotient for a legitimate
microphysical reward that depends on persistent hidden memory.

This is the precise absent source obligation: a downstream organization,
maintenance, repair or reward predicate must be constant on predictive
fibres (or carry additional state/context). Control value and teleology
cannot be inherited from prediction merely by renaming the quotient.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState
open UEOT.V3.FiniteDiscountedControl

/-- A microphysical task valuation reads only the persistent hidden bit. -/
def hiddenMemoryReward (x : Bool × Bool) (_ : Unit) : ℝ :=
  if x.2 then 1 else 0

/-- The present and all future VISIBLE observations are identical for
these different hidden-reward states. -/
theorem hidden_value_states_predictively_identical :
    stochasticFuture visibleFairHiddenPersistent visibleRead (false,false) =
      stochasticFuture visibleFairHiddenPersistent visibleRead (false,true) :=
  (persistent_future_iff_read_equal _ _).2 rfl

/-- Prediction equivalence does NOT imply a reward function on macro
predictive classes exists. The persistent hidden bit is a real microstate
difference erased by the predictive projection, and its reward cannot
factor through that projection. -/
theorem no_macro_reward_for_hidden_memory_goal :
    ¬ ∃ rbar : ReachableState
        (stochasticFuture visibleFairHiddenPersistent visibleRead) → Unit → ℝ,
      ∀ x : Bool × Bool, ∀ a : Unit,
        hiddenMemoryReward x a =
          rbar (toReachable
            (stochasticFuture visibleFairHiddenPersistent visibleRead) x) a := by
  rintro ⟨rbar, h⟩
  have halias :
      toReachable (stochasticFuture visibleFairHiddenPersistent visibleRead)
        (false,false) =
      toReachable (stochasticFuture visibleFairHiddenPersistent visibleRead)
        (false,true) :=
    Subtype.ext hidden_value_states_predictively_identical
  have h0 := h (false,false) ()
  have h1 := h (false,true) ()
  have heq : (0 : ℝ) = 1 := by
    calc
      (0 : ℝ) = rbar
        (toReachable (stochasticFuture visibleFairHiddenPersistent visibleRead)
          (false,false)) () := by
            simpa [hiddenMemoryReward] using h0
      _ = rbar
        (toReachable (stochasticFuture visibleFairHiddenPersistent visibleRead)
          (false,true)) () := by rw [halias]
      _ = 1 := by
        simpa [hiddenMemoryReward] using h1.symm
  norm_num at heq

/-- Conversely, any registered observable bounded macro objective DOES
give a valid exact P-QUO control bridge in this very same stochastic process.
The action type here is Unit; this is a source-coherence/nonvacuity fixture,
not a proof of nontrivial action selection. -/
noncomputable def persistentVisibleExactControl :
    letI : Fintype (ReachableState
      (stochasticFuture visibleFairHiddenPersistent visibleRead)) :=
      Fintype.ofFinite _
    ExactControlQuotient (Bool × Bool)
      (ReachableState
        (stochasticFuture visibleFairHiddenPersistent visibleRead))
      (fun _ => Unit) := by
  classical
  exact predictiveFutureExactControlQuotient
    visibleFairHiddenPersistent visibleRead
    visibleProbe persistentIndicatorCoefficient
    persistent_hidden_future_tests_resolve_classes
    (fun _ _ => (1 : ℝ)) 1 (1/2)
    (by intro c a; norm_num)
    (by norm_num) (by norm_num)

/-- A single process simultaneously witnesses loss of genuine hidden
micro memory and a valid exact control bridge for a supplied observable
objective. Reward fidelity, not stochastic prediction alone, separates
the two control outcomes. -/
theorem persistent_visible_objective_lifts_value_exactly :
    letI : Fintype (ReachableState
      (stochasticFuture visibleFairHiddenPersistent visibleRead)) :=
      Fintype.ofFinite _
    ∀ x : Bool × Bool,
      persistentVisibleExactControl.micro.optimalValue x =
        persistentVisibleExactControl.macroModel.optimalValue
          (persistentVisibleExactControl.f x) := by
  classical
  letI : Fintype (ReachableState
    (stochasticFuture visibleFairHiddenPersistent visibleRead)) :=
    Fintype.ofFinite _
  intro x
  exact persistentVisibleExactControl.optimalValue_apply x

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
