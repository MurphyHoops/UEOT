import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticPredictiveObservabilityBridge
import Mathlib.Tactic

/-!
# UMC stochastic nonvacuity: hidden microstate aliases with random dynamics

Physical tokens are (visible,hidden) booleans. Emission is the visible bit.
The next visible bit is fair random and the next hidden bit resets to false.
For each source state, both visible outcomes have mass 1/2; the kernel is
genuinely nondeterministic. Two different hidden physical tokens produce
identical ALL finite output-word predictions.

ONE-WORD future-output tests reconstruct exactly the TWO predictive class
indicators; therefore the general non-Dirac theorem applies and produces
the unique normalized stochastic quotient. The premise is exhibited,
not claimed to follow from observational equality alone.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

/-- A proper non-Dirac finite stochastic process with a hidden coordinate. -/
noncomputable def visibleFairHiddenReset :
    FiniteControlledStochasticKernel (Bool × Bool) Unit where
  mass := fun _ _ y => if y.2 = false then 1/2 else 0
  nonneg := by
    intro x a y
    split_ifs <;> norm_num
  normalized := by
    intro x a
    simp [Fintype.sum_prod_type]

def visibleRead (x : Bool × Bool) : Bool := x.1

/-- Both distinct true/false visible destinations have positive mass. -/
theorem genuine_stochastic_reset_has_two_positive_successors :
    0 < visibleFairHiddenReset.mass (false,false) () (false,false) ∧
    0 < visibleFairHiddenReset.mass (false,false) () (true,false) := by
  constructor <;> norm_num [visibleFairHiddenReset]

/-- The kernel rows literally agree even across different hidden labels. -/
theorem stochastic_reset_rows_identical (x y z : Bool × Bool) :
    visibleFairHiddenReset.mass x () z =
      visibleFairHiddenReset.mass y () z := rfl

/-- Future responses depend on present visible emission but NEVER on
the hidden bit under this actual stochastic source process. -/
theorem stochastic_reset_same_visible_has_same_all_futures
    {x y : Bool × Bool} (hvis : visibleRead x = visibleRead y) :
    stochasticFuture visibleFairHiddenReset visibleRead x =
      stochasticFuture visibleFairHiddenReset visibleRead y := by
  funext word
  cases word with
  | nil => rfl
  | cons event tail =>
      rcases event with ⟨a,o⟩
      change (if visibleRead x = o then
        ∑ z, visibleFairHiddenReset.mass x a z *
          controlledOutputTrace visibleFairHiddenReset visibleRead z tail
        else 0) =
        (if visibleRead y = o then
        ∑ z, visibleFairHiddenReset.mass y a z *
          controlledOutputTrace visibleFairHiddenReset visibleRead z tail
        else 0)
      rw [hvis]
      rfl

/-- Exact iff: TWO predictive classes, indexed by the actual visible bit.
Identical hidden output aliases do not create additional predictive classes. -/
theorem stochastic_reset_equal_future_iff_visible_equal
    (x y : Bool × Bool) :
    stochasticFuture visibleFairHiddenReset visibleRead x =
      stochasticFuture visibleFairHiddenReset visibleRead y ↔
      visibleRead x = visibleRead y := by
  constructor
  · intro h
    exact equal_stochastic_futures_have_equal_readout
      visibleFairHiddenReset visibleRead h ()
  · exact stochastic_reset_same_visible_has_same_all_futures

/-- A genuinely nontrivial predictive alias: distinct microscopic tokens
have exactly the same future output law, despite hidden-label inequality. -/
theorem stochastic_reset_hidden_alias_is_nontrivial :
    ((false,false) : Bool × Bool) ≠ (false,true) ∧
    stochasticFuture visibleFairHiddenReset visibleRead (false,false) =
      stochasticFuture visibleFairHiddenReset visibleRead (false,true) := by
  constructor
  · decide
  · exact (stochastic_reset_equal_future_iff_visible_equal _ _).2 rfl

def visibleProbe (o : Bool) : List (Unit × Bool) := [((),o)]

noncomputable def visibleIndicatorCoefficient
    (c : ReachableState
      (stochasticFuture visibleFairHiddenReset visibleRead))
    (o : Bool) : ℝ :=
  if visibleRead (Classical.choose c.property) = o then 1 else 0

/-- Explicit proof that the actual future-word tests span BOTH reachable
predictive-class indicators. No manually assigned true class or quotient law. -/
theorem stochastic_reset_future_tests_resolve_classes :
    FutureTestsResolvePredictiveClasses
      visibleFairHiddenReset visibleRead
      visibleProbe visibleIndicatorCoefficient := by
  classical
  intro c y
  let rep : Bool × Bool := Classical.choose c.property
  have hrep : stochasticFuture visibleFairHiddenReset visibleRead rep = c.1 :=
    Classical.choose_spec c.property
  have hclasses :
      (stochasticFuture visibleFairHiddenReset visibleRead y = c.1) ↔
        visibleRead y = visibleRead rep := by
    rw [← hrep]
    exact stochastic_reset_equal_future_iff_visible_equal y rep
  change (if stochasticFuture visibleFairHiddenReset visibleRead y = c.1
          then (1 : ℝ) else 0) =
    ∑ o : Bool, (if visibleRead rep = o then (1 : ℝ) else 0) *
      stochasticFuture visibleFairHiddenReset visibleRead y [((),o)]
  rw [if_congr hclasses (by rfl) (by rfl)]
  simp_rw [one_word_trace_is_pre_transition_observation]
  cases hy : visibleRead y <;> cases hr : visibleRead rep <;>
    norm_num [Fintype.sum_bool, hy, hr]

/-- Proper stochastic process, hidden microstate alias, class-identifying
future tests, AND unique normalized predictive quotient, all in ONE source. -/
theorem stochastic_hidden_alias_has_derived_unique_quotient :
    letI : Fintype (ReachableState
      (stochasticFuture visibleFairHiddenReset visibleRead)) :=
      Fintype.ofFinite _
    ∃! Kbar : FiniteControlledStochasticKernel
      (ReachableState (stochasticFuture visibleFairHiddenReset visibleRead)) Unit,
      ∀ x a c,
        Kbar.mass
          (toReachable (stochasticFuture visibleFairHiddenReset visibleRead) x)
          a c =
        massIntoClass visibleFairHiddenReset
          (stochasticFuture visibleFairHiddenReset visibleRead) x a c :=
  stochastic_future_tests_have_unique_normalized_quotient
    visibleFairHiddenReset visibleRead
    visibleProbe visibleIndicatorCoefficient
    stochastic_reset_future_tests_resolve_classes

/-- A useful negative boundary: failed strong lumpability of the future
quotient formally entails impossibility of ANY registered finite probe set
satisfying the future-indicator spanning premise. -/
theorem no_finite_future_probe_identification_if_not_lumpable
    {X : Type*} {A : Type*} {O : Type*} {I : Type*}
    [Fintype X] [Fintype I] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (hn : ¬ StrongLumpability K (stochasticFuture K read))
    (probe : I → List (A × O))
    (coeff : ReachableState (stochasticFuture K read) → I → ℝ) :
    ¬ FutureTestsResolvePredictiveClasses K read probe coeff := by
  intro h
  exact hn (stochastic_future_tests_force_strong_lumpability
    K read probe coeff h)

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
