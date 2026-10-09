import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticHiddenAliasExample
import Mathlib.Tactic

/-!
# Robustness check: hidden PHYSICAL memory persists while predictive class
collapses it, with genuinely random visible dynamics.

Unlike the earlier hidden-reset example, this transition preserves hidden
state perfectly. Different hidden-state microtokens have different transition
rows (disjoint support), yet every observed future trace is identical if
the present visible bit agrees. So lawful predictive Markov quotients can
forget true persistent microphysical memory, without proving ontic sameness.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

noncomputable def visibleFairHiddenPersistent :
    FiniteControlledStochasticKernel (Bool × Bool) Unit where
  mass := fun x _ y => if y.2 = x.2 then 1/2 else 0
  nonneg := by
    intro x a y
    split_ifs <;> norm_num
  normalized := by
    intro x a
    cases hx : x.2 <;>
      simp [Fintype.sum_prod_type]

/-- Transition rows distinguish the two hidden source labels even though
future emissions do not. -/
theorem persistent_hidden_has_distinct_micro_rows :
    visibleFairHiddenPersistent.mass (false,false) () (false,false) = 1/2 ∧
    visibleFairHiddenPersistent.mass (false,true) () (false,false) = 0 := by
  constructor <;> norm_num [visibleFairHiddenPersistent]

/-- An exact sum formula, independently of the visible source bit. -/
private theorem persistent_next_trace_average
    (b h : Bool) (rest : List (Unit × Bool)) :
    (∑ z : Bool × Bool, visibleFairHiddenPersistent.mass (b,h) () z *
      controlledOutputTrace visibleFairHiddenPersistent visibleRead z rest) =
    (controlledOutputTrace visibleFairHiddenPersistent visibleRead (false,h) rest +
      controlledOutputTrace visibleFairHiddenPersistent visibleRead (true,h) rest) / 2 := by
  cases h <;>
    simp [visibleFairHiddenPersistent, Fintype.sum_prod_type] <;> ring

/-- Pathwise predictive equivalence is stable through every registered
experiment even though the hidden physical bit persists. -/
theorem persistent_hidden_same_visible_all_future_words
    (word : List (Unit × Bool)) (b h1 h2 : Bool) :
    controlledOutputTrace visibleFairHiddenPersistent visibleRead (b,h1) word =
      controlledOutputTrace visibleFairHiddenPersistent visibleRead (b,h2) word := by
  induction word generalizing b h1 h2 with
  | nil => rfl
  | cons ev rest ih =>
      rcases ev with ⟨a,o⟩
      cases a
      change (if b = o then
        ∑ z : Bool × Bool, visibleFairHiddenPersistent.mass (b,h1) () z *
          controlledOutputTrace visibleFairHiddenPersistent visibleRead z rest
        else 0) =
        (if b = o then
        ∑ z : Bool × Bool, visibleFairHiddenPersistent.mass (b,h2) () z *
          controlledOutputTrace visibleFairHiddenPersistent visibleRead z rest
        else 0)
      by_cases hv : b = o
      · simp only [hv, if_pos]
        rw [persistent_next_trace_average, persistent_next_trace_average,
          ih false h1 h2, ih true h1 h2]
      · simp [hv]

/-- Despite physically persistent hidden memory, complete future
response equivalence is EXACTLY equality of the visible bit. -/
theorem persistent_future_iff_read_equal (x y : Bool × Bool) :
    stochasticFuture visibleFairHiddenPersistent visibleRead x =
      stochasticFuture visibleFairHiddenPersistent visibleRead y ↔
      visibleRead x = visibleRead y := by
  constructor
  · intro h
    exact equal_stochastic_futures_have_equal_readout
      visibleFairHiddenPersistent visibleRead h ()
  · intro h
    rcases x with ⟨bx,hx⟩
    rcases y with ⟨cy,hy⟩
    change bx = cy at h
    subst cy
    funext word
    exact persistent_hidden_same_visible_all_future_words word bx hx hy

noncomputable def persistentIndicatorCoefficient
    (c : ReachableState
      (stochasticFuture visibleFairHiddenPersistent visibleRead))
    (o : Bool) : ℝ :=
  if visibleRead (Classical.choose c.property) = o then 1 else 0

/-- Explicit proof that the actual future-word tests span BOTH reachable
predictive-class indicators. No manually assigned true class or quotient law. -/
theorem persistent_hidden_future_tests_resolve_classes :
    FutureTestsResolvePredictiveClasses
      visibleFairHiddenPersistent visibleRead
      visibleProbe persistentIndicatorCoefficient := by
  classical
  intro c y
  let rep : Bool × Bool := Classical.choose c.property
  have hrep : stochasticFuture visibleFairHiddenPersistent visibleRead rep = c.1 :=
    Classical.choose_spec c.property
  have hclasses :
      (stochasticFuture visibleFairHiddenPersistent visibleRead y = c.1) ↔
        visibleRead y = visibleRead rep := by
    rw [← hrep]
    exact persistent_future_iff_read_equal y rep
  change (if stochasticFuture visibleFairHiddenPersistent visibleRead y = c.1
          then (1 : ℝ) else 0) =
    ∑ o : Bool, (if visibleRead rep = o then (1 : ℝ) else 0) *
      stochasticFuture visibleFairHiddenPersistent visibleRead y [((),o)]
  rw [if_congr hclasses (by rfl) (by rfl)]
  simp_rw [one_word_trace_is_pre_transition_observation]
  cases hy : visibleRead y <;> cases hr : visibleRead rep <;>
    norm_num [Fintype.sum_bool, hy, hr]

/-- Proper stochastic process, hidden microstate alias, class-identifying
future tests, AND unique normalized predictive quotient, all in ONE source. -/
theorem persistent_hidden_has_derived_unique_quotient :
    letI : Fintype (ReachableState
      (stochasticFuture visibleFairHiddenPersistent visibleRead)) :=
      Fintype.ofFinite _
    ∃! Kbar : FiniteControlledStochasticKernel
      (ReachableState (stochasticFuture visibleFairHiddenPersistent visibleRead)) Unit,
      ∀ x a c,
        Kbar.mass
          (toReachable (stochasticFuture visibleFairHiddenPersistent visibleRead) x)
          a c =
        massIntoClass visibleFairHiddenPersistent
          (stochasticFuture visibleFairHiddenPersistent visibleRead) x a c :=
  stochastic_future_tests_have_unique_normalized_quotient
    visibleFairHiddenPersistent visibleRead
    visibleProbe persistentIndicatorCoefficient
    persistent_hidden_future_tests_resolve_classes

/-- Physically distinct persistent hidden dynamics coexist with
identical entire future observational signatures and a legitimately
constructed unique normalized Markov predictive quotient. This is a
nontrivial non-Dirac witness that predictive identity is not microphysical
identity, not a P8 genealogical/organizational identity conclusion. -/
theorem persistent_hidden_predictive_quotient_loses_real_micro_memory :
    visibleFairHiddenPersistent.mass (false,false) () (false,false) = 1/2 ∧
    visibleFairHiddenPersistent.mass (false,true) () (false,false) = 0 ∧
    stochasticFuture visibleFairHiddenPersistent visibleRead (false,false) =
      stochasticFuture visibleFairHiddenPersistent visibleRead (false,true) ∧
    (letI : Fintype (ReachableState
        (stochasticFuture visibleFairHiddenPersistent visibleRead)) :=
        Fintype.ofFinite _
     ∃! Kbar : FiniteControlledStochasticKernel
       (ReachableState (stochasticFuture visibleFairHiddenPersistent visibleRead)) Unit,
       ∀ x a c,
         Kbar.mass
           (toReachable (stochasticFuture visibleFairHiddenPersistent visibleRead) x)
           a c =
         massIntoClass visibleFairHiddenPersistent
           (stochasticFuture visibleFairHiddenPersistent visibleRead) x a c) := by
  refine ⟨persistent_hidden_has_distinct_micro_rows.1,
    persistent_hidden_has_distinct_micro_rows.2, ?_,
    persistent_hidden_has_derived_unique_quotient⟩
  exact (persistent_future_iff_read_equal _ _).2 rfl

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
