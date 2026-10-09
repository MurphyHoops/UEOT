import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictiveGoalClosureBoundary
import Mathlib.Tactic

/-!
# UMC: active stochastic control with persistent hidden micro memory

Unlike the passive Unit-action fixture, this model has TWO actual actions,
each producing a different random visible distribution, while the hidden
physical memory persists unchanged. All future observations remain
independent of that hidden memory. A two-word-class finite experiment
certificate constructs an exact Markov predictive quotient, and the frozen
P-QUO theorem then transfers macro-optimal control to all physical causal
history-dependent randomized policies for a declared observable reward.

No physical parent identity, autonomous choice of goal, or source program
is inferred from this example.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState
open UEOT.V3.FiniteDiscountedControl
open CausalPolicy

universe uMemory

/-- A has TWO actions, each selecting the visible bit with probability 3/4
and the alternative visible bit with probability 1/4; hidden memory persists. -/
noncomputable def activeHiddenKernel :
    FiniteControlledStochasticKernel (Bool × Bool) Bool where
  mass := fun x a z =>
    if z.2 = x.2 then
      (if z.1 = a then (3/4 : ℝ) else 1/4) else 0
  nonneg := by
    intro x a z
    split_ifs <;> norm_num
  normalized := by
    intro ⟨b,h⟩ a
    cases h <;> cases a <;>
      norm_num [Fintype.sum_prod_type]

/-- Two genuinely different non-Dirac action kernels on one source token. -/
theorem active_hidden_kernel_has_nontrivial_control_effect :
    activeHiddenKernel.mass (false,false) false (false,false) = 3/4 ∧
    activeHiddenKernel.mass (false,false) true (false,false) = 1/4 ∧
    activeHiddenKernel.mass (false,false) false (true,false) = 1/4 ∧
    activeHiddenKernel.mass (false,false) true (true,false) = 3/4 := by
  constructor <;> norm_num [activeHiddenKernel]
  -- remaining conjuncts handled by normalization

/-- Actual one-step expected response, not an independent macro oracle. -/
private theorem active_expected_trace
    (b h a : Bool) (word : List (Bool × Bool)) :
    (∑ z : Bool × Bool, activeHiddenKernel.mass (b,h) a z *
      controlledOutputTrace activeHiddenKernel visibleRead z word) =
    3/4 * controlledOutputTrace activeHiddenKernel visibleRead (a,h) word +
    1/4 * controlledOutputTrace activeHiddenKernel visibleRead (!a,h) word := by
  cases h <;> cases a <;>
    simp [activeHiddenKernel, Fintype.sum_prod_type] <;> ring

/-- Hidden physical memory can affect transition support while remaining
unidentifiable from every future *visible* output, with both actions active. -/
theorem active_hidden_future_independent_of_memory
    (word : List (Bool × Bool)) (b h1 h2 : Bool) :
    controlledOutputTrace activeHiddenKernel visibleRead (b,h1) word =
      controlledOutputTrace activeHiddenKernel visibleRead (b,h2) word := by
  induction word generalizing b h1 h2 with
  | nil => rfl
  | cons ev rest ih =>
      rcases ev with ⟨a,o⟩
      change (if b = o then
        ∑ z : Bool × Bool, activeHiddenKernel.mass (b,h1) a z *
          controlledOutputTrace activeHiddenKernel visibleRead z rest else 0) =
        (if b = o then
        ∑ z : Bool × Bool, activeHiddenKernel.mass (b,h2) a z *
          controlledOutputTrace activeHiddenKernel visibleRead z rest else 0)
      by_cases hb : b = o
      · simp only [hb, if_pos]
        rw [active_expected_trace, active_expected_trace,
          ih a h1 h2, ih (!a) h1 h2]
      · simp [hb]

theorem active_hidden_future_eq_iff_visible (x y : Bool × Bool) :
    stochasticFuture activeHiddenKernel visibleRead x =
      stochasticFuture activeHiddenKernel visibleRead y ↔
      visibleRead x = visibleRead y := by
  constructor
  · intro h
    exact equal_stochastic_futures_have_equal_readout
      activeHiddenKernel visibleRead h false
  · intro h
    rcases x with ⟨bx,hx⟩
    rcases y with ⟨cy,hy⟩
    change bx = cy at h
    subst cy
    funext word
    exact active_hidden_future_independent_of_memory word bx hx hy

def activeFutureProbe (o : Bool) : List (Bool × Bool) :=
  [(false,o)]

noncomputable def activeIndicatorCoefficient
    (c : ReachableState (stochasticFuture activeHiddenKernel visibleRead))
    (o : Bool) : ℝ :=
  if visibleRead (Classical.choose c.property) = o then 1 else 0

/-- A two-test spanning certificate derived using only TRUE source
future-word responses, for the genuine two-action random process. -/
theorem active_future_indicator_probe_certificate :
    FutureTestsResolvePredictiveClasses
      activeHiddenKernel visibleRead
      activeFutureProbe activeIndicatorCoefficient := by
  classical
  intro c y
  let rep : Bool × Bool := Classical.choose c.property
  have hrep : stochasticFuture activeHiddenKernel visibleRead rep = c.1 :=
    Classical.choose_spec c.property
  have hclasses :
      (stochasticFuture activeHiddenKernel visibleRead y = c.1) ↔
        visibleRead y = visibleRead rep := by
    rw [← hrep]
    exact active_hidden_future_eq_iff_visible y rep
  change (if stochasticFuture activeHiddenKernel visibleRead y = c.1
          then (1 : ℝ) else 0) =
    ∑ o : Bool, (if visibleRead rep = o then (1 : ℝ) else 0) *
      stochasticFuture activeHiddenKernel visibleRead y [(false,o)]
  rw [if_congr hclasses (by rfl) (by rfl)]
  simp_rw [one_word_trace_is_pre_transition_observation]
  cases hy : visibleRead y <;> cases hr : visibleRead rep <;>
    norm_num [Fintype.sum_bool, hy, hr]

/-- External declared goal: reward an action which matches present
visible observation. This remains an input, not an emergent physical goal. -/
noncomputable def activeObservableReward
    (c : ReachableState (stochasticFuture activeHiddenKernel visibleRead))
    (a : Bool) : ℝ :=
  if visibleRead (Classical.choose c.property) = a then 1 else 0

/-- The macro-goal readout is actually sourced by the present physical
visible state. It does not secretly depend on a choice of representative,
so the control reward contract is genuinely implemented by this one K/read. -/
theorem activeObservableReward_exact_source_readout
    (x : Bool × Bool) (a : Bool) :
    activeObservableReward
      (toReachable (stochasticFuture activeHiddenKernel visibleRead) x) a =
        (if visibleRead x = a then (1 : ℝ) else 0) := by
  classical
  let c := toReachable (stochasticFuture activeHiddenKernel visibleRead) x
  let rep : Bool × Bool := Classical.choose c.property
  have hrep : stochasticFuture activeHiddenKernel visibleRead rep = c.1 :=
    Classical.choose_spec c.property
  have hobs : visibleRead rep = visibleRead x :=
    (active_hidden_future_eq_iff_visible rep x).mp hrep
  simpa [activeObservableReward, c, rep, hobs]

private theorem activeObservableReward_bound :
    ∀ c a, |activeObservableReward c a| ≤ (1 : ℝ) := by
  intro c a
  unfold activeObservableReward
  split_ifs <;> norm_num

/-- Real, non-Dirac, TWO-ACTION, persistent hidden-state process produces
a precise finite discounted control quotient from its own future tests. -/
noncomputable def activePredictiveControl :
    letI : Fintype (ReachableState
      (stochasticFuture activeHiddenKernel visibleRead)) :=
      Fintype.ofFinite _
    ExactControlQuotient (Bool × Bool)
      (ReachableState (stochasticFuture activeHiddenKernel visibleRead))
      (fun _ => Bool) := by
  classical
  exact predictiveFutureExactControlQuotient
    activeHiddenKernel visibleRead
    activeFutureProbe activeIndicatorCoefficient
    active_future_indicator_probe_certificate
    activeObservableReward 1 (1/2)
    activeObservableReward_bound (by norm_num) (by norm_num)

/-- The actual macro greedy action on its canonical predictive classes is
optimal against ANY history-dependent randomized MICRO control policy. -/
theorem active_two_action_macro_greedy_is_micro_causally_optimal :
    letI : Fintype (ReachableState
      (stochasticFuture activeHiddenKernel visibleRead)) :=
      Fintype.ofFinite _
    (∀ x : Bool × Bool,
      activePredictiveControl.micro.optimalValue x =
        activePredictiveControl.macroModel.optimalValue
          (activePredictiveControl.f x)) ∧
    (∀ {t : ℕ} (x : Bool × Bool),
      infiniteValue
        (selectorPolicy
          (activePredictiveControl.liftSelector
            activePredictiveControl.macroModel.greedyAction))
        activePredictiveControl.micro (t := t) x =
        activePredictiveControl.micro.optimalValue x) ∧
    (∀ (π : CausalPolicy.{0,0,uMemory} (Bool × Bool) (fun _ => Bool)) {t : ℕ}
      (h : π.Memory t),
      infiniteValue π activePredictiveControl.micro h ≤
        activePredictiveControl.micro.optimalValue (π.current h)) := by
  classical
  letI : Fintype (ReachableState
    (stochasticFuture activeHiddenKernel visibleRead)) :=
    Fintype.ofFinite _
  refine ⟨activePredictiveControl.optimalValue_apply, ?_, ?_⟩
  · intro t x
    exact (ExactControlQuotient.macroGreedy_lift_optimal.{0,0,0,uMemory}
        activePredictiveControl).1 (t := t) x
  · intro π t h
    exact (ExactControlQuotient.macroGreedy_lift_optimal.{0,0,0,uMemory}
        activePredictiveControl).2 π h

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
