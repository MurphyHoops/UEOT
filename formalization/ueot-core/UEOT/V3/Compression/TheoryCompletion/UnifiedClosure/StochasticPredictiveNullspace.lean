import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticPredictiveObservabilityBridge
import Mathlib.Tactic

/-!
# UMC deeper obstruction — Markov descent is governed by a predictive nullspace

Even when microstate future-signature equivalence is NOT Markov lumpable,
one-step class transition-mass differences for equal predictive states
are invisible to EVERY future response. That means the class-mass
difference lies in the kernel of the linear prediction-response map.

If distinct class future response functions are linearly independent,
the kernel is trivial and strong lumpability follows WITHOUT an explicit
probe reconstruction coefficient. This is a geometric source-side
criterion; no independent transition-mass agreement is assumed.

The result does not claim that future rows are always independent:
the existing six-state mixture-alias no-go is a counterexample to that.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

universe uX uA uO

/-- The exact source-to-class mass aggregation intertwines the one-step
microstate prediction with a linear mixture of reachable class futures.
Holds for EVERY finite K/read, including non-lumpable countermodels. -/
theorem class_trace_mixture_equals_micro_successor_trace
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (x : X) (a : A) (w : List (A × O)) :
    letI : Fintype (ReachableState (stochasticFuture K read)) :=
      Fintype.ofFinite _
    (∑ c : ReachableState (stochasticFuture K read),
       massIntoClass K (stochasticFuture K read) x a c * c.1 w) =
      ∑ z : X, K.mass x a z * stochasticFuture K read z w := by
  classical
  letI : Fintype (ReachableState (stochasticFuture K read)) :=
    Fintype.ofFinite _
  change (∑ c : ReachableState (stochasticFuture K read),
      massIntoClass K (stochasticFuture K read) x a c * c.1 w) =
    ∑ z : X, K.mass x a z * stochasticFuture K read z w
  calc
    (∑ c : ReachableState (stochasticFuture K read),
        massIntoClass K (stochasticFuture K read) x a c * c.1 w) =
      ∑ c : ReachableState (stochasticFuture K read),
        ∑ z : X, (if stochasticFuture K read z = c.1 then
          K.mass x a z else 0) * c.1 w := by
        apply Finset.sum_congr rfl
        intro c _
        rw [massIntoClass, Finset.sum_mul]
    _ = ∑ z : X, ∑ c : ReachableState (stochasticFuture K read),
        (if stochasticFuture K read z = c.1 then
          K.mass x a z else 0) * c.1 w := Finset.sum_comm
    _ = ∑ z : X, K.mass x a z * stochasticFuture K read z w := by
      apply Finset.sum_congr rfl
      intro z _
      have hclass : ∀ c : ReachableState (stochasticFuture K read),
          (stochasticFuture K read z = c.1) ↔
          (c = toReachable (stochasticFuture K read) z) := by
        intro c
        constructor
        · intro heq; exact Subtype.ext heq.symm
        · intro heq; exact congrArg Subtype.val heq |>.symm
      simp_rw [hclass]
      calc
        (∑ c : ReachableState (stochasticFuture K read),
          (if c = toReachable (stochasticFuture K read) z then
            K.mass x a z else 0) * c.1 w) =
          ∑ c : ReachableState (stochasticFuture K read),
            if c = toReachable (stochasticFuture K read) z then
              K.mass x a z * c.1 w else 0 := by
                apply Finset.sum_congr rfl
                intro c _
                split_ifs <;> ring
        _ = K.mass x a z *
            (toReachable (stochasticFuture K read) z).1 w := by simp
        _ = K.mass x a z * stochasticFuture K read z w := rfl

/-- Equal entire future responses force the micro transition-class
difference to lie in the *observable prediction nullspace*, irrespective
of whether the ordinary quotient exists. -/
theorem equivalent_futures_have_nullspace_class_mass_difference
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    {x y : X} (heq : stochasticFuture K read x =
      stochasticFuture K read y)
    (a : A) (w : List (A × O)) :
    letI : Fintype (ReachableState (stochasticFuture K read)) :=
      Fintype.ofFinite _
    (∑ c : ReachableState (stochasticFuture K read),
      (massIntoClass K (stochasticFuture K read) x a c -
        massIntoClass K (stochasticFuture K read) y a c) * c.1 w) = 0 := by
  classical
  letI : Fintype (ReachableState (stochasticFuture K read)) :=
    Fintype.ofFinite _
  change (∑ c : ReachableState (stochasticFuture K read),
     (massIntoClass K (stochasticFuture K read) x a c -
      massIntoClass K (stochasticFuture K read) y a c) * c.1 w) = 0
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [class_trace_mixture_equals_micro_successor_trace,
    class_trace_mixture_equals_micro_successor_trace,
    equal_futures_agree_on_transition_future_tests K read heq a w]
  ring

/-- If the unique future response functions of the reachable predictive
classes are linearly independent, then every observable nullspace
difference vanishes, forcing actual stochastic Markov lumpability.

Unlike future-test spanning, this only assumes a source-side algebraic
independence property of the canonical trace functions. -/
theorem linearly_independent_stochastic_futures_force_lumpability
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (hind : LinearIndependent ℝ
      (fun c : ReachableState (stochasticFuture K read) => c.1)) :
    StrongLumpability K (stochasticFuture K read) := by
  classical
  letI : Fintype (ReachableState (stochasticFuture K read)) :=
    Fintype.ofFinite _
  intro x y heq a c
  let delta : ReachableState (stochasticFuture K read) → ℝ :=
    fun d => massIntoClass K (stochasticFuture K read) x a d -
      massIntoClass K (stochasticFuture K read) y a d
  have hzero : (∑ d : ReachableState (stochasticFuture K read),
      delta d • (d.1 : List (A × O) → ℝ)) = 0 := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact equivalent_futures_have_nullspace_class_mass_difference
      K read heq a w
  have hc := (linearIndependent_iff').mp hind Finset.univ delta
    hzero c (Finset.mem_univ c)
  exact sub_eq_zero.mp hc

/-- Fully normalized controlled stochastic predictive quotient obtained
from the intrinsic linear independence of the class future signatures.
The six-state counterexample prevents replacing this assumption by mere
pairwise distinctness. -/
theorem independent_stochastic_predictive_rows_unique_quotient
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (hind : LinearIndependent ℝ
      (fun c : ReachableState (stochasticFuture K read) => c.1)) :
    letI : Fintype (ReachableState (stochasticFuture K read)) :=
      Fintype.ofFinite _
    ∃! Kbar : FiniteControlledStochasticKernel
      (ReachableState (stochasticFuture K read)) A,
      ∀ x a c,
        Kbar.mass (toReachable (stochasticFuture K read) x) a c =
          massIntoClass K (stochasticFuture K read) x a c :=
  (strong_lumpability_iff_existsUnique_stochastic_quotient
    K (stochasticFuture K read)).mp
      (linearly_independent_stochastic_futures_force_lumpability
        K read hind)

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
