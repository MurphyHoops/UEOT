import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticPredictiveNullspace
import Mathlib.Tactic

/-!
# UMC quantitative breakthrough — operational future-test observability budget

For a registered family of actual future-word probes which reconstruct
canonical predictive class indicators, approximate experimental agreement
of their one-event-extended response probabilities yields an explicit
class-transition-mass error bound.

Unlike the prior generic approximate test-span theorem, here the
tests are the SAME K/read future-word probabilities, with identical
pre-action time convention; the one-step transition-test expectation is
not a separate experimental oracle. The coefficient L1 weights express
observability conditioning: weakly conditioned probes amplify error.

Statistical validity of bounds on measured probabilities must still be
obtained independently, e.g. with existing calibrated concentration tools.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

universe uX uA uO uI

/-- The exact pre-emission prefix of one genuine future word is its
conditional transition expectation, for any finite stochastic source. -/
theorem future_prefix_eq_successor_expectation
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (x : X) (a : A) (w : List (A × O)) :
    stochasticFuture K read x ((a, read x) :: w) =
      ∑ z : X, K.mass x a z * stochasticFuture K read z w := by
  simp [stochasticFuture, controlledOutputTrace]

/-- Finite, checkable future-test certificate. With class-indicator
reconstruction exact, the sole difference between two sources is the
measured difference of their next-event true prediction coordinates.
The L1 coefficient weights quantify amplification of finite-probe error. -/
theorem quantitative_future_probe_mass_defect
    {X : Type uX} {A : Type uA} {O : Type uO} {I : Type uI}
    [Fintype X] [Fintype I] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (probe : I → List (A × O))
    (coeff : ReachableState (stochasticFuture K read) → I → ℝ)
    (hresolve : FutureTestsResolvePredictiveClasses K read probe coeff)
    (x y : X) (a : A) (hread : read x = read y)
    (eps : I → ℝ)
    (hprobe : ∀ i,
      |stochasticFuture K read x ((a, read x) :: probe i) -
       stochasticFuture K read y ((a, read x) :: probe i)| ≤ eps i)
    (c : ReachableState (stochasticFuture K read)) :
    |massIntoClass K (stochasticFuture K read) x a c -
      massIntoClass K (stochasticFuture K read) y a c| ≤
      ∑ i, |coeff c i| * eps i := by
  classical
  have hstep : ∀ i,
      |(∑ z : X, K.mass x a z * stochasticFuture K read z (probe i)) -
       (∑ z : X, K.mass y a z * stochasticFuture K read z (probe i))| ≤
      eps i := by
    intro i
    rw [← future_prefix_eq_successor_expectation,
        ← future_prefix_eq_successor_expectation]
    simpa only [← hread] using hprobe i
  rw [class_mass_eq_reconstructed_future_expectations
        K read probe coeff hresolve x a c,
      class_mass_eq_reconstructed_future_expectations
        K read probe coeff hresolve y a c]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  calc
    |∑ i, coeff c i *
      ((∑ z : X, K.mass x a z * stochasticFuture K read z (probe i)) -
       (∑ z : X, K.mass y a z * stochasticFuture K read z (probe i)))| ≤
      ∑ i, |coeff c i| *
      |(∑ z : X, K.mass x a z * stochasticFuture K read z (probe i)) -
       (∑ z : X, K.mass y a z * stochasticFuture K read z (probe i))| := by
        simpa only [abs_mul] using
          (Finset.abs_sum_le_sum_abs
             (s := Finset.univ)
             (f := fun i => coeff c i *
               ((∑ z : X, K.mass x a z *
                 stochasticFuture K read z (probe i)) -
                (∑ z : X, K.mass y a z *
                 stochasticFuture K read z (probe i)))))
    _ ≤ ∑ i, |coeff c i| * eps i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hstep i) (abs_nonneg _)

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
