import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCStochasticDescent
import Mathlib.Tactic

/-!
# Observable experiments -> controlled Markov lumpability

**Scientific distinction.** Observational agreement is not the same as
Markov block-mass agreement. A finite family of registered one-step response
tests can, however, *force* exact lumpability if it linearly reconstructs
every target block's indicator. This is a checkable spanning assumption,
stronger than mere pairwise separation of output labels.

The theorem below has no `Stable`, Markov-quotient, or block-mass-equality
premise. It derives `Stable` from measured test expectations and an explicit
test-to-class reconstruction certificate, then uses the existing P-ALG
quotient descent mechanism.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.FiniteStablePartition

universe uX uA uR uO uI

/-- One-step expected test response for the real controlled transition. -/
def transitionTestExpectation
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    [Fintype X]
    (M : Model X A R O) (test : X → ℝ) (a : A) (x : X) : ℝ :=
  ∑ y, M.transition a x y * test y

/-- A finite registered test family explicitly reconstructs the indicator
of EVERY target equivalence class. A pairwise-separating test family is not
automatically indicator-spanning: that implication is not assumed. -/
def SpansPartitionIndicators
    {X : Type uX} {I : Type uI} [Fintype I]
    (S : Setoid X) (test : I → X → ℝ) (coeff : X → I → ℝ) : Prop :=
  by
    classical
    exact ∀ z y, (if S.r y z then (1 : ℝ) else 0) =
      ∑ i, coeff z i * test i y

/-- Observed one-step test laws agree at *every* pair of source states in the
same declared candidate class, for all actions and tests. -/
def SameTestExpectationsOnFibers
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    {I : Type uI} [Fintype X] [Fintype I]
    (M : Model X A R O) (S : Setoid X) (test : I → X → ℝ) : Prop :=
  ∀ ⦃x y⦄, S.r x y → ∀ a i,
    transitionTestExpectation M (test i) a x =
      transitionTestExpectation M (test i) a y

/-- Finite linear test reconstruction turns each real block transition mass
into a linear combination of directly observed test expectations. -/
theorem blockMass_eq_sum_testExpectations
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    {I : Type uI} [Fintype X] [Fintype I]
    (M : Model X A R O) (S : Setoid X)
    (test : I → X → ℝ) (coeff : X → I → ℝ)
    (hspan : SpansPartitionIndicators S test coeff)
    (a : A) (x z : X) :
    blockMass M S a x z =
      ∑ i, coeff z i * transitionTestExpectation M (test i) a x := by
  classical
  calc
    blockMass M S a x z =
        ∑ y : X, M.transition a x y * (if S.r y z then 1 else 0) := by
      unfold blockMass
      apply Finset.sum_congr rfl
      intro y hy
      split_ifs <;> ring
    _ = ∑ y : X, M.transition a x y * (∑ i, coeff z i * test i y) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hspan z y]
    _ = ∑ y : X, ∑ i, M.transition a x y * (coeff z i * test i y) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ i, ∑ y : X, M.transition a x y * (coeff z i * test i y) :=
      Finset.sum_comm
    _ = ∑ i, coeff z i * transitionTestExpectation M (test i) a x := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [transitionTestExpectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring

/-- **The observational-to-dynamical bridge:** matching measured one-step
test expectations plus a separate indicator-spanning certificate is sufficient
to derive *actual*, all-action strong Markov lumpability. -/
theorem test_spanning_forces_controlled_lumpability
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    {I : Type uI} [Fintype X] [Fintype A] [Fintype I]
    (M : Model X A R O) (S : Setoid X)
    (test : I → X → ℝ) (coeff : X → I → ℝ)
    (hspan : SpansPartitionIndicators S test coeff)
    (hobs : SameTestExpectationsOnFibers M S test) :
    Stable M S := by
  intro x y hxy a z
  rw [blockMass_eq_sum_testExpectations M S test coeff hspan a x z,
      blockMass_eq_sum_testExpectations M S test coeff hspan a y z]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hobs hxy a i]

/-- The real quotient exists and is UNIQUE, derived solely from an observable
test certificate. The hidden `Stable` property is a theorem, not an input. -/
theorem measured_tests_unique_markov_quotient
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    {I : Type uI} [Fintype X] [Fintype A] [Fintype I]
    (M : Model X A R O) (S : Setoid X)
    (test : I → X → ℝ) (coeff : X → I → ℝ)
    (hspan : SpansPartitionIndicators S test coeff)
    (hobs : SameTestExpectationsOnFibers M S test) :
    ∃! Q : A → Quotient S → Quotient S → ℝ,
      ExactControlledMarkovDescent M S Q := by
  exact (stable_iff_unique_stochastic_descent M S).mp
    (test_spanning_forces_controlled_lumpability M S test coeff hspan hobs)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
