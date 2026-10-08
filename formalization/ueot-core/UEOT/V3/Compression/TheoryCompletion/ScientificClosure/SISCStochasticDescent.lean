import UEOT.V3.FiniteStablePartitionQuotientLaw
import Mathlib.Tactic

/-!
# SISC stochastic continuation: exactly when a finite Markov quotient exists

This is a necessary-and-sufficient **bridge** to the existing P-ALG-01
controlled-stable partition theorem, not a substitute for it. An arbitrary
candidate predictive partition need not support a Markov kernel on its classes.
The additional obligation is stability of the *actual block masses*.

We deliberately do not identify output predictive equivalence with strong
Markov lumpability without a separately certified identification condition.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.FiniteStablePartition

universe uX uA uR uO

/-- A kernel on quotient blocks whose values agree with the underlying
controlled transition's exact block mass. -/
def ExactControlledMarkovDescent
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    [Fintype X] [Fintype A]
    (M : Model X A R O) (S : Setoid X)
    (Q : A → Quotient S → Quotient S → ℝ) : Prop :=
  ∀ a x z, Q a (Quotient.mk S x) (Quotient.mk S z) = blockMass M S a x z

/-- The existing `Stable` condition is **necessary AND sufficient** for a
well-defined quotient transition, and that transition is unique. This is an
exact stochastic analogue of `M-QD` descent for finite transition matrices. -/
theorem stable_iff_unique_stochastic_descent
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    [Fintype X] [Fintype A]
    (M : Model X A R O) (S : Setoid X) :
    Stable M S ↔
      ∃! Q : A → Quotient S → Quotient S → ℝ,
        ExactControlledMarkovDescent M S Q := by
  constructor
  · intro hStable
    refine ⟨quotientTransition M S hStable, ?_, ?_⟩
    · intro a x z
      exact quotientTransition_mk M S hStable a x z
    · intro Q hQ
      funext a q r
      refine Quotient.inductionOn q ?_
      intro x
      refine Quotient.inductionOn r ?_
      intro z
      exact (hQ a x z).trans
        (quotientTransition_mk M S hStable a x z).symm
  · rintro ⟨Q, hQ, _⟩
    intro x y hxy a z
    calc
      blockMass M S a x z = Q a ⟦x⟧ ⟦z⟧ := (hQ a x z).symm
      _ = Q a ⟦y⟧ ⟦z⟧ := by rw [Quotient.sound hxy]
      _ = blockMass M S a y z := hQ a y z

/-- Uniquely descended transitions really form a nonnegative finite stochastic
law (normalization is established by the existing finite block partition
theorem, rather than by summing over redundant source representatives). -/
theorem stable_quotient_transition_nonnegative
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    [Fintype X] [Fintype A]
    (M : Model X A R O) (S : Setoid X)
    (hStable : Stable M S) (a : A) (q r : Quotient S) :
    0 ≤ quotientTransition M S hStable a q r :=
  quotientTransition_nonneg M S hStable a q r

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
