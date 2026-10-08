import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFiniteStochasticQuotient
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCStochasticDescent

/-!
# SISC N1: reconciliation of two already proved stochastic quotient interfaces

The P-ALG-01 finite controlled model uses `Setoid X` and `blockMass`.
The new process-level finite stochastic interface uses any representation
`q : X → Q` and the reachable-image `massIntoClass`. The two constructions
must not silently diverge when q is the quotient map of the same Setoid.

This module proves a concrete conversion, equality of all class masses and
equivalence of the two strong-lumpability predicates. The result is an
architectural consistency check rather than a new physical-identity claim.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.FiniteStablePartition
open UEOT.V3.Compression.RecursiveSufficientState

universe uX uA uR uO

/-- Every P-ALG finite controlled model induces a normalized finite
controlled stochastic kernel with *identical* microscopic transitions. -/
def modelAsFiniteKernel
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    [Fintype X] (M : Model X A R O) :
    FiniteControlledStochasticKernel X A where
  mass := fun x a y => M.transition a x y
  nonneg := fun x a y => M.transition_nonneg a x y
  normalized := fun x a => M.transition_sum_one a x

/-- The concrete map into the quotient type of a declared Setoid. -/
def setoidRepresentation {X : Type uX} (S : Setoid X) : X → Quotient S :=
  fun x => Quotient.mk S x

/-- Old block mass and new reachable-image class mass are literally the same
finite sum once the target class is represented by the same source state. -/
theorem model_class_mass_reconciliation
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    [Fintype X] (M : Model X A R O) (S : Setoid X)
    (x z : X) (a : A) :
    massIntoClass (modelAsFiniteKernel M) (setoidRepresentation S)
      x a (toReachable (setoidRepresentation S) z) =
        blockMass M S a x z := by
  classical
  unfold massIntoClass blockMass
  apply Finset.sum_congr rfl
  intro y _
  have hrel : (setoidRepresentation S y = setoidRepresentation S z) ↔
      S.r y z := Quotient.eq
  by_cases h : S.r y z
  · have h' := hrel.mpr h
    simp [h, h', toReachable, modelAsFiniteKernel]
  · have h' : setoidRepresentation S y ≠ setoidRepresentation S z := by
      intro he
      exact h (hrel.mp he)
    simp [h, h', toReachable]

/-- The P-ALG-01 Setoid stability and the general reachable-image kernel
lumpability are equivalent mathematical claims, not separate axioms. -/
theorem model_strongLumpability_iff_stable
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    [Fintype X] [Fintype A]
    (M : Model X A R O) (S : Setoid X) :
    StrongLumpability (modelAsFiniteKernel M) (setoidRepresentation S) ↔
      Stable M S := by
  constructor
  · intro h x y hxy a z
    have hq : setoidRepresentation S x = setoidRepresentation S y :=
      Quotient.sound hxy
    have hs := h x y hq a (toReachable (setoidRepresentation S) z)
    simpa only [model_class_mass_reconciliation] using hs
  · intro h x y hxy a c
    rcases c.property with ⟨z, hz⟩
    have hc : c = toReachable (setoidRepresentation S) z :=
      Subtype.ext hz.symm
    rw [hc]
    have hrel : S.r x y := Quotient.eq.mp hxy
    simpa only [model_class_mass_reconciliation] using h hrel a z

/-- Consequently the two independently typed existence/uniqueness claims
are both true under precisely the same finite-model hypothesis. -/
theorem reconciliation_both_unique_quotients
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    [Fintype X] [Fintype A]
    (M : Model X A R O) (S : Setoid X)
    (h : Stable M S) :
    (∃! Q : A → Quotient S → Quotient S → ℝ,
        ExactControlledMarkovDescent M S Q) ∧
    (∃! Kbar : ReachableState (setoidRepresentation S) → A →
        ReachableState (setoidRepresentation S) → ℝ,
      ∀ x a c, Kbar (toReachable (setoidRepresentation S) x) a c =
        massIntoClass (modelAsFiniteKernel M) (setoidRepresentation S) x a c) := by
  constructor
  · exact (stable_iff_unique_stochastic_descent M S).mp h
  · exact (strong_lumpability_iff_existsUnique_class_kernel
      (modelAsFiniteKernel M) (setoidRepresentation S)).mp
        ((model_strongLumpability_iff_stable M S).mpr h)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
