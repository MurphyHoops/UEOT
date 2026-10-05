import UEOT.V3.Compression.TheoryCompletion.Purpose

/-!
# P1.5 — Teleological objective classes

A teleological objective is not identified with one scalar representative.
This stage packages the weak-order representation class and proves the expected
equivalence-class laws. Pi/Phi gauge structure is added only in P1.6.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set

universe uP

/-- The teleological class of J is the set of numerical objectives that induce
exactly the same weak ordering. -/
def TeleologicalObjectiveClass {P : Type uP}
    (J : NumericalObjective P) : Set (NumericalObjective P) :=
  {K | PolicyOrderingEquivalent J K}

@[simp] theorem mem_teleologicalObjectiveClass
    {P : Type uP} (J K : NumericalObjective P) :
    K ∈ TeleologicalObjectiveClass J ↔ PolicyOrderingEquivalent J K := by
  rfl

theorem policyOrderingEquivalent_refl
    {P : Type uP} (J : NumericalObjective P) :
    PolicyOrderingEquivalent J J := by
  intro p q
  rfl

theorem policyOrderingEquivalent_symm
    {P : Type uP} {J K : NumericalObjective P}
    (h : PolicyOrderingEquivalent J K) :
    PolicyOrderingEquivalent K J := by
  intro p q
  exact (h p q).symm

theorem policyOrderingEquivalent_trans
    {P : Type uP} {J K L : NumericalObjective P}
    (hJK : PolicyOrderingEquivalent J K)
    (hKL : PolicyOrderingEquivalent K L) :
    PolicyOrderingEquivalent J L := by
  intro p q
  exact (hJK p q).trans (hKL p q)

theorem teleologicalObjectiveClass_eq_of_equivalent
    {P : Type uP} {J K : NumericalObjective P}
    (h : PolicyOrderingEquivalent J K) :
    TeleologicalObjectiveClass J = TeleologicalObjectiveClass K := by
  ext L
  constructor
  · intro hJL
    exact policyOrderingEquivalent_trans
      (policyOrderingEquivalent_symm h) hJL
  · intro hKL
    exact policyOrderingEquivalent_trans h hKL

end UEOT.V3.Compression.TheoryCompletion
