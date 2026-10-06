import UEOT.V3.Compression.TheoryCompletion.SameObjectIdentity
import UEOT.V3.FiniteHistory

/-!
# P2.1 — Same-parent own-history carrier

P2 binds histories to an explicit parent token before any effective-state or
control construction. The underlying history semantics is the canonical UEOT
FiniteHistory.Carrier; this module only adds the identity guard.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open UEOT.V3.FiniteHistory

universe uP uX uA

/-- One finite controlled history tagged by the parent whose process history it
is claimed to be. The tag is identity data, not inferred from the history type. -/
structure ParentBoundHistory
    (Parent : Type uP) (X : Type uX) (A : Type uA) where
  parent : Parent
  history : Carrier X A

/-- Histories owned by one fixed parent token. -/
abbrev OwnHistory
    {Parent : Type uP} (parent : Parent)
    (X : Type uX) (A : Type uA) :=
  {h : ParentBoundHistory Parent X A // h.parent = parent}

/-- The time-zero history of one fixed parent. -/
def ownHistorySingleton
    {Parent : Type uP} (parent : Parent)
    {X : Type uX} {A : Type uA} (x : X) :
    OwnHistory parent X A :=
  ⟨⟨parent, Carrier.singleton (A := A) x⟩, rfl⟩

/-- Read the current physical state from the parent's own finite history. -/
def OwnHistory.current
    {Parent : Type uP} {parent : Parent}
    {X : Type uX} {A : Type uA}
    (h : OwnHistory parent X A) : X :=
  h.1.history.current

/-- Extend one parent's own history by one action/state pair while preserving
the same parent identity token. -/
def OwnHistory.advance
    {Parent : Type uP} {parent : Parent}
    {X : Type uX} {A : Type uA}
    (h : OwnHistory parent X A) (a : A) (x' : X) :
    OwnHistory parent X A :=
  ⟨⟨parent, Carrier.advance h.1.history a x'⟩, rfl⟩

@[simp] theorem ownHistorySingleton_parent
    {Parent : Type uP} (parent : Parent)
    {X : Type uX} {A : Type uA} (x : X) :
    (ownHistorySingleton parent (A := A) x).1.parent = parent :=
  rfl

@[simp] theorem OwnHistory.current_singleton
    {Parent : Type uP} (parent : Parent)
    {X : Type uX} {A : Type uA} (x : X) :
    (ownHistorySingleton parent (A := A) x).current = x := by
  rfl

@[simp] theorem OwnHistory.current_advance
    {Parent : Type uP} {parent : Parent}
    {X : Type uX} {A : Type uA}
    (h : OwnHistory parent X A) (a : A) (x' : X) :
    (h.advance a x').current = x' := by
  exact Carrier.current_advance h.1.history a x'

/-- P2.1 identity preservation: extending the process history cannot change the
owning parent token. -/
theorem OwnHistory.advance_preserves_parent
    {Parent : Type uP} {parent : Parent}
    {X : Type uX} {A : Type uA}
    (h : OwnHistory parent X A) (a : A) (x' : X) :
    (h.advance a x').1.parent = parent :=
  rfl

end UEOT.V3.Compression.TheoryCompletion
