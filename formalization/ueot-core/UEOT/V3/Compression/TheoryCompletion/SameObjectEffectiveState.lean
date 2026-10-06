import UEOT.V3.Compression.TheoryCompletion.SameObjectHistory

/-!
# P2.2 — Endogenous effective state from the same parent's own history

The effective control state is not an externally supplied encoder. For one
fixed parent token, the canonical current-state readout of that parent's own
FiniteHistory carrier is surjective onto the physical state type, and the
history response is exactly the same parent's transition law.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Function
open UEOT.V3.Compression.RecursiveSufficientState

universe uP uX uA

/-- Every physical state is represented by a time-zero own-history of the same
parent. -/
theorem ownHistoryCurrent_surjective
    {Parent : Type uP} (parent : Parent)
    {X : Type uX} {A : Type uA} :
    Surjective
      (OwnHistory.current :
        OwnHistory parent X A → X) := by
  intro x
  exact ⟨ownHistorySingleton parent (A := A) x, rfl⟩

/-- History-level next-state response of one fixed parent. -/
def parentHistoryTransitionResponse
    {Parent : Type uP} {X : Type uX} {A : Type uA}
    (dynamics : Parent → X → A → PMF X)
    (parent : Parent) :
    OwnHistory parent X A → A → PMF X :=
  fun h a => dynamics parent h.current a

/-- The same parent's transition response is sufficient through its own current
physical state. -/
theorem parentHistoryTransitionResponse_compatible
    {Parent : Type uP} {X : Type uX} {A : Type uA}
    (dynamics : Parent → X → A → PMF X)
    (parent : Parent) :
    InputFiberCompatible
      (OwnHistory.current :
        OwnHistory parent X A → X)
      (parentHistoryTransitionResponse dynamics parent) := by
  intro h h' hcurrent a
  simp only [parentHistoryTransitionResponse]
  rw [hcurrent]

/-- P2.2 exact closure: the current physical state of the same parent's own
history uniquely carries that parent's next-state response.

No unrelated encoder or independently supplied transition model appears in the
statement. -/
theorem existsUnique_parentDynamics_effectiveResponse
    {Parent : Type uP} {X : Type uX} {A : Type uA}
    (dynamics : Parent → X → A → PMF X)
    (parent : Parent) :
    ∃! U : X → A → PMF X,
      ∀ h a,
        U h.current a =
          parentHistoryTransitionResponse dynamics parent h a := by
  exact existsUnique_ambientUpdate_of_surjective
    (OwnHistory.current :
      OwnHistory parent X A → X)
    (ownHistoryCurrent_surjective parent)
    (parentHistoryTransitionResponse dynamics parent)
    (parentHistoryTransitionResponse_compatible dynamics parent)

/-- The original parent-owned transition law is the canonical witness of the
P2.2 state-level response. -/
theorem parentDynamics_realizes_ownHistoryResponse
    {Parent : Type uP} {X : Type uX} {A : Type uA}
    (dynamics : Parent → X → A → PMF X)
    (parent : Parent)
    (h : OwnHistory parent X A) (a : A) :
    dynamics parent h.current a =
      parentHistoryTransitionResponse dynamics parent h a :=
  rfl

end UEOT.V3.Compression.TheoryCompletion
