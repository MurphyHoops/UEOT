import UEOT.V3.Compression.AgencyGodGoaAssembly

/-!
# P0.3 scratch — GOD constitution

Universal GOD semantics is set-valued/local: a correspondence of admissible
actions, policies, or directions certified as locally optimal in the declared
model.  This file instantiates that idea for the canonical finite discounted
control model without assuming uniqueness or gradient structure.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.AgencyGodGoaAssembly

universe uS uA uH

/-- Generic state-dependent local-choice correspondence.  This is the semantic
shape needed by GOD before choosing a domain-specific notion of local choice. -/
abbrev LocalChoiceCorrespondence
    (S : Type uS) (A : S → Type uA) :=
  (s : S) → Set (A s)

/-- Bellman GOD correspondence for the canonical finite discounted control
model: every action in the set attains the optimal one-step action value. -/
def BellmanGODCorrespondence
    {S : Type uS} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) :
    LocalChoiceCorrespondence S A :=
  fun s => {a | M.qValue M.optimalValue s a = M.optimalValue s}

/-- A stationary selector is GOD-compatible when it chooses an element of the
Bellman-optimal correspondence at every state. -/
def IsBellmanGODSelector
    {S : Type uS} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (selector : (s : S) → A s) : Prop :=
  ∀ s, selector s ∈ BellmanGODCorrespondence M s

@[simp] theorem mem_bellmanGODCorrespondence_iff
    {S : Type uS} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (s : S) (a : A s) :
    a ∈ BellmanGODCorrespondence M s ↔
      M.qValue M.optimalValue s a = M.optimalValue s := by
  rfl

/-- The canonical greedy action is one witness of the GOD correspondence.
Nothing here claims it is the unique witness. -/
theorem greedyAction_mem_bellmanGODCorrespondence
    {S : Type uS} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (s : S) :
    M.greedyAction s ∈ BellmanGODCorrespondence M s := by
  exact M.greedyAction_spec s

/-- Consequently every finite nonempty action model has a nonempty GOD
correspondence at every state. -/
theorem bellmanGODCorrespondence_nonempty
    {S : Type uS} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (s : S) :
    (BellmanGODCorrespondence M s).Nonempty := by
  exact ⟨M.greedyAction s, greedyAction_mem_bellmanGODCorrespondence M s⟩

/-- Membership has the expected argmax meaning: a GOD action weakly dominates
every other admissible action at that state. -/
theorem bellmanGOD_action_dominates
    {S : Type uS} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (s : S) {a : A s}
    (ha : a ∈ BellmanGODCorrespondence M s) (b : A s) :
    M.qValue M.optimalValue s b ≤ M.qValue M.optimalValue s a := by
  rw [mem_bellmanGODCorrespondence_iff] at ha
  rw [ha]
  exact M.qValue_optimal_le s b

/-- The canonical greedy selector is GOD-compatible, but the semantics remains
set-valued and permits multiple optimal selectors. -/
theorem greedyAction_isBellmanGODSelector
    {S : Type uS} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) :
    IsBellmanGODSelector M M.greedyAction := by
  intro s
  exact greedyAction_mem_bellmanGODCorrespondence M s

/-- The history-derived control model already present in canonical UEOT
therefore inherits a nonempty GOD correspondence after quotient construction.
This theorem does not claim that the history belongs to a particular Objecthood
object; that identity bridge is reserved for P2. -/
theorem historyControlSpec_has_bellmanGOD
    {H : Type uH} {S : Type uS} [Fintype S] [Nonempty S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Function.Surjective C)
    (D : HistoryControlSpec H S Act C) :
    ∀ s, (BellmanGODCorrespondence (D.toModel hC) s).Nonempty := by
  intro s
  exact bellmanGODCorrespondence_nonempty (D.toModel hC) s

end UEOT.V3.Compression.TheoryCompletion
