import UEOT.V3.Compression.TheoryCompletion.SameObjectTeleologicalControl
import UEOT.V3.Compression.TheoryCompletion.GOD

/-!
# P2.4 preflight — GOD on the same-parent induced control model
-/

namespace UEOT.V3.Compression.TheoryCompletion

open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.AgencyGodGoaAssembly

universe uP uX uA uF

namespace ParentTeleologicalControlRealization

variable
    {Parent : Type uP} {X : Type uX} {A : Type uA}
    {Future : Type uF}

/-- Finite control model induced from the same parent's own-history dynamics and
the declared P1 teleological realization. -/
noncomputable def toControlModel
    [Fintype X] [Fintype A] [Nonempty A]
    (dynamics : Parent → X → A → PMF X)
    (R : ParentTeleologicalControlRealization Parent X A Future) :
    Model X (fun _ : X => A) :=
  (R.toHistoryControlSpec dynamics).toModel
    (ownHistoryCurrent_surjective R.parent)

@[simp] theorem toControlModel_reward
    [Fintype X] [Fintype A] [Nonempty A]
    (dynamics : Parent → X → A → PMF X)
    (R : ParentTeleologicalControlRealization Parent X A Future)
    (x : X) (a : A) :
    (R.toControlModel dynamics).reward x a =
      R.objective (R.actionFuture x a) := by
  let h : OwnHistory R.parent X A :=
    ownHistorySingleton R.parent (A := A) x
  have hreward :=
    HistoryControlSpec.toModel_reward_on_history
      (R.toHistoryControlSpec dynamics)
      (ownHistoryCurrent_surjective R.parent) h a
  simpa [toControlModel, h] using hreward

@[simp] theorem toControlModel_transition
    [Fintype X] [Fintype A] [Nonempty A]
    (dynamics : Parent → X → A → PMF X)
    (R : ParentTeleologicalControlRealization Parent X A Future)
    (x : X) (a : A) (y : X) :
    (R.toControlModel dynamics).transition x a y =
      ((dynamics R.parent x a) y).toReal := by
  let h : OwnHistory R.parent X A :=
    ownHistorySingleton R.parent (A := A) x
  have htransition :=
    HistoryControlSpec.toModel_transition_on_history
      (R.toHistoryControlSpec dynamics)
      (ownHistoryCurrent_surjective R.parent) h a y
  simpa [toControlModel, h] using htransition

/-- P2.4: the same-parent induced control model has a nonempty set-valued
Bellman GOD correspondence at every physical state. No uniqueness or gradient
representation is claimed. -/
theorem sameParent_bellmanGOD_nonempty
    [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]
    (dynamics : Parent → X → A → PMF X)
    (R : ParentTeleologicalControlRealization Parent X A Future) :
    ∀ x, (BellmanGODCorrespondence (R.toControlModel dynamics) x).Nonempty := by
  intro x
  exact bellmanGODCorrespondence_nonempty (R.toControlModel dynamics) x

/-- The canonical greedy selector is one GOD-compatible selector of the
same-parent induced model. -/
theorem sameParent_greedyAction_isBellmanGODSelector
    [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]
    (dynamics : Parent → X → A → PMF X)
    (R : ParentTeleologicalControlRealization Parent X A Future) :
    IsBellmanGODSelector
      (R.toControlModel dynamics)
      (R.toControlModel dynamics).greedyAction :=
  greedyAction_isBellmanGODSelector (R.toControlModel dynamics)

end ParentTeleologicalControlRealization

end UEOT.V3.Compression.TheoryCompletion
