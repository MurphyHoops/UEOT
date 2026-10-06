import UEOT.V3.Compression.AgencyGodGoaAssembly

/-!
# P2.0 preflight — same control data does not imply same object

Two distinct parent identities can carry literally the same history-derived
control specification. P2 therefore needs an explicit parent-identity guard
before Objecthood and control/GOA certificates may be composed.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Function
open UEOT.V3.Compression.AgencyGodGoaAssembly
open UEOT.V3.Compression.RecursiveSufficientState

universe uP uH uS uA

/-- A history-control specification explicitly owned by one parent token. -/
structure ParentBoundHistoryControlSpec
    (Parent : Type uP)
    (H : Type uH) (S : Type uS) [Fintype S]
    (Act : Type uA) [Fintype Act] [Nonempty Act]
    (C : H → S) where
  parent : Parent
  control : HistoryControlSpec H S Act C

/-- Same-object identity at this interface is equality of the owning parent
token, not equality of the state type or the control data. -/
def SameControlParent
    {Parent : Type uP}
    {H : Type uH} {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    {C : H → S}
    (M N : ParentBoundHistoryControlSpec Parent H S Act C) : Prop :=
  M.parent = N.parent

private noncomputable def unitHistoryControlSpec :
    HistoryControlSpec Unit Unit Unit (fun _ => ()) where
  transition := fun _ _ _ => 1
  reward := fun _ _ => 0
  rewardBound := 0
  discount := 1 / 2
  transition_nonneg := by
    intro _ _ _
    norm_num
  transition_sum_one := by
    intro _ _
    simp
  reward_abs_le := by
    intro _ _
    norm_num
  discount_pos := by
    norm_num
  discount_lt_one := by
    norm_num
  sufficient := by
    intro h h' _ a
    rfl

/-- P2.0 identity-guard no-go. Even literally identical history-control data
can be attached to distinct parent identities. Hence neither a common
state/action type nor equality of the entire history-control specification
licenses a same-object composition. -/
theorem identical_historyControlSpec_does_not_imply_sameParent :
    ∃ M N :
        ParentBoundHistoryControlSpec
          Bool Unit Unit Unit (fun _ => ()),
      M.control = N.control ∧ ¬ SameControlParent M N := by
  let D := unitHistoryControlSpec
  let M :
      ParentBoundHistoryControlSpec
        Bool Unit Unit Unit (fun _ => ()) :=
    ⟨false, D⟩
  let N :
      ParentBoundHistoryControlSpec
        Bool Unit Unit Unit (fun _ => ()) :=
    ⟨true, D⟩
  refine ⟨M, N, rfl, ?_⟩
  simp [SameControlParent, M, N]

end UEOT.V3.Compression.TheoryCompletion
