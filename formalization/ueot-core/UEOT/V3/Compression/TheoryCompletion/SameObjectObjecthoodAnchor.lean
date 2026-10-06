import UEOT.V3.Compression.TheoryCompletion.SameObjectGOD
import UEOT.V3.Compression.TheoryCompletion.OperationalObject

/-!
# P2 object anchor

Specialize the generic parent-bound control layer to the canonical Objecthood
selected parent. No parent-equality hypothesis is stored: the generic parent is
definitionally fixed to C.repairing.operational.parent.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set MeasureTheory ProbabilityTheory
open UEOT.V3
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.Objecthood

universe uV uChild uH uProbe uR uY uE uZ uX uA uC uS uF

noncomputable section

variable {V : Type uV} {Child : Type uChild}
variable {H : Type uH} {Probe : Type uProbe}
variable {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
variable {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace (ConstitutiveState X A)]
variable [MeasurableSingletonClass (ConstitutiveState X A)]
variable {Csem : Type uC}
variable {Ssem : Type uS} [Fintype Ssem] [Nonempty Ssem]
variable {Future : Type uF}
noncomputable local instance objecthoodAnchorSemanticDecidableEq :
    DecidableEq Ssem :=
  Classical.decEq Ssem

/-- Teleological data attached specifically to one canonical Objecthood package.

Unlike ParentTeleologicalControlRealization, this type has no free parent field.
Its generic realization is constructed definitionally at the selected
Objecthood parent. -/
structure ObjecthoodTeleologicalControlSpec
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (C : SemanticallyStableSelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)
    (Future : Type uF) where
  contract : TeleologicalContract Future
  actionFuture :
    X → A → AdmissibleFuture contract.admissible
  objective :
    NumericalObjective (AdmissibleFuture contract.admissible)
  objective_represents :
    ObjectiveRepresentsContract contract objective
  rewardBound : ℝ
  reward_abs_le :
    ∀ x a, |objective (actionFuture x a)| ≤ rewardBound
  discount : ℝ
  discount_pos : 0 < discount
  discount_lt_one : discount < 1

namespace ObjecthoodTeleologicalControlSpec

variable [Fintype Child]
variable
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (C : SemanticallyStableSelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)

/-- Forget only the Objecthood specialization. The generic parent field is
filled definitionally by the exact selected operational parent. -/
def toParentRealization
    (R : ObjecthoodTeleologicalControlSpec C Future) :
    ParentTeleologicalControlRealization
      (FormedCandidate readout p regions) X A Future where
  parent := C.repairing.operational.parent
  contract := R.contract
  actionFuture := R.actionFuture
  objective := R.objective
  objective_represents := R.objective_represents
  rewardBound := R.rewardBound
  reward_abs_le := R.reward_abs_le
  discount := R.discount
  discount_pos := R.discount_pos
  discount_lt_one := R.discount_lt_one

@[simp] theorem toParentRealization_parent
    (R : ObjecthoodTeleologicalControlSpec C Future) :
    (R.toParentRealization C).parent =
      C.repairing.operational.parent :=
  rfl

/-- The exact same Objecthood parent owns the P2 history carrier. -/
abbrev OwnObjectHistory
    (R : ObjecthoodTeleologicalControlSpec C Future) :=
  OwnHistory (R.toParentRealization C).parent X A

/-- The selected Objecthood parent remains in the Track-X semantic fibre used
by the same Objecthood certificate. -/
theorem selected_parent_semantic_identity
    (R : ObjecthoodTeleologicalControlSpec C Future) :
    SemanticFiberIdentity
      pi (R.toParentRealization C).parent C.semantic.child := by
  simpa [toParentRealization] using
    semanticallyStableParent_identity C

/-- The induced control transition is exactly the physical dynamics of the
canonical selected Objecthood parent. -/
@[simp] theorem toControlModel_transition_selectedParent
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (x : X) (a : A) (y : X) :
    ((R.toParentRealization C).toControlModel dynamics).transition x a y =
      ((dynamics C.repairing.operational.parent x a) y).toReal := by
  exact
    ParentTeleologicalControlRealization.toControlModel_transition
      dynamics (R.toParentRealization C) x a y

/-- The induced reward remains the explicitly contract-valid objective of this
Objecthood-specialized realization. -/
@[simp] theorem toControlModel_reward_selectedParent
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (x : X) (a : A) :
    ((R.toParentRealization C).toControlModel dynamics).reward x a =
      R.objective (R.actionFuture x a) := by
  exact
    ParentTeleologicalControlRealization.toControlModel_reward
      dynamics (R.toParentRealization C) x a

end ObjecthoodTeleologicalControlSpec

end

end UEOT.V3.Compression.TheoryCompletion
