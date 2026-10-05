import UEOT.V3.Compression.TheoryCompletion.Purpose

/-!
# P1.0 — Object evidence does not identify purpose

This is an identifiability statement about a projection from richer
object-plus-purpose models to object evidence. It does not claim that every
purpose extension is physically realizable.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TeleologicalEquivalence

universe uO uP uM

/-- A richer model in which one exact object-evidence witness is accompanied by
one numerical purpose representation. -/
structure PurposeExtension (ObjectEvidence : Type uO) (Policy : Type uP) where
  objectEvidence : ObjectEvidence
  objective : NumericalObjective Policy

/-- An evidence projection identifies teleological purpose if any two richer
models with identical object evidence induce the same weak ordering on the
declared policy/future domain. -/
def PurposeIdentifiedByEvidence
    {Model : Type uM} {ObjectEvidence : Type uO} {Policy : Type uP}
    (objectEvidence : Model → ObjectEvidence)
    (objective : Model → NumericalObjective Policy) : Prop :=
  ∀ M N, objectEvidence M = objectEvidence N →
    PolicyOrderingEquivalent (objective M) (objective N)

/-- **P1.0 boundary.**  For any fixed object-evidence witness, the projection
that forgets the purpose representation is not purpose-identifying on the
unconstrained extension space. Therefore an additional teleological bridge is
logically necessary before Objecthood evidence can determine a choice class.

This theorem does not say that both extensions are physically realized; it says
that object evidence alone contains no theorem-level discriminator between
them. -/
theorem objectEvidence_projection_not_purposeIdentifying
    {ObjectEvidence : Type uO}
    (object : ObjectEvidence) :
    ¬ PurposeIdentifiedByEvidence
      (fun M : PurposeExtension ObjectEvidence Bool => M.objectEvidence)
      (fun M => M.objective) := by
  rcases carrier_does_not_determine_choiceRepresentationClass with
    ⟨J, K, hJK⟩
  intro hid
  let MJ : PurposeExtension ObjectEvidence Bool :=
    ⟨object, J⟩
  let MK : PurposeExtension ObjectEvidence Bool :=
    ⟨object, K⟩
  have hsame : MJ.objectEvidence = MK.objectEvidence := rfl
  have horder : PolicyOrderingEquivalent MJ.objective MK.objective :=
    hid MJ MK hsame
  have hmax : MaximizerEquivalent MJ.objective MK.objective :=
    policyOrderingEquivalent_to_maximizerEquivalent horder
  exact hJK hmax

end UEOT.V3.Compression.TheoryCompletion
