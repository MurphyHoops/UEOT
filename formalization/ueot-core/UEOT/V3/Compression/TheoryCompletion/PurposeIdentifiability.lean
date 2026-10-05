import UEOT.V3.Compression.TheoryCompletion.Purpose

/-!
# P1.0 — Purpose-identifiability boundary

This module separates two claims that must not be conflated:

1. a generic valid-model criterion for proving non-identifiability when two
   admissible models share object evidence but differ teleologically;
2. a concrete unconstrained-product witness showing that a bare evidence value
   contains no purpose coordinate by itself.

The second item is an interface-level observation, not a proof that two
physically realizable UEOT Objecthood models with the same evidence must exist.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open UEOT.V3.Compression.TeleologicalEquivalence

universe uO uP uM

/-- Unconstrained object-evidence plus numerical-purpose extension.

This product is useful for the interface-level projection boundary below, but
does not itself encode physical/model admissibility. -/
structure PurposeExtension (ObjectEvidence : Type uO) (Policy : Type uP) where
  objectEvidence : ObjectEvidence
  objective : NumericalObjective Policy

/-- Purpose identification restricted to an explicit validity predicate.

This is the scientifically relevant schema: only models satisfying the validity
predicate participate in the identifiability claim. -/
def PurposeIdentifiedByEvidenceAmongValid
    {Model : Type uM} {ObjectEvidence : Type uO} {Policy : Type uP}
    (valid : Model → Prop)
    (objectEvidence : Model → ObjectEvidence)
    (objective : Model → NumericalObjective Policy) : Prop :=
  ∀ M N, valid M → valid N → objectEvidence M = objectEvidence N →
    PolicyOrderingEquivalent (objective M) (objective N)

/-- Two valid evidence-compatible models with different weak orderings are a
complete counterexample to purpose identification on that model class. -/
theorem purpose_not_identified_of_valid_counterexample
    {Model : Type uM} {ObjectEvidence : Type uO} {Policy : Type uP}
    (valid : Model → Prop)
    (objectEvidence : Model → ObjectEvidence)
    (objective : Model → NumericalObjective Policy)
    {M N : Model}
    (hM : valid M) (hN : valid N)
    (hEvidence : objectEvidence M = objectEvidence N)
    (hOrder : ¬ PolicyOrderingEquivalent (objective M) (objective N)) :
    ¬ PurposeIdentifiedByEvidenceAmongValid
      valid objectEvidence objective := by
  intro hIdentified
  exact hOrder (hIdentified M N hM hN hEvidence)

/-- Unrestricted projection identification, retained only as the special case
where every extension is declared admissible. -/
def PurposeIdentifiedByEvidence
    {Model : Type uM} {ObjectEvidence : Type uO} {Policy : Type uP}
    (objectEvidence : Model → ObjectEvidence)
    (objective : Model → NumericalObjective Policy) : Prop :=
  PurposeIdentifiedByEvidenceAmongValid
    (fun _ => True) objectEvidence objective

/-- P1.0 interface boundary. For any fixed evidence value, forgetting the
purpose coordinate is not identifying on the unconstrained product extension.

This theorem does not establish the stronger model-theoretic claim that two
physically admissible UEOT Objecthood models with identical full evidence and
different purposes exist. That stronger claim requires an explicit validity
relation and valid witnesses, for which
purpose_not_identified_of_valid_counterexample is the reusable criterion. -/
theorem unconstrained_objectEvidence_projection_not_purposeIdentifying
    {ObjectEvidence : Type uO}
    (object : ObjectEvidence) :
    ¬ PurposeIdentifiedByEvidence
      (fun M : PurposeExtension ObjectEvidence Bool => M.objectEvidence)
      (fun M => M.objective) := by
  rcases carrier_does_not_determine_choiceRepresentationClass with
    ⟨J, K, hJK⟩
  let MJ : PurposeExtension ObjectEvidence Bool := ⟨object, J⟩
  let MK : PurposeExtension ObjectEvidence Bool := ⟨object, K⟩
  apply purpose_not_identified_of_valid_counterexample
    (valid := fun _ : PurposeExtension ObjectEvidence Bool => True)
    (objectEvidence := fun M => M.objectEvidence)
    (objective := fun M => M.objective)
    (M := MJ) (N := MK)
  · trivial
  · trivial
  · rfl
  · intro hOrder
    exact hJK (policyOrderingEquivalent_to_maximizerEquivalent hOrder)

end UEOT.V3.Compression.TheoryCompletion
