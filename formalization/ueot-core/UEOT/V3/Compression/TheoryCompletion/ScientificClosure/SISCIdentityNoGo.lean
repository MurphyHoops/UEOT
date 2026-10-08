import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C4SetValuedFBT

/-!
# SISC SI-1: observational identity and genealogy no-go

None of these witnesses assumes a `SameObject` primitive. They demonstrate
that an independently observed response map and a causal edge relation do not
in general identify unique ontic tokens, parents or successors.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

/-- Operational equivalence under the declared response map, not token identity. -/
def ObservationallyEquivalent {Token Response : Type*}
    (response : Token → Response) (a b : Token) : Prop :=
  response a = response b

/-- Even *exact* equality of all observations cannot imply equality of tokens
without response injectivity. A one-element response space is sufficient. -/
theorem equal_response_does_not_force_token_identity :
    ∃ (response : Bool → PUnit) (a b : Bool),
      a ≠ b ∧ ObservationallyEquivalent response a b := by
  refine ⟨fun _ => PUnit.unit, false, true, Bool.false_ne_true, ?_⟩
  rfl

/-- Two identity assignments can agree on the **entire** accessible response
process yet disagree whether the very same pair of physical tokens is one
object. The physical/operational evidence must not be used to choose an
identity map after inspecting the answer. -/
theorem response_cannot_identify_sameObject_semantics :
    ∃ (response : Bool → PUnit) (splitId mergeId : Bool → Bool),
      (∀ x y, response x = response y) ∧
      splitId false ≠ splitId true ∧
      mergeId false = mergeId true := by
  refine ⟨fun _ => PUnit.unit, id, (fun _ => false), ?_, ?_, ?_⟩
  · intro x y
    rfl
  · exact Bool.false_ne_true
  · rfl

/-- Causal provenance (an edge between times) is distinct from successor
uniqueness. A genuine one-to-many edge relation permits clone/split. -/
theorem causal_edge_alone_does_not_force_unique_successor :
    ∃ (edge : PUnit → Bool → Prop) (source : PUnit)
      (left right : Bool),
      edge source left ∧ edge source right ∧ left ≠ right := by
  exact ⟨fun _ _ => True, PUnit.unit, false, true,
    trivial, trivial, Bool.false_ne_true⟩

/-- Equally, a many-to-one event permits a fusion/merge with two different
predecessors. This is one source of lineage ambiguity. -/
theorem causal_edge_alone_does_not_force_unique_predecessor :
    ∃ (edge : Bool → PUnit → Prop) (left right : Bool)
      (target : PUnit),
      edge left target ∧ edge right target ∧ left ≠ right := by
  exact ⟨fun _ _ => True, false, true, PUnit.unit,
    trivial, trivial, Bool.false_ne_true⟩

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
