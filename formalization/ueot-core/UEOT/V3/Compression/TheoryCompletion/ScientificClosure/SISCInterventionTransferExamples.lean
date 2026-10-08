import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCInterventionTransferAudit
import Mathlib.Tactic

/-!
# N6-C non-vacuity and deliberately uninformative transfer record

Two registered parent tokens both have authenticated/admissible transfer
records (the toy record is deliberately permissive and does not
distinguish sources). Under passive-only observation both remain
possible. Once the active intervention probe is registered, only
parent false remains. This tests the separation hypothesis instead
of relying on a singleton provenance registry.

Finally a separately declared P8 genealogy and different identity
map are required before upgrading a selected source to offspring.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.TheoryCompletion

def n6ActiveTransferAudit :
    FiniteInterventionTransferAudit Bool Bool Bool where
  registered := Finset.univ
  authenticatedTransfer := fun _ _ => True
  referenceResponse := n6ParentProbe
  observedResponse := fun _ probe => n6ParentProbe false probe
  tolerance := 0

def n6PassiveTransferAudit :
    FiniteInterventionTransferAudit Bool Bool PUnit where
  registered := Finset.univ
  authenticatedTransfer := fun _ _ => True
  referenceResponse := fun _ _ => 0
  observedResponse := fun _ _ => 0
  tolerance := 0

theorem n6_active_true_source_fits :
    FormedByResponse
      (fun (c : Bool) (i : Bool) => n6ActiveTransferAudit.observedResponse c i)
      n6ActiveTransferAudit.referenceResponse
      n6ActiveTransferAudit.tolerance true false := by
  intro i
  simp [n6ActiveTransferAudit]

theorem n6_active_local_gap :
    LocalResponseGap n6ActiveTransferAudit.referenceResponse
      n6ActiveTransferAudit.tolerance false := by
  intro q hne
  cases q
  · exact False.elim (hne rfl)
  · refine ⟨true, ?_⟩
    norm_num [n6ActiveTransferAudit, n6ParentProbe]

/-- Even when the external transfer records admit BOTH parents, the
intervention response is sufficiently separating to certify one parent. -/
theorem n6_active_transfer_selection_singleton :
    auditedSourceCandidates n6ActiveTransferAudit true = {false} := by
  apply audited_source_candidates_eq_singleton_of_gap
    n6ActiveTransferAudit true false
  · simp [n6ActiveTransferAudit]
  · trivial
  · exact n6_active_true_source_fits
  · exact n6_active_local_gap

/-- Registered source candidates are *not* individually identifiable if
the intervention family only contains the passive/non-separating probe,
even with exact response measurements and transfer records. -/
theorem n6_passive_transfer_selection_has_two_sources :
    false ∈ auditedSourceCandidates n6PassiveTransferAudit true ∧
    true ∈ auditedSourceCandidates n6PassiveTransferAudit true := by
  constructor
  · rw [audited_source_mem_iff]
    constructor
    · simp [n6PassiveTransferAudit]
    constructor
    · trivial
    · intro i
      simp [n6PassiveTransferAudit]
  · rw [audited_source_mem_iff]
    constructor
    · simp [n6PassiveTransferAudit]
    constructor
    · trivial
    · intro i
      simp [n6PassiveTransferAudit]

theorem n6_passive_cannot_certify_unique_parent :
    ∀ parent : Bool,
      auditedSourceCandidates n6PassiveTransferAudit true ≠ {parent} := by
  obtain ⟨hf, ht⟩ := n6_passive_transfer_selection_has_two_sources
  exact two_audited_parent_matches_prevent_unique
    n6PassiveTransferAudit true hf ht Bool.false_ne_true

/-- Toy lineage semantics is explicitly an interpretation supplied
SEPARATELY from both the transfer ledger and observations. Its permissive
parentOf relation is not claimed to be real-world genealogy. -/
def n6ToyLineage : LineageSemantics Bool Bool where
  identity := id
  parentOf := fun _ _ => True

/-- Even the non-vacuous positive P8 conclusion requires the toy's
separate audit-to-lineage soundness mapping AND an identity difference. -/
theorem n6_active_audit_to_toy_offspring :
    n6ToyLineage.OffspringOf false true := by
  apply audited_unique_to_P8_offspring_of_sound_transfer
    n6ActiveTransferAudit n6ToyLineage
    (by intro _ _ _; trivial)
    true false n6_active_transfer_selection_singleton
  simp [LineageSemantics.SameObject, n6ToyLineage]

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
