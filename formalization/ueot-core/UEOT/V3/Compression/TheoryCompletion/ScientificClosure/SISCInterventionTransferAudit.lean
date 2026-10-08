import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCInterventionParentIdentification
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFormationIdentityBridge
import Mathlib.Tactic

/-!
# N6-B finite intervention + material/program-transfer candidate intersection

Reuse SI-2's proved common-observation triangle and LocalResponseGap.
This module does NOT declare a source parent in the algorithm. The
algorithm enumerates independently registered candidates and intersects
(a) an external authenticated transfer record with
(b) actually measured intervention-response compatibility.

The transfer record and intervention calibration are separate inputs,
not derived genealogical facts. A positive P8 lineage conclusion requires
an additional external soundness bridge from the authenticated record
to the intended physical genealogy.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.TheoryCompletion

universe uP uC uI uIdentity

/-- Candidate parent information is operational; 'authenticatedTransfer'
is an independently verified trace of material, program, or causal
transport into this particular child. The predicate is not created by
looking at the final selected parent. -/
structure FiniteInterventionTransferAudit
    (Parent : Type uP) (Child : Type uC) (Probe : Type uI)
    [Fintype Parent] where
  registered : Finset Parent
  authenticatedTransfer : Parent → Child → Prop
  referenceResponse : Parent → Probe → ℝ
  observedResponse : Child → Probe → ℝ
  tolerance : ℝ

/-- The actual finite audited candidate set, with no chosen transporter
or parent token in the data constructor. -/
noncomputable def auditedSourceCandidates
    {Parent : Type uP} {Child : Type uC} {Probe : Type uI}
    [Fintype Parent] [DecidableEq Parent]
    (audit : FiniteInterventionTransferAudit Parent Child Probe)
    (child : Child) : Finset Parent := by
  classical
  exact audit.registered.filter (fun parent =>
    audit.authenticatedTransfer parent child ∧
      FormedByResponse
        (fun (c : Child) (i : Probe) => audit.observedResponse c i)
        audit.referenceResponse audit.tolerance child parent)

/-- Explicit equivalence: inclusion demands both transfer provenance
and agreement with *every* registered intervention response coordinate. -/
theorem audited_source_mem_iff
    {Parent : Type uP} {Child : Type uC} {Probe : Type uI}
    [Fintype Parent] [DecidableEq Parent]
    (audit : FiniteInterventionTransferAudit Parent Child Probe)
    (child : Child) (parent : Parent) :
    parent ∈ auditedSourceCandidates audit child ↔
      parent ∈ audit.registered ∧
        audit.authenticatedTransfer parent child ∧
        FormedByResponse
          (fun (c : Child) (i : Probe) => audit.observedResponse c i)
          audit.referenceResponse audit.tolerance child parent := by
  classical
  exact Finset.mem_filter

/-- SI-2's *existing* response gap is precisely the extra witness
needed to prove any other formed candidate, with or without another
transport record, has the same parent label. -/
theorem audit_fitted_parent_unique_of_existing_gap
    {Parent : Type uP} {Child : Type uC} {Probe : Type uI}
    [Fintype Parent] [DecidableEq Parent]
    (audit : FiniteInterventionTransferAudit Parent Child Probe)
    (child : Child) (parent : Parent)
    (hfit : FormedByResponse
      (fun (c : Child) (i : Probe) => audit.observedResponse c i)
      audit.referenceResponse audit.tolerance child parent)
    (hsep : LocalResponseGap audit.referenceResponse audit.tolerance parent) :
    ∀ q, q ∈ auditedSourceCandidates audit child → q = parent := by
  intro q hq
  have hformed := (audited_source_mem_iff audit child q).1 hq |>.2.2
  exact unique_formed_target_of_local_gap
    (fun (c : Child) (i : Probe) => audit.observedResponse c i)
    audit.referenceResponse audit.tolerance child parent hfit hsep q hformed

/-- A registered, independently transfer-attested parent with a fitting
interventional signature and a strictly separating SI-2 response gap
is the *only* operationally admissible parent. The selected answer is
NOT a primitive assumption of the candidate-search routine. -/
theorem audited_source_candidates_eq_singleton_of_gap
    {Parent : Type uP} {Child : Type uC} {Probe : Type uI}
    [Fintype Parent] [DecidableEq Parent]
    (audit : FiniteInterventionTransferAudit Parent Child Probe)
    (child : Child) (parent : Parent)
    (hreg : parent ∈ audit.registered)
    (htransfer : audit.authenticatedTransfer parent child)
    (hfit : FormedByResponse
      (fun (c : Child) (i : Probe) => audit.observedResponse c i)
      audit.referenceResponse audit.tolerance child parent)
    (hsep : LocalResponseGap audit.referenceResponse audit.tolerance parent) :
    auditedSourceCandidates audit child = {parent} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨(audited_source_mem_iff audit child parent).2
    ⟨hreg, htransfer, hfit⟩, ?_⟩
  intro q hq
  exact audit_fitted_parent_unique_of_existing_gap
    audit child parent hfit hsep q hq

/-- Identifiability must fail safely when TWO genuinely distinct parents
both have transfer records and fit the observed interventions. A single
winner cannot be certified in this situation. -/
theorem two_audited_parent_matches_prevent_unique
    {Parent : Type uP} {Child : Type uC} {Probe : Type uI}
    [Fintype Parent] [DecidableEq Parent]
    (audit : FiniteInterventionTransferAudit Parent Child Probe)
    (child : Child)
    {p q : Parent}
    (hp : p ∈ auditedSourceCandidates audit child)
    (hq : q ∈ auditedSourceCandidates audit child)
    (hne : p ≠ q) :
    ∀ selected, auditedSourceCandidates audit child ≠ {selected} := by
  intro selected hsingleton
  have hsubset : auditedSourceCandidates audit child ⊆
      ({selected} : Finset Parent) := Finset.subset_of_eq hsingleton
  have hps := Finset.mem_singleton.mp (hsubset hp)
  have hqs := Finset.mem_singleton.mp (hsubset hq)
  exact hne (hps.trans hqs.symm)

/-- An independently checked audit-to-genealogy soundness statement,
NOT a consequence of response agreement, converts a singleton
operational candidate to the already defined P8 parentOf relation. -/
theorem audited_unique_to_P8_parent_of_sound_transfer
    {Parent : Type uP} {Probe : Type uI} {Identity : Type uIdentity}
    [Fintype Parent] [DecidableEq Parent]
    (audit : FiniteInterventionTransferAudit Parent Parent Probe)
    (L : LineageSemantics Parent Identity)
    (hsound : ∀ p c, audit.authenticatedTransfer p c → L.parentOf p c)
    (child parent : Parent)
    (hunique : auditedSourceCandidates audit child = {parent}) :
    L.parentOf parent child := by
  have hmem : parent ∈ auditedSourceCandidates audit child :=
    (Finset.subset_of_eq hunique.symm) (Finset.mem_singleton_self _)
  have haudit := (audited_source_mem_iff audit child parent).1 hmem
  exact hsound parent child haudit.2.1

/-- Distinct identities must still be certified separately from the
physical/material transfer log. Repair has the same identity and should
not silently count as reproduction. -/
theorem audited_unique_to_P8_offspring_of_sound_transfer
    {Parent : Type uP} {Probe : Type uI} {Identity : Type uIdentity}
    [Fintype Parent] [DecidableEq Parent]
    (audit : FiniteInterventionTransferAudit Parent Parent Probe)
    (L : LineageSemantics Parent Identity)
    (hsound : ∀ p c, audit.authenticatedTransfer p c → L.parentOf p c)
    (child parent : Parent)
    (hunique : auditedSourceCandidates audit child = {parent})
    (hnewIdentity : ¬ L.SameObject parent child) :
    L.OffspringOf parent child := by
  exact ⟨audited_unique_to_P8_parent_of_sound_transfer
    audit L hsound child parent hunique, hnewIdentity⟩

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
