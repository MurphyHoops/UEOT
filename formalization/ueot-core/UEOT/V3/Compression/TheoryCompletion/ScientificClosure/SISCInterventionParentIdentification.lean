import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCKernelLineageBridge
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFormationIdentityBridge
import UEOT.V3.Compression.TheoryCompletion.InverseObjecthood.NonIdentifiabilityBoundaries
import Mathlib.Tactic

/-!
# N6-A: A registered intervention can separate parental response models
# even when passive observational signatures are identical.

This deliberately reuses P4's validity-aware identifiability and the
already proved SI-2 formed-target response triangle, rather than proving
an independent generic evidence-injectivity theorem.

'Probe = false' is a passive condition; 'Probe = true' represents a
registered parent-specific intervention, not a physical intervention
enforced by Lean. Experimental fidelity and causal interpretation of
the probe remain independent assumptions.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.TheoryCompletion.InverseObjecthood

/-- A toy interventional readout: both parent hypotheses agree under
passive observation; active intervention exposes a different response. -/
def n6ParentProbe (parent probe : Bool) : ℝ :=
  if probe then (if parent then 1 else 0) else 0

theorem n6_passive_parent_alias :
    n6ParentProbe false false = n6ParentProbe true false := by
  rfl

theorem n6_active_parent_separates :
    n6ParentProbe false true ≠ n6ParentProbe true true := by
  norm_num [n6ParentProbe]

/-- Reuses already formalized inverse-Objecthood no-go, now with both
parents known to have exactly the same passive observation but a
different response under the registered active probe. -/
theorem n6_passive_observation_cannot_identify_parent :
    ¬ ObjectClassIdentifiedByEvidenceAmongValid
      (fun _ : Bool => True)
      (fun p : Bool => n6ParentProbe p false)
      (equalitySetoid Bool) := by
  exact literalCandidate_not_identified_of_valid_sameEvidence
    (fun _ : Bool => True)
    (fun p : Bool => n6ParentProbe p false)
    (ha := trivial) (hb := trivial)
    n6_passive_parent_alias Bool.false_ne_true

/-- After adding the active probe, the two registered *model labels*
are identifiable; this says nothing by itself about the physical
meaning or fidelity of the active intervention. -/
theorem n6_active_probe_identifies_parent_labels :
    ObjectClassIdentifiedByEvidenceAmongValid
      (fun _ : Bool => True)
      (fun p : Bool => n6ParentProbe p true)
      (equalitySetoid Bool) := by
  intro p q _ _ h
  cases p <;> cases q <;>
    simp_all [n6ParentProbe, EvidenceEquivalent]

/-- Active intervention makes the previously hidden parent classes
response-separated, while passive-only identification provably fails. -/
theorem n6_intervention_changes_operational_identifiability :
    (¬ ObjectClassIdentifiedByEvidenceAmongValid
      (fun _ : Bool => True)
      (fun p : Bool => n6ParentProbe p false)
      (equalitySetoid Bool)) ∧
    ObjectClassIdentifiedByEvidenceAmongValid
      (fun _ : Bool => True)
      (fun p : Bool => n6ParentProbe p true)
      (equalitySetoid Bool) :=
  ⟨n6_passive_observation_cannot_identify_parent,
   n6_active_probe_identifies_parent_labels⟩

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
