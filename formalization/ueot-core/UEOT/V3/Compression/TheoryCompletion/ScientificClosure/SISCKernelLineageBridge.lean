import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCCausalLineageNoGo
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCSeparationPower
import Mathlib.Tactic

/-!
# SISC N5 — typed positive-mass intervention → P8 lineage interface

The process-generated *reachability predicate* is derived from the
already registered finite controlled kernel: candidate c is admitted
only if K(source,action,c)>0.  This removes a chosen successor and an
arbitrary causal-admissibility oracle from the **operational N3 resolver**
for the special case where a candidate is a microscopic next state.

The P8 interpretation of those transitions as *genealogical parent edges*
remains a separately required CompatibleTransmission proof. The preceding
SISCCausalLineageNoGo establishes why this premise cannot be inferred from
the kernel or full current-state readout alone.

No P12 actual parent map, repaired identity, candidate universe
completeness, or reproductive program synthesis is fabricated.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.TheoryCompletion

universe uX uA uO uI

/-- A finite microstate candidate family whose eligibility is derived from
the *actual positive transition mass* to the proposed next token. The
observations/predictions, thresholds and C2 calibrations are preserved
exactly from P; only its previously user-supplied causal predicate is
replaced with this operational stochastic-support condition. -/
noncomputable def supportAdmittedProtocol
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype O]
    (P : RegisteredCausalCandidateProtocol X A X O) :
    RegisteredCausalCandidateProtocol X A X O :=
  { P with causal := fun c => 0 < P.kernel.mass P.source P.action c }

/-- Candidate eligibility now has an explicit process-based soundness
condition; it is not simply assumed by calling the candidate 'causal'. -/
theorem support_admitted_candidate_has_positive_transition
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq X]
    (P : RegisteredCausalCandidateProtocol X A X O)
    (c : X)
    (hpossible : c ∈ registeredPossible (supportAdmittedProtocol P)) :
    0 < P.kernel.mass P.source P.action c := by
  classical
  exact (Finset.mem_filter.mp hpossible).2.1

/-- The new finite search still uses N3's original registered risk and
per-candidate C2 intervals; no evidence quality is strengthened by the
mere substitution of positive transition support. -/
theorem support_admitted_risk_eq_original
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype O]
    (P : RegisteredCausalCandidateProtocol X A X O) (c : X) :
    registeredCandidateRisk (supportAdmittedProtocol P) c =
      registeredCandidateRisk P c := rfl

/-- A process-supported unique candidate is **operationally** certified
without any selected tp, under the existing simultaneous C2 calibration
event. This is an *actual* process next-state statement: positive mass,
registered response compatibility and registered-family uniqueness. -/
theorem support_admitted_unique_operational_successor
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq X]
    (P : RegisteredCausalCandidateProtocol X A X O)
    (hcal : (supportAdmittedProtocol P).Calibrated)
    (c : X)
    (hout : resolveRegisteredCandidates (supportAdmittedProtocol P) =
      .unique c) :
    0 < P.kernel.mass P.source P.action c ∧
    (supportAdmittedProtocol P).TrulyCompatible c ∧
    ∀ d, (supportAdmittedProtocol P).TrulyCompatible d → d = c := by
  obtain ⟨hc, hunique⟩ :=
    unique_resolution_sound (supportAdmittedProtocol P) hcal c hout
  exact ⟨hc.2.1, hc, hunique⟩

/-- P8 already defines what it means for a **reproductive** stochastic
transmission channel to be compatible with an independently registered
genealogy. Here the exact N1 microstate kernel at the registered action is
used as P8's transmission channel. -/
def P8LineageCompatibleAtAction
    {X : Type uX} {A : Type uA} {O : Type uO} {Identity : Type uI}
    [Fintype X] [Fintype O]
    (P : RegisteredCausalCandidateProtocol X A X O)
    (L : LineageSemantics X Identity) : Prop :=
  L.CompatibleTransmission (fun x y => P.kernel.mass x P.action y)

/-- A derived supported successor can be called a *genealogical parent
edge* only when the **independently checked P8 compatibility** holds.
Without hlineage this conclusion is invalid by the N5 no-go. -/
theorem support_admitted_unique_compatible_parent_edge
    {X : Type uX} {A : Type uA} {O : Type uO} {Identity : Type uI}
    [Fintype X] [Fintype O] [DecidableEq X]
    (P : RegisteredCausalCandidateProtocol X A X O)
    (L : LineageSemantics X Identity)
    (hlineage : P8LineageCompatibleAtAction P L)
    (hcal : (supportAdmittedProtocol P).Calibrated)
    (c : X)
    (hout : resolveRegisteredCandidates (supportAdmittedProtocol P) =
      .unique c) :
    L.parentOf P.source c ∧
    (supportAdmittedProtocol P).TrulyCompatible c ∧
    ∀ d, (supportAdmittedProtocol P).TrulyCompatible d → d = c := by
  obtain ⟨hpos, hc, hunique⟩ :=
    support_admitted_unique_operational_successor P hcal c hout
  exact ⟨hlineage P.source c hpos, hc, hunique⟩

/-- Stronger P8's ReproductiveTransmission certificate directly certifies
offspring at the derived positive-mass successor; it already includes the
essential identity inequality that makes reproduction different from repair. -/
theorem support_admitted_unique_compatible_offspring
    {X : Type uX} {A : Type uA} {O : Type uO} {Identity : Type uI}
    [Fintype X] [Fintype O] [DecidableEq X]
    (P : RegisteredCausalCandidateProtocol X A X O)
    (L : LineageSemantics X Identity)
    (hlineage : L.ReproductiveTransmission
      (fun x y => P.kernel.mass x P.action y))
    (hcal : (supportAdmittedProtocol P).Calibrated)
    (c : X)
    (hout : resolveRegisteredCandidates (supportAdmittedProtocol P) =
      .unique c) :
    L.OffspringOf P.source c ∧
    ¬ L.SameObject P.source c := by
  obtain ⟨hpos, _, _⟩ :=
    support_admitted_unique_operational_successor P hcal c hout
  have hoff := hlineage P.source c hpos
  exact ⟨hoff, hoff.2⟩

/-- The P8 negative repair/offspring distinction remains preserved after
N3 operational inference; it is not reconstructed from an output label. -/
theorem support_admitted_offspring_excludes_same_object_repair
    {X : Type uX} {A : Type uA} {O : Type uO} {Identity : Type uI}
    [Fintype X] [Fintype O] [DecidableEq X]
    (P : RegisteredCausalCandidateProtocol X A X O)
    (L : LineageSemantics X Identity)
    (hlineage : L.ReproductiveTransmission
      (fun x y => P.kernel.mass x P.action y))
    (hcal : (supportAdmittedProtocol P).Calibrated)
    (c : X)
    (hout : resolveRegisteredCandidates (supportAdmittedProtocol P) =
      .unique c) :
    ¬ L.SameObject P.source c := by
  exact (support_admitted_unique_compatible_offspring
    P L hlineage hcal c hout).2

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
