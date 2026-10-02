import UEOT.V3.Compression.CrossTrack.EndogenousCandidateFormation
import UEOT.V3.Compression.CrossTrack.EndogenousConstitutivePersistence

/-!
# Operational synthesis: formed + identifiable + constitutively persistent

This module joins the two remaining post-Interaction research branches without
renaming the result as full UEOT Objecthood.

Formation is supplied by response-generated exact physical carriers and the
P-COMP-06 child-coalition lift.  Identification is supplied by the finite
interaction-response separation layer.  Persistence is supplied by a
nonvacuous P-PER-03 viability kernel whose preserving controller has been
embedded into reflexive state, leaving only `Unit` as the external action.

The resulting certificate is deliberately called *operational*: the internal
controller is synthesized and initialized, but the present constitutive lift
does not construct or repair that controller.  Full Omega-loop Objecthood
therefore remains stronger.
-/

namespace UEOT.V3.Compression.CrossTrack

open MeasureTheory
open UEOT.V3
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.CompositionCarrierLift
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityStrategy

universe uV uChild uH uProbe uR uY uE uZ uX uA

noncomputable section

variable {V : Type uV} {Child : Type uChild}
variable {H : Type uH} {Probe : Type uProbe}
variable {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
variable {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace (ConstitutiveState X A)]
variable [MeasurableSingletonClass (ConstitutiveState X A)]

/-- A parent certificate joining generated provenance, family-wide interaction
identifiability, and one nonvacuous autonomous constitutive persistence
witness for the selected formed parent. -/
structure OperationalFormedPersistentParent
    [Fintype Child]
    (readout : Finset V → H → Rout)
    (p : H → Probe → Measure Y)
    (regions : Child → Finset V)
    (response : Finset Child → E → Measure Z)
    (hprob : ∀ S e, IsProbabilityMeasure (response S e))
    (probes : Finset E)
    (dynamics : FormedCandidate readout p regions → X → A → PMF X)
    (persistenceDomain : FormedCandidate readout p regions → Set X) where
  parent : FormedCandidate readout p regions
  probes_nonempty : probes.Nonempty
  separating : PairwiseInteractionSeparating
    (formedCandidateResponseFamily readout p regions response hprob) probes
  persistence : ConstitutivePersistenceCertificate
    (dynamics parent) (persistenceDomain parent)

/-- Formation provenance is not a separate assumption in the operational
certificate: it follows definitionally from the selected parent's subtype. -/
theorem OperationalFormedPersistentParent.parent_mem_generatedFamily
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    (C : OperationalFormedPersistentParent
      readout p regions response hprob probes dynamics persistenceDomain) :
    C.parent.1 ∈ responseFormedCandidateFamily readout p regions :=
  C.parent.2

/-- For a genuinely nontrivial generated candidate family, the operational
certificate gives a positive quantitative interaction-identification margin. -/
theorem OperationalFormedPersistentParent.interactionIsolation_pos
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    [Nontrivial (FormedCandidate readout p regions)]
    (C : OperationalFormedPersistentParent
      readout p regions response hprob probes dynamics persistenceDomain) :
    0 < interactionIsolationConorm
      (formedCandidateResponseFamily readout p regions response hprob)
      probes C.probes_nonempty := by
  exact (formedCandidate_interactionIsolation_pos_iff
    readout p regions response hprob probes C.probes_nonempty).2 C.separating

/-- **Operational formation + identification + persistence synthesis.**

One zero-defect lower-level carrier seed and child-region coverage generate a
nonempty candidate family.  If the chosen finite probe family separates all
generated candidates and every formed candidate has a nonempty P-PER-03
winning set for its own dynamics, then at least one generated candidate admits
an operational formed-persistent-parent certificate. -/
theorem exists_operationalFormedPersistentParent_of_responseSeed
    [Fintype Child] [Nonempty A]
    (readout : Finset V → H → Rout)
    (p : H → Probe → Measure Y)
    (regions : Child → Finset V)
    (S0 : Finset V)
    (hzero : UEOT.V3.StatisticalDefect.responseDefect readout p S0 = 0)
    (hcoverSeed : coalitionCovers regions S0 Finset.univ)
    (response : Finset Child → E → Measure Z)
    (hprob : ∀ S e, IsProbabilityMeasure (response S e))
    (probes : Finset E) (hprobes : probes.Nonempty)
    (hsep : PairwiseInteractionSeparating
      (formedCandidateResponseFamily readout p regions response hprob) probes)
    (dynamics : FormedCandidate readout p regions → X → A → PMF X)
    (persistenceDomain : FormedCandidate readout p regions → Set X)
    (hwin : ∀ parent : FormedCandidate readout p regions,
      (winningSet (dynamics parent) (persistenceDomain parent)).Nonempty) :
    Nonempty (OperationalFormedPersistentParent
      readout p regions response hprob probes dynamics persistenceDomain) := by
  rcases responseFormedCandidateFamily_nonempty_of_zeroDefectSeed
      readout p regions S0 hzero hcoverSeed with ⟨S, hS⟩
  let parent : FormedCandidate readout p regions := ⟨S, hS⟩
  rcases exists_constitutivePersistenceCertificate_of_nonempty_winningSet
      (dynamics parent) (persistenceDomain parent) (hwin parent) with
    ⟨hpersist⟩
  exact ⟨{
    parent := parent
    probes_nonempty := hprobes
    separating := hsep
    persistence := hpersist
  }⟩

/-- **Objecthood boundary.**  The operational certificate cannot by itself
erase the self-repair limitation of the current constitutive lift: a corrupted
controller remains corrupted along every one-step support transition. -/
theorem operationalPersistence_does_not_supply_controller_repair
    (P : X → A → PMF X) (x : X)
    (controller target : X → A) (hne : controller ≠ target) :
    StaysIn (constitutiveLift P (x, controller) ())
      {z : ConstitutiveState X A | z.2 ≠ target} :=
  constitutiveLift_wrong_controller_stays_wrong P x controller target hne

end

end UEOT.V3.Compression.CrossTrack
