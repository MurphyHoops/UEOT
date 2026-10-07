import UEOT.V3.Compression.TheoryCompletion.OperationalObject

/-!
# P4.4 — operational validity gates

Inverse selection and Objecthood certification are different operations.
Selecting a candidate because its declared evidence fits the data does not by
itself prove that the candidate was formed by the object mechanism, is
interaction-delimited, persists, repairs, or belongs to the certified semantic
fibre.

This module packages the P0 operational predicates into explicit, layered
validity certificates for response-generated formed candidates.  No new
physical or semantic law is introduced: each constructor theorem is a thin
adapter from already canonical Track-X / Track-O / P0 certificate structures.

The hierarchy is intentionally strict:

* `FormedCandidateOperationalValidity`: provenance + delimitation + persistence;
* `RecoverableFormedCandidateValidity`: additionally physical recoverability on
  an explicit target/basin;
* `SemanticRecoverableFormedCandidateValidity`: additionally typed semantic
  fibre identity.

P4 selection theorems may identify only among candidates for which the declared
validity layer has actually been supplied or separately estimated.
-/

namespace UEOT.V3.Compression.TheoryCompletion.InverseObjecthood

open MeasureTheory
open UEOT.V3
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.TheoryCompletion

universe uV uChild uH uProbe uR uY uE uZ uX uA uC

/-- Base operational validity for one response-generated formed candidate. -/
structure FormedCandidateOperationalValidity
    {V : Type uV} {Child : Type uChild} [Fintype Child]
    {H : Type uH} {Probe : Type uProbe}
    {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
    {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (readout : Finset V → H → Rout)
    (p : H → Probe → Measure Y)
    (regions : Child → Finset V)
    (response : Finset Child → E → Measure Z)
    (hprob : ∀ S e, IsProbabilityMeasure (response S e))
    (probes : Finset E)
    (dynamics : FormedCandidate readout p regions → X → A → PMF X)
    (persistenceDomain : FormedCandidate readout p regions → Set X)
    (candidate : FormedCandidate readout p regions) : Prop where
  provenance : FormedProvenance
    (responseFormedCandidateFamily readout p regions) candidate.1
  interactionDelimited : InteractionDelimitedAt
    (formedCandidateResponseFamily readout p regions response hprob)
    probes candidate
  persistence : ConstitutivelyPersists
    (dynamics candidate) (persistenceDomain candidate)

/-- Recoverable validity adds a separately declared target and repair basin.
The basin is not silently enlarged to the full state space. -/
structure RecoverableFormedCandidateValidity
    {V : Type uV} {Child : Type uChild} [Fintype Child]
    {H : Type uH} {Probe : Type uProbe}
    {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
    {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (readout : Finset V → H → Rout)
    (p : H → Probe → Measure Y)
    (regions : Child → Finset V)
    (response : Finset Child → E → Measure Z)
    (hprob : ∀ S e, IsProbabilityMeasure (response S e))
    (probes : Finset E)
    (dynamics : FormedCandidate readout p regions → X → A → PMF X)
    (persistenceDomain : FormedCandidate readout p regions → Set X)
    (candidate : FormedCandidate readout p regions)
    (target basin : Set X) : Prop
    extends FormedCandidateOperationalValidity
      readout p regions response hprob probes dynamics persistenceDomain candidate where
  recoverable : PhysicallyRecoverableOn (dynamics candidate) target basin

/-- Semantic hardening adds only the typed fibre-identity statement supplied by
P0.  It does not manufacture the separate robust semantic-kernel certificate. -/
structure SemanticRecoverableFormedCandidateValidity
    {V : Type uV} {Child : Type uChild} [Fintype Child]
    {H : Type uH} {Probe : Type uProbe}
    {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
    {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    {Csem : Type uC}
    (readout : Finset V → H → Rout)
    (p : H → Probe → Measure Y)
    (regions : Child → Finset V)
    (response : Finset Child → E → Measure Z)
    (hprob : ∀ S e, IsProbabilityMeasure (response S e))
    (probes : Finset E)
    (dynamics : FormedCandidate readout p regions → X → A → PMF X)
    (persistenceDomain : FormedCandidate readout p regions → Set X)
    (candidate : FormedCandidate readout p regions)
    (target basin : Set X)
    (pi : FormedCandidate readout p regions → Csem)
    (child : Csem) : Prop
    extends RecoverableFormedCandidateValidity
      readout p regions response hprob probes dynamics persistenceDomain
      candidate target basin where
  semanticIdentity : SemanticFiberIdentity pi candidate child

/-- The canonical Track-X operational parent supplies exactly the base P4
validity gate; inverse selection need not re-prove these constituents. -/
theorem operationalParent_validity
    {V : Type uV} {Child : Type uChild} [Fintype Child]
    {H : Type uH} {Probe : Type uProbe}
    {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
    {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
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
    FormedCandidateOperationalValidity
      readout p regions response hprob probes dynamics persistenceDomain C.parent := by
  rcases operationalParent_constituents C with ⟨hprov, hinteraction, hpersist⟩
  exact ⟨hprov, hinteraction, hpersist⟩

/-- A self-repairing parent with a nonempty certified repair basin supplies the
recoverable P4 validity layer on the exact same selected parent. -/
theorem selfRepairingParent_validity
    {V : Type uV} {Child : Type uChild} [Fintype Child]
    {H : Type uH} {Probe : Type uProbe}
    {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
    {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    (C : SelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain)
    (hbasin : C.physicalRepair.basin.Nonempty) :
    RecoverableFormedCandidateValidity
      readout p regions response hprob probes dynamics persistenceDomain
      C.operational.parent C.operational.persistence.K C.physicalRepair.basin := by
  refine ⟨operationalParent_validity C.operational, ?_⟩
  exact selfRepairingParent_recoverability C hbasin

/-- The hardened semantic/self-repair package supplies the full P4 validity
layer, but only after the physical repair basin is explicitly known nonempty.
`[DecidableEq Ssem]` is only the finite-matrix indexing requirement inherited
from the canonical semantic-kernel package, not an additional scientific
identifiability assumption. -/
theorem semanticallyStableParent_validity
    {V : Type uV} {Child : Type uChild} [Fintype Child]
    {H : Type uH} {Probe : Type uProbe}
    {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
    {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
    {X : Type uX} {A : Type uA}
    {Csem : Type uC} {Ssem : Type uR}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    [Fintype Ssem] [Nonempty Ssem] [DecidableEq Ssem]
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
    (hbasin : C.repairing.physicalRepair.basin.Nonempty) :
    SemanticRecoverableFormedCandidateValidity
      readout p regions response hprob probes dynamics persistenceDomain
      C.repairing.operational.parent
      C.repairing.operational.persistence.K
      C.repairing.physicalRepair.basin
      pi C.semantic.child := by
  refine ⟨selfRepairingParent_validity C.repairing hbasin, ?_⟩
  exact semanticallyStableParent_identity C

end UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
