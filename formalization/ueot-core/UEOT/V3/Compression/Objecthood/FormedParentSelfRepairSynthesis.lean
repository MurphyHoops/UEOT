import UEOT.V3.Compression.Objecthood.FailureRepairabilityBoundary
import UEOT.V3.Compression.CrossTrack.EndogenousObjectSynthesis
import UEOT.V3.Compression.CrossTrack.RobustParentSemanticCertificate

/-!
# Track O / O7 — formed parent × identification × self-repair synthesis

The merged Track-X `OperationalFormedPersistentParent` already selects one
response-generated parent and stores:

* generated-family provenance;
* family-wide interaction identifiability;
* one nonvacuous P-PER constitutive persistence certificate for that exact
  selected parent's dynamics.

O7 adds an O4 physical-repair certificate whose target is definitionally the
same persistence kernel. The resulting object therefore repairs to the
legitimate constitutive domain of the same formed parent, rather than merely to
an unrelated viable state.

No new parent selector, semantic identity, or counted primitive is introduced.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.OmegaMinimalFailure
open scoped ENNReal ProbabilityTheory

universe uV uChild uH uProbe uR uY uE uZ uX uA uDel uC uS

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

/-- O7 end-to-end package. The repair target is not supplied independently:
it is exactly the persistence kernel already stored by the selected operational
formed parent. -/
structure SelfRepairingOperationalParent
    [Fintype Child]
    (readout : Finset V → H → Rout)
    (p : H → Probe → Measure Y)
    (regions : Child → Finset V)
    (response : Finset Child → E → Measure Z)
    (hprob : ∀ S e, IsProbabilityMeasure (response S e))
    (probes : Finset E)
    (dynamics : FormedCandidate readout p regions → X → A → PMF X)
    (persistenceDomain : FormedCandidate readout p regions → Set X) where
  operational : OperationalFormedPersistentParent
    readout p regions response hprob probes dynamics persistenceDomain
  physicalRepair : PhysicalRepairCertificate
    (dynamics operational.parent) operational.persistence.K

namespace SelfRepairingOperationalParent

/-- Rebuild the O3 controller-level self-stabilization certificate on the exact
P-PER kernel already stored by Track X. No second winning kernel is selected. -/
def controllerCertificate
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    (C : SelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain) :
    ControllerSelfStabilizationCertificate
      (dynamics C.operational.parent)
      (persistenceDomain C.operational.parent) where
  K := C.operational.persistence.K
  seed := C.operational.persistence.seed
  kernel_sub_domain := C.operational.persistence.kernel_sub_domain
  seed_mem := C.operational.persistence.seed_mem
  source_fixed := C.operational.persistence.source_fixed
  source_winning := C.operational.persistence.source_winning
  closure := by
    intro z hz
    exact controllerRepairLift_staysIn_legitimate
      (dynamics C.operational.parent) C.operational.persistence.K
      C.operational.persistence.source_fixed hz
  controller_convergence := by
    intro z hz
    exact controllerRepairLift_enters_legitimate
      (dynamics C.operational.parent) C.operational.persistence.K
      C.operational.persistence.source_fixed hz
  path_after_one := by
    intro z hz
    exact controllerRepairLift_all_times_after_one
      (dynamics C.operational.parent) C.operational.persistence.K
      C.operational.persistence.source_fixed hz

/-- O5 self-stabilization package for the same selected formed parent. -/
def selfStabilizing
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    (C : SelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain) :
    SelfStabilizingConstitutiveCertificate
      (dynamics C.operational.parent)
      (persistenceDomain C.operational.parent) where
  controller := C.controllerCertificate
  physicalRepair := by
    simpa [controllerCertificate] using C.physicalRepair

/-- The self-repair kernel is definitionally the exact persistence kernel
already certified for the operational formed parent. -/
theorem repair_kernel_eq_operational_kernel
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    (C : SelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain) :
    C.selfStabilizing.controller.K = C.operational.persistence.K := by
  rfl

/-- Formation provenance survives unchanged through the O7 extension. -/
theorem parent_mem_generatedFamily
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    (C : SelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain) :
    C.operational.parent.1 ∈ responseFormedCandidateFamily readout p regions :=
  C.operational.parent_mem_generatedFamily

/-- Family-wide interaction identification is preserved because O7 extends the
same operational certificate rather than rebuilding parent identity. -/
theorem interactionIsolation_pos
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
    (C : SelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain) :
    0 < interactionIsolationConorm
      (formedCandidateResponseFamily readout p regions response hprob)
      probes C.operational.probes_nonempty :=
  C.operational.interactionIsolation_pos

/-- Quantitative expected repair time to the legitimate organization of the
same formed parent. -/
theorem expectedRepairTime_le
    [Fintype Child]
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
    (z : ConstitutiveState X A) :
    expectedHittingTime
      (stationaryKernel
        (autonomousRepairLift
          (dynamics C.operational.parent) C.operational.persistence.K
          C.operational.persistence.source_fixed C.physicalRepair)
        noExternalControl)
      z
      (legitimateConstitutiveDomain
        (dynamics C.operational.parent) C.operational.persistence.K) ≤
      autonomousRepairPotential
        (dynamics C.operational.parent) C.operational.persistence.K
        C.physicalRepair z / C.physicalRepair.drift :=
  autonomousRepair_expectedHittingTime_le
    (dynamics C.operational.parent) C.operational.persistence.K
    C.operational.persistence.source_fixed C.physicalRepair z

/-- **O7 restoration theorem.** Every certified damaged state eventually
returns almost surely to the legitimate constitutive domain of the exact same
selected formed parent. -/
theorem eventually_restores_same_parent_contract
    [Fintype Child]
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
    {z : ConstitutiveState X A}
    (hz : z.1 ∈ C.physicalRepair.basin) :
    ∀ᵐ omega ∂stationaryTrajMeasure
        (autonomousRepairLift
          (dynamics C.operational.parent) C.operational.persistence.K
          C.operational.persistence.source_fixed C.physicalRepair)
        noExternalControl (PMF.pure z),
      ∃ n : ℕ,
        omega n ∈ legitimateConstitutiveDomain
          (dynamics C.operational.parent) C.operational.persistence.K :=
  autonomousRepair_eventually_legitimate_ae
    (dynamics C.operational.parent) C.operational.persistence.K
    C.operational.persistence.source_fixed C.physicalRepair hz

/-- Expanded form of O7 restoration: the returned state lies in the original
Track-X persistence kernel and carries a controller that preserves that exact
kernel for the same selected parent's dynamics. -/
theorem eventually_restores_original_persistence_kernel
    [Fintype Child]
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
    {z : ConstitutiveState X A}
    (hz : z.1 ∈ C.physicalRepair.basin) :
    ∀ᵐ omega ∂stationaryTrajMeasure
        (autonomousRepairLift
          (dynamics C.operational.parent) C.operational.persistence.K
          C.operational.persistence.source_fixed C.physicalRepair)
        noExternalControl (PMF.pure z),
      ∃ n : ℕ,
        (omega n).1 ∈ C.operational.persistence.K ∧
        PreservingController
          (dynamics C.operational.parent) C.operational.persistence.K
          (omega n).2 := by
  filter_upwards [C.eventually_restores_same_parent_contract hz] with omega homega
  rcases homega with ⟨n, hn⟩
  have hn' :
      (omega n).1 ∈ C.operational.persistence.K ∧
      PreservingController
        (dynamics C.operational.parent) C.operational.persistence.K
        (omega n).2 := by
    simpa [legitimateConstitutiveDomain] using hn
  exact ⟨n, hn'.1, hn'.2⟩

/-- Once restored, the same O7 dynamics preserves the same parent contract. -/
theorem restored_contract_closed
    [Fintype Child]
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
    {z : ConstitutiveState X A}
    (hz : z ∈ legitimateConstitutiveDomain
      (dynamics C.operational.parent) C.operational.persistence.K) :
    StaysIn
      (autonomousRepairLift
        (dynamics C.operational.parent) C.operational.persistence.K
        C.operational.persistence.source_fixed C.physicalRepair z ())
      (legitimateConstitutiveDomain
        (dynamics C.operational.parent) C.operational.persistence.K) :=
  autonomousRepairLift_staysIn_legitimate
    (dynamics C.operational.parent) C.operational.persistence.K
    C.operational.persistence.source_fixed C.physicalRepair hz

/-- O6 deletion failures can be threaded through O7 without changing the
selected parent: a repairable failing deletion has a minimal destructive
witness and almost-sure return to that parent's legitimate domain. -/
theorem failingDeletion_restores_same_parent_contract
    [Fintype Child]
    {Del : Type uDel}
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
    (Failure : Finset Del → Prop)
    (hmono : FailureMonotone Failure)
    (damage : Finset Del → ConstitutiveState X A)
    (D : Finset Del) (hfail : Failure D)
    (hrepair : RepairableDeletion C.physicalRepair damage D) :
    ∃ Dmin, Dmin ∈ minimalFailures Failure ∧ Dmin ⊆ D ∧
      (∀ᵐ omega ∂stationaryTrajMeasure
          (autonomousRepairLift
            (dynamics C.operational.parent) C.operational.persistence.K
            C.operational.persistence.source_fixed C.physicalRepair)
          noExternalControl (PMF.pure (damage D)),
        ∃ n : ℕ, omega n ∈ legitimateConstitutiveDomain
          (dynamics C.operational.parent) C.operational.persistence.K) :=
  failure_witness_and_autonomous_repair
    (dynamics C.operational.parent) C.operational.persistence.K
    C.operational.persistence.source_fixed C.physicalRepair
    Failure hmono damage D hfail hrepair

end SelfRepairingOperationalParent

/-- O7 requires no new formation theorem: any already formed operational parent
becomes an O7 object exactly when an explicit physical repair certificate is
supplied for its own stored persistence kernel. -/
theorem exists_selfRepairingOperationalParent
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
      readout p regions response hprob probes dynamics persistenceDomain)
    (R : PhysicalRepairCertificate (dynamics C.parent) C.persistence.K) :
    Nonempty (SelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain) :=
  ⟨{ operational := C, physicalRepair := R }⟩

/-! ## O7 semantic-stability hardening

`OperationalFormedPersistentParent` carries formation, interaction
identifiability, and constitutive persistence, but Track-X long-run semantic
stability lives in the separate `RobustParentSemanticCertificate` surface.
O7 therefore needs an explicit typed extension rather than treating interaction
isolation as though it were already the long-run semantic certificate.
-/

variable {Csem : Type uC}
variable {Ssem : Type uS} [Fintype Ssem] [Nonempty Ssem]
noncomputable local instance formedParentSemanticDecidableEq : DecidableEq Ssem :=
  Classical.decEq Ssem

/-- The hardened O7 package binds the exact same formed-parent completion to
both the self-repair certificate and Track-X robust long-run semantics.

`selected_parent_in_fiber` is the explicit identity bridge: it states that the
selected operational parent is one of the parent completions certified in the
semantic fibre. No relation between physical repair dynamics and the separate
semantic kernel is invented beyond their shared parent identity. -/
structure SemanticallyStableSelfRepairingOperationalParent
    [Fintype Child]
    (readout : Finset V → H → Rout)
    (p : H → Probe → Measure Y)
    (regions : Child → Finset V)
    (response : Finset Child → E → Measure Z)
    (hprob : ∀ S e, IsProbabilityMeasure (response S e))
    (probes : Finset E)
    (dynamics : FormedCandidate readout p regions → X → A → PMF X)
    (persistenceDomain : FormedCandidate readout p regions → Set X)
    (pi : FormedCandidate readout p regions → Csem)
    (semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ)
    (hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem) where
  repairing : SelfRepairingOperationalParent
    readout p regions response hprob probes dynamics persistenceDomain
  semantic : RobustParentSemanticCertificate pi semanticKernel hSemanticKernel
  selected_parent_in_fiber :
    pi repairing.operational.parent = semantic.child

namespace SemanticallyStableSelfRepairingOperationalParent

/-- The selected formed parent retains an explicit Track-X invariant long-run
semantic witness. -/
theorem selected_parent_invariant
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
      pi semanticKernel hSemanticKernel) :
    C.semantic.invariantLaw C.repairing.operational.parent ∈
      invariantLawSet
        (semanticKernel C.repairing.operational.parent)
        (hSemanticKernel C.repairing.operational.parent) :=
  C.semantic.invariant C.repairing.operational.parent

/-- The exact selected parent inherits the Track-X `epsilon / kappaMin`
long-run semantic bound against every completion in the same certified child
fibre. -/
theorem selected_parent_pairwise_semantic_bound
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
    (hcard : 1 < Fintype.card Ssem)
    {q : FormedCandidate readout p regions}
    (hq : pi q = C.semantic.child) :
    lawTV
      (C.semantic.invariantLaw C.repairing.operational.parent)
      (C.semantic.invariantLaw q) ≤
        C.semantic.epsilon / C.semantic.kappaMin := by
  exact C.semantic.pairwise_bound
    pi semanticKernel hSemanticKernel hcard
    C.selected_parent_in_fiber hq

/-- **Hardened O7 joint theorem.** The same selected formed parent retains its
Track-X long-run semantic stability guarantee while transient damage in the
declared O5 repair basin returns almost surely to that parent's legitimate
constitutive domain. The two claims share the same parent completion but remain
properly typed on their distinct semantic and constitutive dynamics. -/
theorem semantic_bound_and_eventual_same_parent_repair
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
    (hcard : 1 < Fintype.card Ssem)
    {q : FormedCandidate readout p regions}
    (hq : pi q = C.semantic.child)
    {z : ConstitutiveState X A}
    (hz : z.1 ∈ C.repairing.physicalRepair.basin) :
    lawTV
      (C.semantic.invariantLaw C.repairing.operational.parent)
      (C.semantic.invariantLaw q) ≤
        C.semantic.epsilon / C.semantic.kappaMin ∧
    (∀ᵐ omega ∂stationaryTrajMeasure
        (autonomousRepairLift
          (dynamics C.repairing.operational.parent)
          C.repairing.operational.persistence.K
          C.repairing.operational.persistence.source_fixed
          C.repairing.physicalRepair)
        noExternalControl (PMF.pure z),
      ∃ n : ℕ,
        omega n ∈ legitimateConstitutiveDomain
          (dynamics C.repairing.operational.parent)
          C.repairing.operational.persistence.K) := by
  exact ⟨C.selected_parent_pairwise_semantic_bound hcard hq,
    C.repairing.eventually_restores_same_parent_contract hz⟩

end SemanticallyStableSelfRepairingOperationalParent

end

end UEOT.V3.Compression.Objecthood
