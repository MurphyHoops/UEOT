import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.RepairThenPreserve
import UEOT.V3.Compression.Objecthood.FormedParentSelfRepairSynthesis

/-!
# RLSR-T4 — tightened same-parent terminal theorem

This is the preferred post-audit RLSR endpoint.  It uses the mode-free safe
kernel and one dynamics-level internal-program contract implementing the
canonical `repair outside / preserve inside` law for the exact selected parent.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.CrossTrack
open scoped ENNReal ProbabilityTheory

universe uV uChild uH uProbe uR uY uE uZ uX uA uP uC uS

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
variable {Program : Type uP} [DecidableEq Program]
variable {Csem : Type uC}
variable {Ssem : Type uS} [Fintype Ssem] [Nonempty Ssem]
noncomputable local instance rlsrT4SemanticDecidableEq : DecidableEq Ssem :=
  Classical.decEq Ssem

/-- Projection from strengthened RLSR organization state back to the established
O1 constitutive state. -/
def repairOrganizationConstitutiveProjection
    {Representation : Type*}
    (s : RepairOrganizationState X A Representation) : ConstitutiveState X A :=
  (s.physical, s.controller)

omit [Fintype X] [Fintype A] [Nonempty A]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace (ConstitutiveState X A)]
  [MeasurableSingletonClass (ConstitutiveState X A)] [DecidableEq Program] in
/-- A recovered safe-joint state projects into the already established O1
legitimate constitutive domain.  The strengthened RLSR target therefore refines,
rather than replaces, the existing Objecthood legitimacy API. -/
theorem safeRecoveredTarget_projects_to_legitimate
    {Representation : Type*}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (K : Set X)
    {r : Program} (hr : RepairProgramValid T P K r)
    {s : RepairOrganizationState X A Representation}
    (hs : s ∈ SafeRecoveredTarget T codec K r) :
    repairOrganizationConstitutiveProjection s ∈
      legitimateConstitutiveDomain P K := by
  rcases hs with ⟨x, hx, rfl⟩
  exact ⟨hx, hr⟩

omit [DecidableEq Program] [Nonempty Ssem] in
/-- The one-contract same-parent program is valid on the selected parent's
persistence kernel. -/
theorem tightenedSameParent_program_valid
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ T e, IsProbabilityMeasure (response T e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (C : SemanticallyStableSelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T
      (dynamics C.repairing.operational.parent) r
      (repairThenPreservePolicy
        (dynamics C.repairing.operational.parent)
        C.repairing.operational.persistence.K
        C.repairing.operational.persistence.source_fixed
        C.repairing.physicalRepair.repairPolicy)) :
    RepairProgramValid T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K r := by
  exact repairProgramValid_of_dynamicsImplements_repairThenPreserve
    T (dynamics C.repairing.operational.parent)
    C.repairing.operational.persistence.K
    C.repairing.operational.persistence.source_fixed
    C.repairing.physicalRepair.repairPolicy r himpl

omit [DecidableEq Program] [Nonempty Ssem] in
/-- The same single contract transfers the parent's certified physical repair
basin to the reconstructed internal program. -/
theorem tightenedSameParent_program_recoverable
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ T e, IsProbabilityMeasure (response T e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (C : SemanticallyStableSelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T
      (dynamics C.repairing.operational.parent) r
      (repairThenPreservePolicy
        (dynamics C.repairing.operational.parent)
        C.repairing.operational.persistence.K
        C.repairing.operational.persistence.source_fixed
        C.repairing.physicalRepair.repairPolicy))
    {x : X} (hx : x ∈ C.repairing.physicalRepair.basin) :
    RepairProgramRecoverableAt T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K r x := by
  apply repairProgramRecoverableAt_of_dynamicsImplements_repairThenPreserve
    T (dynamics C.repairing.operational.parent)
    C.repairing.operational.persistence.K
    C.repairing.operational.persistence.source_fixed
    C.repairing.physicalRepair.repairPolicy r himpl
  exact C.repairing.physicalRepair.expectedHittingTime_ne_top_of_mem_basin hx

/-- **Strengthened RLSR same-parent endpoint.**  One dynamics-level internal
program contract now implies all of the former `himpl + hvalid` consequences.
For one arbitrary program-replica replacement and arbitrary stored-controller
corruption, the mode-free runtime repairs organization before the physical move,
executes the reconstructed controller, preserves the exact selected parent's
Track-X semantic identity, and yields eventual-permanent physical return plus
closure in an RLSR target whose constitutive projection is O1-legitimate. -/
theorem tightened_singleReplica_sameParent_recovery
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ T e, IsProbabilityMeasure (response T e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (C : SemanticallyStableSelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T
      (dynamics C.repairing.operational.parent) r
      (repairThenPreservePolicy
        (dynamics C.repairing.operational.parent)
        C.repairing.operational.persistence.K
        C.repairing.operational.persistence.source_fixed
        C.repairing.physicalRepair.repairPolicy))
    (hcard : 1 < Fintype.card Ssem)
    {q : FormedCandidate readout p regions}
    (hq : pi q = C.semantic.child)
    {x : X} (hx : x ∈ C.repairing.physicalRepair.basin)
    (controller : X → A) (bad : Program) (i : Fin 3) :
    let damaged := safeSingleReplicaDamagedState x controller r bad i
    safeRepairKernel T tripleRepairCodec
        (dynamics C.repairing.operational.parent) damaged =
      ((dynamics C.repairing.operational.parent) x (T.execute r x)).map
        (canonicalRepairOrganizationState T tripleRepairCodec r) ∧
    lawTV
      (C.semantic.invariantLaw C.repairing.operational.parent)
      (C.semantic.invariantLaw q) ≤
        C.semantic.epsilon / C.semantic.kappaMin ∧
    (∀ᵐ omega ∂stationaryTrajMeasure
        (dynamics C.repairing.operational.parent)
        (T.execute r) (PMF.pure x),
      ∃ N : ℕ, ∀ m ≥ N,
        omega m ∈ C.repairing.operational.persistence.K) ∧
    (∀ y ∈ C.repairing.operational.persistence.K,
      StaysIn
        (safeRepairKernel T tripleRepairCodec
          (dynamics C.repairing.operational.parent)
          (canonicalRepairOrganizationState T tripleRepairCodec r y))
        (SafeRecoveredTarget T tripleRepairCodec
          C.repairing.operational.persistence.K r)) ∧
    (∀ s ∈ SafeRecoveredTarget T tripleRepairCodec
        C.repairing.operational.persistence.K r,
      repairOrganizationConstitutiveProjection s ∈
        legitimateConstitutiveDomain
          (dynamics C.repairing.operational.parent)
          C.repairing.operational.persistence.K) := by
  dsimp
  have hvalid := tightenedSameParent_program_valid C T r himpl
  have hrecover := tightenedSameParent_program_recoverable C T r himpl hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact safeRepairKernel_singleReplica_exact T
      (dynamics C.repairing.operational.parent) x controller r bad i
  · exact C.selected_parent_pairwise_semantic_bound hcard hq
  · exact reconstructedProgram_eventually_always_target_ae T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K hvalid hrecover
  · intro y hy
    exact safeRepairKernel_staysIn_recoveredTarget T tripleRepairCodec
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K hvalid hy
  · intro s hs
    exact safeRecoveredTarget_projects_to_legitimate T tripleRepairCodec
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K hvalid hs

end
end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
