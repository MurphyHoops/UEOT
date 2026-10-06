import UEOT.V3.Compression.TheoryCompletion.SameObjectViability
import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.TightenedSameParentRestoration

/-!
# P2.8 — Same-parent restoration for the same Objecthood/control object

This module does not reopen RLSR. It only exposes that the parent restored by
the canonical tightened RLSR theorem is definitionally the same selected
Objecthood parent that owns the P2 control/GOD/GOA realization.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set MeasureTheory ProbabilityTheory
open UEOT.V3
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open scoped ENNReal ProbabilityTheory

universe uV uChild uH uProbe uR uY uE uZ uX uA uP uC uS uF

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
variable {Future : Type uF}
noncomputable local instance sameObjectRestorationSemanticDecidableEq :
    DecidableEq Ssem :=
  Classical.decEq Ssem

namespace ObjecthoodTeleologicalControlSpec

variable [Fintype Child]
variable
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

/-- P2.8 same-object adapter to the canonical tightened RLSR endpoint.

The first conjunct is the P2 identity guard. The remaining five conjuncts are
exactly the established RLSR conclusions for that same selected parent:
organizational reconstruction before the physical move, Track-X semantic
stability, eventual-permanent physical return, recovered-target closure, and
projection back into the legitimate constitutive domain.
-/
theorem tightenedRLSR_restores_same_control_object
    (R : ObjecthoodTeleologicalControlSpec C Future)
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
    (R.toParentRealization C).parent =
        C.repairing.operational.parent ∧
    (let damaged := safeSingleReplicaDamagedState x controller r bad i;
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
            C.repairing.operational.persistence.K)) := by
  refine ⟨rfl, ?_⟩
  exact tightened_singleReplica_sameParent_recovery
    C T r himpl hcard hq hx controller bad i

end ObjecthoodTeleologicalControlSpec

end

end UEOT.V3.Compression.TheoryCompletion
