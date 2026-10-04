import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.NoInfiniteRegress
import UEOT.V3.Compression.Objecthood.FormedParentSelfRepairSynthesis

/-!
# RLSR8 — same-parent / semantic restoration

The reconstructed mutable repair program is now tied back to the exact selected
formed parent.  The bridge is behavioral: the decoded program implements that
parent's already-certified physical repair policy.  An additional validity
premise is kept explicit because a `PhysicalRepairCertificate` guarantees
hitting its target but does not by itself guarantee target preservation after
entry.

This stage therefore distinguishes:

* physical return to the selected parent's persistence kernel;
* permanent preservation there by the reconstructed program;
* unchanged Track-X semantic identity of that exact formed parent.
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
noncomputable local instance rlsr8SemanticDecidableEq : DecidableEq Ssem :=
  Classical.decEq Ssem

omit [Nonempty A] [DecidableEq Program] [Nonempty Ssem] in
/-- If the reconstructed program implements the selected parent's certified
physical repair policy, every state in that parent's physical repair basin lies
in the reconstructed program's own recovery basin. -/
theorem repairProgramRecoverableAt_of_sameParent_physicalRepair
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
    (himpl : RepairProgramImplementsPolicy T r
      C.repairing.physicalRepair.repairPolicy)
    {x : X}
    (hx : x ∈ C.repairing.physicalRepair.basin) :
    RepairProgramRecoverableAt T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K r x := by
  apply (repairProgramRecoverableAt_iff T
    (dynamics C.repairing.operational.parent)
    C.repairing.operational.persistence.K r x).2
  have hpolicy :
      T.execute r = C.repairing.physicalRepair.repairPolicy := by
    funext y
    exact himpl y
  rw [hpolicy]
  exact C.repairing.physicalRepair.expectedHittingTime_ne_top_of_mem_basin hx

/-- Canonical damaged RLSR state for the one-replica benchmark. -/
def sameParentSingleReplicaDamagedState
    (x : X) (controller : X → A)
    (r bad : Program) (i : Fin 3) :
    JointRepairState (X := X) (A := A) (Program := Program) :=
  { physical := x
    controller := controller
    repairProgram := replaceProgramReplica i bad (tripleProgramEncode r)
    mode := .restoreProgram }

omit [Nonempty A] [DecidableEq Program] [Nonempty Ssem] in
/-- A same-parent single-replica fault lies in the explicit RLSR joint recovery
basin whenever the encoded repair program is target-preserving and implements
the selected parent's certified physical repair policy. -/
theorem sameParentSingleReplicaDamagedState_mem_jointRecoveryBasin
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
    (himpl : RepairProgramImplementsPolicy T r
      C.repairing.physicalRepair.repairPolicy)
    (hvalid : RepairProgramValid T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K r)
    {x : X} (hx : x ∈ C.repairing.physicalRepair.basin)
    (controller : X → A) (bad : Program) (i : Fin 3) :
    sameParentSingleReplicaDamagedState x controller r bad i ∈
      JointRecoveryBasin T
        (dynamics C.repairing.operational.parent)
        C.repairing.operational.persistence.K := by
  refine ⟨rfl, r, hvalid, ?_, ?_⟩
  · exact ⟨i, bad, rfl⟩
  · exact repairProgramRecoverableAt_of_sameParent_physicalRepair C T r himpl hx

/-- **RLSR8 terminal same-parent theorem.**  Starting with arbitrary ordinary
controller corruption plus one arbitrary repair-program replica replacement:

1. the damaged joint state is inside the explicit RLSR basin;
2. the first autonomous joint step reconstructs the intended repair program and
   controller exactly without moving physical state;
3. the exact selected formed parent retains its Track-X semantic bound;
4. the reconstructed internal program drives physical state eventually and
   permanently into that parent's persistence kernel;
5. the fully recovered joint target is closed under the same joint kernel.

The semantic certificate itself is not reconstructed; it remains the independent
Track-X specification attached to the exact same selected parent. -/
theorem singleReplica_reconstructs_sameParent_semantics_and_recovery
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
    (himpl : RepairProgramImplementsPolicy T r
      C.repairing.physicalRepair.repairPolicy)
    (hvalid : RepairProgramValid T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K r)
    (hcard : 1 < Fintype.card Ssem)
    {q : FormedCandidate readout p regions}
    (hq : pi q = C.semantic.child)
    {x : X} (hx : x ∈ C.repairing.physicalRepair.basin)
    (controller : X → A) (bad : Program) (i : Fin 3) :
    let damaged := sameParentSingleReplicaDamagedState x controller r bad i
    damaged ∈ JointRecoveryBasin T
        (dynamics C.repairing.operational.parent)
        C.repairing.operational.persistence.K ∧
      jointRepairKernel T (dynamics C.repairing.operational.parent) damaged =
        PMF.pure (restoredJointState T r x) ∧
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
          (jointRepairKernel T (dynamics C.repairing.operational.parent)
            (restoredJointState T r y))
          (RecoveredJointTarget T C.repairing.operational.persistence.K r)) := by
  dsimp
  have hrecover : RepairProgramRecoverableAt T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K r x :=
    repairProgramRecoverableAt_of_sameParent_physicalRepair C T r himpl hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact sameParentSingleReplicaDamagedState_mem_jointRecoveryBasin
      C T r himpl hvalid hx controller bad i
  · exact jointRepairKernel_singleReplica_restore T
      (dynamics C.repairing.operational.parent) x controller r bad i
  · exact C.selected_parent_pairwise_semantic_bound hcard hq
  · exact reconstructedProgram_eventually_always_target_ae T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K hvalid hrecover
  · intro y hy
    exact jointRepairKernel_staysIn_recoveredTarget T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K hvalid hy

end
end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
