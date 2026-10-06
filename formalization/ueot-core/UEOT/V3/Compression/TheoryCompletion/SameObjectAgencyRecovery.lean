import UEOT.V3.Compression.TheoryCompletion.SameObjectViableGOA
import UEOT.V3.Compression.TheoryCompletion.SameObjectRestoration

/-!
# P2 audit hardening — repair outside, greedy agency inside

Canonical RLSR restores and preserves the same parent, but its default
repair-then-preserve controller need not induce the Bellman-greedy agency
dynamics after recovery. Under P2.7's explicit greedy-viability certificate,
we may instead splice the certified physical repair policy outside the
persistence kernel with the Bellman-greedy controller inside it.

This does not modify Track-O. It is a Track-TC adapter proving that:

* the splice preserves the exact same persistence kernel;
* first-hitting-time/recovery-basin semantics are unchanged;
* an internal repair program implementing the splice is valid and recoverable;
* after recovery, that program induces exactly the same physical kernel as the
  Bellman-greedy agency controller on the persistence kernel.

Implementation equality is required only at the induced-dynamics level, not at
the action-label level.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set MeasureTheory ProbabilityTheory
open UEOT.V3
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteDiscountedControl
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
noncomputable local instance sameObjectAgencyRecoverySemanticDecidableEq :
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

/-- P2-specific fault/recovery controller: use the certified Objecthood physical
repair policy outside the persistence kernel, then resume Bellman-greedy agency
inside the persistence kernel. -/
noncomputable def repairThenGreedyAgencyPolicy
    (R : ObjecthoodTeleologicalControlSpec C Future) : X → A := by
  classical
  exact fun x =>
    if x ∈ C.repairing.operational.persistence.K then
      ((R.toParentRealization C).toControlModel dynamics).greedyAction x
    else
      C.repairing.physicalRepair.repairPolicy x

/-- Under the explicit P2.7 viability gate, repair-then-greedy is a preserving
controller for the exact same Objecthood persistence kernel. -/
theorem repairThenGreedyAgencyPolicy_preserving
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C) :
    PreservingController
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K
      (R.repairThenGreedyAgencyPolicy C) := by
  intro x hx
  simpa [repairThenGreedyAgencyPolicy, hx] using hviable x hx

/-- Outside the target kernel the P2-specific splice is literally the existing
certified physical repair policy. -/
theorem repairThenGreedyAgencyPolicy_eq_outside
    (R : ObjecthoodTeleologicalControlSpec C Future)
    {x : X} (hx : x ∉ C.repairing.operational.persistence.K) :
    R.repairThenGreedyAgencyPolicy C x =
      C.repairing.physicalRepair.repairPolicy x := by
  simp [repairThenGreedyAgencyPolicy, hx]

/-- Replacing only the inside-target behavior by greedy agency leaves the exact
first-hitting-time semantics unchanged. -/
theorem repairThenGreedyAgencyPolicy_expectedHittingTime_eq
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (x : X) :
    expectedHittingTime
        (stationaryKernel
          (dynamics C.repairing.operational.parent)
          (R.repairThenGreedyAgencyPolicy C))
        x C.repairing.operational.persistence.K =
      expectedHittingTime
        (stationaryKernel
          (dynamics C.repairing.operational.parent)
          C.repairing.physicalRepair.repairPolicy)
        x C.repairing.operational.persistence.K := by
  apply expectedHittingTime_stationary_eq_of_policyKernel_eq_outside
  intro z hz
  rw [R.repairThenGreedyAgencyPolicy_eq_outside C hz]

/-- A trusted internal program implementing repair-then-greedy at the physical
kernel level is valid on the same Objecthood persistence kernel. -/
theorem repairThenGreedy_program_valid
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C)
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T
      (dynamics C.repairing.operational.parent) r
      (R.repairThenGreedyAgencyPolicy C)) :
    RepairProgramValid T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K r := by
  intro x hx y hy
  rw [himpl x] at hy
  exact R.repairThenGreedyAgencyPolicy_preserving C hviable x hx hy

/-- The same program has exactly the canonical physical-repair basin, because
the splice differs from the certified repair policy only after the first hit of
the target kernel. -/
theorem repairThenGreedy_program_recoverable
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T
      (dynamics C.repairing.operational.parent) r
      (R.repairThenGreedyAgencyPolicy C))
    {x : X} (hx : x ∈ C.repairing.physicalRepair.basin) :
    RepairProgramRecoverableAt T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K r x := by
  apply (repairProgramRecoverableAt_iff T
    (dynamics C.repairing.operational.parent)
    C.repairing.operational.persistence.K r x).2
  calc
    expectedHittingTime
        (stationaryKernel
          (dynamics C.repairing.operational.parent)
          (T.execute r))
        x C.repairing.operational.persistence.K =
      expectedHittingTime
        (stationaryKernel
          (dynamics C.repairing.operational.parent)
          (R.repairThenGreedyAgencyPolicy C))
        x C.repairing.operational.persistence.K := by
          apply expectedHittingTime_stationary_eq_of_policyKernel_eq_outside
          intro z hz
          exact himpl z
    _ = expectedHittingTime
        (stationaryKernel
          (dynamics C.repairing.operational.parent)
          C.repairing.physicalRepair.repairPolicy)
        x C.repairing.operational.persistence.K :=
      R.repairThenGreedyAgencyPolicy_expectedHittingTime_eq C x
    _ ≠ ∞ :=
      C.repairing.physicalRepair.expectedHittingTime_ne_top_of_mem_basin hx

/-- Inside the restored persistence kernel, a program implementing the splice
induces exactly the Bellman-greedy physical dynamics. -/
theorem recoveredProgram_greedyDynamics_on_persistence
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T
      (dynamics C.repairing.operational.parent) r
      (R.repairThenGreedyAgencyPolicy C))
    {x : X} (hx : x ∈ C.repairing.operational.persistence.K) :
    dynamics C.repairing.operational.parent x (T.execute r x) =
      dynamics C.repairing.operational.parent x
        (((R.toParentRealization C).toControlModel dynamics).greedyAction x) := by
  rw [himpl x]
  simp [repairThenGreedyAgencyPolicy, hx]

/-- Optional semantic recovery certificate.  On the restored persistence
kernel, the program's executed action and the canonical Bellman-greedy action
must denote contract-indifferent admissible futures.

This is intentionally separate from dynamics implementation: two action labels
can induce the same physical transition while carrying different teleological
meaning. -/
def RepairProgramTeleologicallyEquivalentToGreedyOnPersistence
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (T : TrustedRepairSubstrate Program X A)
    (r : Program) : Prop :=
  ∀ x ∈ C.repairing.operational.persistence.K,
    R.contract.Indifferent
      (R.actionFuture x (T.execute r x))
      (R.actionFuture x
        (((R.toParentRealization C).toControlModel dynamics).greedyAction x))

/-- Contract indifference forces equality of the chosen numerical reward
representation for recovered and greedy actions. -/
theorem recoveredProgram_reward_eq_greedy_on_persistence
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (htele : R.RepairProgramTeleologicallyEquivalentToGreedyOnPersistence C T r)
    {x : X} (hx : x ∈ C.repairing.operational.persistence.K) :
    ((R.toParentRealization C).toControlModel dynamics).reward
        x (T.execute r x) =
      ((R.toParentRealization C).toControlModel dynamics).reward
        x (((R.toParentRealization C).toControlModel dynamics).greedyAction x) := by
  let f :=
    R.actionFuture x (T.execute r x)
  let g :=
    R.actionFuture x
      (((R.toParentRealization C).toControlModel dynamics).greedyAction x)
  have hindiff : R.contract.Indifferent f g := by
    simpa [f, g] using htele x hx
  have hfg : InducedPreference R.objective f g :=
    (R.objective_represents f g).2 hindiff.1
  have hgf : InducedPreference R.objective g f :=
    (R.objective_represents g f).2 hindiff.2
  change R.objective f ≤ R.objective g at hfg
  change R.objective g ≤ R.objective f at hgf
  rw [R.toControlModel_reward_selectedParent C,
    R.toControlModel_reward_selectedParent C]
  simpa [f, g] using le_antisymm hfg hgf

/-- Physical-kernel equality plus teleological equivalence closes the Bellman
action-value gap: the recovered program action has exactly the greedy Q-value
on the restored persistence kernel. -/
theorem recoveredProgram_qValue_eq_greedy_on_persistence
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T
      (dynamics C.repairing.operational.parent) r
      (R.repairThenGreedyAgencyPolicy C))
    (htele : R.RepairProgramTeleologicallyEquivalentToGreedyOnPersistence C T r)
    {x : X} (hx : x ∈ C.repairing.operational.persistence.K) :
    let M := (R.toParentRealization C).toControlModel dynamics
    M.qValue M.optimalValue x (T.execute r x) =
      M.qValue M.optimalValue x (M.greedyAction x) := by
  dsimp
  let M := (R.toParentRealization C).toControlModel dynamics
  have hrewards :
      M.reward x (T.execute r x) =
        M.reward x (M.greedyAction x) := by
    simpa [M] using
      R.recoveredProgram_reward_eq_greedy_on_persistence C T r htele hx
  have hdynamics :=
    R.recoveredProgram_greedyDynamics_on_persistence C T r himpl hx
  have htransition (y : X) :
      M.transition x (T.execute r x) y =
        M.transition x (M.greedyAction x) y := by
    have hpoint :=
      congrArg (fun p : PMF X => (p y).toReal) hdynamics
    simpa [M] using hpoint
  have hexpect :
      M.expect x (T.execute r x) M.optimalValue =
        M.expect x (M.greedyAction x) M.optimalValue := by
    simp only [Model.expect]
    apply Finset.sum_congr rfl
    intro y hy
    rw [htransition y]
  simp only [Model.qValue]
  rw [hrewards, hexpect]

/-- The missing semantic bridge for RLSR agency recovery.  A program that
restores the greedy physical kernel is Bellman-GOD compatible only after the
explicit teleological-equivalence certificate is supplied. -/
theorem recoveredProgram_mem_bellmanGOD_on_persistence
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T
      (dynamics C.repairing.operational.parent) r
      (R.repairThenGreedyAgencyPolicy C))
    (htele : R.RepairProgramTeleologicallyEquivalentToGreedyOnPersistence C T r)
    {x : X} (hx : x ∈ C.repairing.operational.persistence.K) :
    T.execute r x ∈
      BellmanGODCorrespondence
        ((R.toParentRealization C).toControlModel dynamics) x := by
  rw [mem_bellmanGODCorrespondence_iff]
  rw [R.recoveredProgram_qValue_eq_greedy_on_persistence C T r himpl htele hx]
  exact
    ((R.toParentRealization C).toControlModel dynamics).greedyAction_spec x

/-- End-to-end same-object agency recovery.  Physical repair validity and
recoverability come from the repair-then-greedy implementation/viability gates;
Bellman-GOD restoration additionally requires teleological equivalence on the
restored persistence kernel.

This theorem is the precise point at which it is legitimate to say that agency,
not merely physical dynamics, has been restored. -/
theorem sameObject_recovery_restores_bellmanGOD
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C)
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T
      (dynamics C.repairing.operational.parent) r
      (R.repairThenGreedyAgencyPolicy C))
    (htele : R.RepairProgramTeleologicallyEquivalentToGreedyOnPersistence C T r)
    {x : X} (hx : x ∈ C.repairing.physicalRepair.basin) :
    (R.toParentRealization C).parent =
        C.repairing.operational.parent ∧
    RepairProgramValid T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K r ∧
    RepairProgramRecoverableAt T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K r x ∧
    (∀ y ∈ C.repairing.operational.persistence.K,
      T.execute r y ∈
        BellmanGODCorrespondence
          ((R.toParentRealization C).toControlModel dynamics) y) := by
  refine ⟨rfl, R.repairThenGreedy_program_valid C hviable T r himpl,
    R.repairThenGreedy_program_recoverable C T r himpl hx, ?_⟩
  intro y hy
  exact R.recoveredProgram_mem_bellmanGOD_on_persistence
    C T r himpl htele hy

/-- Strengthened P2/RLSR physical endpoint. One dynamics-level program contract plus the
explicit greedy-viability gate gives same-parent RLSR recovery and additionally
proves that, after return to the persistence kernel, the reconstructed program
resumes the exact Bellman-greedy physical dynamics.

No teleological equivalence or GOD membership is claimed by this theorem. -/
theorem singleReplica_recovery_resumes_greedyPhysicalDynamics
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C)
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T
      (dynamics C.repairing.operational.parent) r
      (R.repairThenGreedyAgencyPolicy C))
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
            C.repairing.operational.persistence.K) ∧
      (∀ y ∈ C.repairing.operational.persistence.K,
        dynamics C.repairing.operational.parent y (T.execute r y) =
          dynamics C.repairing.operational.parent y
            (((R.toParentRealization C).toControlModel dynamics).greedyAction y))) := by
  have hvalid := R.repairThenGreedy_program_valid C hviable T r himpl
  have hrecover := R.repairThenGreedy_program_recoverable C T r himpl hx
  refine ⟨rfl, ?_⟩
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro y hy
    exact R.recoveredProgram_greedyDynamics_on_persistence C T r himpl hy

end ObjecthoodTeleologicalControlSpec

end

end UEOT.V3.Compression.TheoryCompletion
