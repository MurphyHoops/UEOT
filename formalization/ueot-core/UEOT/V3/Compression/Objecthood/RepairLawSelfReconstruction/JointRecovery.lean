import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.ProgramRecovery
import UEOT.V3.Compression.Objecthood.CanonicalStationaryRepair
import UEOT.V3.Compression.Objecthood.EventualAlwaysLegitimacy

/-!
# RLSR6 — joint physical / controller / repair-program recovery

One autonomous two-mode kernel now owns the organizational transition order.
`restoreProgram` first reconstructs the mutable repair representation and binds
the ordinary controller to the decoded program without moving physical state.
`executeProgram` then lets that reconstructed internal program drive physical
recovery.  No external maximal repair policy is switched in at runtime.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.DynamicsKernel
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.Compression.Objecthood
open scoped ENNReal ProbabilityTheory

universe uX uA uP

noncomputable section

variable {X : Type uX} {A : Type uA} {Program : Type uP}
variable [DecidableEq Program]

inductive JointRepairMode
  | restoreProgram
  | executeProgram
  deriving DecidableEq, Repr

/-- Mutable RLSR state used by the concrete finite reconstruction benchmark. -/
structure JointRepairState where
  physical : X
  controller : X → A
  repairProgram : TripleProgramRepresentation Program
  mode : JointRepairMode

/-- Canonical joint state after one repair-program reconstruction step. -/
def restoredJointState
    (T : TrustedRepairSubstrate Program X A)
    (r : Program) (x : X) : JointRepairState (X := X) (A := A) (Program := Program) :=
  { physical := x
    controller := T.execute r
    repairProgram := tripleProgramEncode r
    mode := .executeProgram }

/-- Deterministic organizational repair.  Physical state does not move. -/
def restoreProgramState
    (T : TrustedRepairSubstrate Program X A)
    (s : JointRepairState (X := X) (A := A) (Program := Program)) :
    JointRepairState (X := X) (A := A) (Program := Program) :=
  restoredJointState T (tripleProgramDecode s.repairProgram) s.physical

/-- One autonomous joint kernel.  In restore mode it reconstructs organization;
in execute mode the decoded internal program itself selects the physical action
and the joint state is re-canonicalized around that same program. -/
noncomputable def jointRepairKernel
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X)
    (s : JointRepairState (X := X) (A := A) (Program := Program)) :
    PMF (JointRepairState (X := X) (A := A) (Program := Program)) :=
  match s.mode with
  | .restoreProgram => PMF.pure (restoreProgramState T s)
  | .executeProgram =>
      let r := tripleProgramDecode s.repairProgram
      (P s.physical (T.execute r s.physical)).map (restoredJointState T r)

/-- A single corrupted replica is exactly reconstructed in the first autonomous
joint step; arbitrary ordinary-controller corruption is overwritten at the same
time. -/
theorem jointRepairKernel_singleReplica_restore
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X)
    (x : X) (controller : X → A)
    (r bad : Program) (i : Fin 3) :
    jointRepairKernel T P
      { physical := x
        controller := controller
        repairProgram := replaceProgramReplica i bad (tripleProgramEncode r)
        mode := .restoreProgram } =
      PMF.pure (restoredJointState T r x) := by
  simp [jointRepairKernel, restoreProgramState,
    tripleProgramDecode_replace_encode]

/-- Once restored, every execute-mode joint step is exactly the physical kernel
driven by the reconstructed internal program, mapped back into the recovered
joint-state representation. -/
theorem jointRepairKernel_restored
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (r : Program) (x : X) :
    jointRepairKernel T P (restoredJointState T r x) =
      (P x (T.execute r x)).map (restoredJointState T r) := by
  simp [jointRepairKernel, restoredJointState]

/-- Fully recovered joint target for one behaviorally valid program. -/
def RecoveredJointTarget
    (T : TrustedRepairSubstrate Program X A)
    (K : Set X) (r : Program) :
    Set (JointRepairState (X := X) (A := A) (Program := Program)) :=
  {s | ∃ x ∈ K, s = restoredJointState T r x}

/-- Behavioral program validity makes the recovered joint target closed under
the autonomous execute mode. -/
theorem jointRepairKernel_staysIn_recoveredTarget
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    {r : Program} (hr : RepairProgramValid T P K r)
    {x : X} (hx : x ∈ K) :
    StaysIn (jointRepairKernel T P (restoredJointState T r x))
      (RecoveredJointTarget T K r) := by
  rw [jointRepairKernel_restored]
  intro s hs
  rw [PMF.mem_support_map_iff] at hs
  rcases hs with ⟨y, hy, rfl⟩
  exact ⟨y, hr x hx hy, rfl⟩

variable [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]

omit [DecidableEq Program] in
/-- Program-specific physical recovery basin.  Unlike the pre-RLSR autonomous
repair layer, the policy here is the execution of the reconstructed internal
program itself. -/
def RepairProgramRecoverableAt
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    (r : Program) (x : X) : Prop :=
  x ∈ (policyCanonicalRepairCertificate P K (T.execute r)).basin

omit [DecidableEq Program] in
/-- Exact expected-hitting characterization of the program-specific basin. -/
theorem repairProgramRecoverableAt_iff
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    (r : Program) (x : X) :
    RepairProgramRecoverableAt T P K r x ↔
      expectedHittingTime (stationaryKernel P (T.execute r)) x K ≠ ∞ := by
  rfl

omit [DecidableEq Program] in
/-- The reconstructed internal program reaches the physical target almost
surely from its explicit program-specific basin. -/
theorem reconstructedProgram_eventually_hits_ae
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    (r : Program) {x : X}
    (hx : RepairProgramRecoverableAt T P K r x) :
    ∀ᵐ omega ∂stationaryTrajMeasure P (T.execute r) (PMF.pure x),
      ∃ n : ℕ, omega n ∈ K := by
  exact
    PhysicalRepairCertificate.stationaryTrajMeasure_eventually_hits_ae_of_mem_basin
      (policyCanonicalRepairCertificate P K (T.execute r)) hx

omit [DecidableEq Program] in
/-- If the reconstructed program is also behaviorally valid on `K`, physical
recovery is eventual-and-permanent rather than a one-time hit. -/
theorem reconstructedProgram_eventually_always_target_ae
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    {r : Program} (hr : RepairProgramValid T P K r)
    {x : X} (hx : RepairProgramRecoverableAt T P K r x) :
    ∀ᵐ omega ∂stationaryTrajMeasure P (T.execute r) (PMF.pure x),
      ∃ N : ℕ, ∀ m ≥ N, omega m ∈ K := by
  let Q := stationaryKernel P (T.execute r)
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have hclosed : ∀ y ∈ K, Q y K = 1 := by
    intro y hy
    exact (staysIn_iff_toMeasure_eq_one (P y (T.execute r y)) hK).1 (hr y hy)
  have hhit :
      ∀ᵐ omega ∂homTrajMeasure (PMF.pure x).toMeasure Q,
        ∃ n : ℕ, omega n ∈ K := by
    simpa [Q, stationaryTrajMeasure] using
      reconstructedProgram_eventually_hits_ae T P K r hx
  have hEA :=
    eventually_always_of_eventually_hits_absorbing
      Q K hclosed (PMF.pure x).toMeasure hhit
  simpa [Q, stationaryTrajMeasure] using hEA

/-- Explicit benchmark basin for the complete ordered mechanism.  The program
representation is one arbitrary-replica corruption of a valid codeword and the
physical state lies in that decoded program's own finite-mean recovery basin.
The ordinary controller may be arbitrarily corrupted because restore mode
rewrites it before any physical move. -/
def JointRecoveryBasin
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X) :
    Set (JointRepairState (X := X) (A := A) (Program := Program)) :=
  {s | s.mode = .restoreProgram ∧
    ∃ r, RepairProgramValid T P K r ∧
      SingleReplicaCorruptionOf r s.repairProgram ∧
      RepairProgramRecoverableAt T P K r s.physical}

/-- **RLSR6 terminal ordered-chain theorem.**  Every state in the explicit joint
basin admits one source program `r` such that:

1. the first autonomous joint step reconstructs program + controller exactly,
   without moving the physical state;
2. subsequent execute-mode steps are the internal-program physical kernel
   (`jointRepairKernel_restored` above);
3. the physical trajectory is almost surely eventually permanently in `K`;
4. once physical `K` is reached, the corresponding fully recovered joint target
   is closed under the same autonomous joint kernel.
-/
theorem jointRecoveryBasin_recovers
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    {s : JointRepairState (X := X) (A := A) (Program := Program)}
    (hs : s ∈ JointRecoveryBasin T P K) :
    ∃ r,
      jointRepairKernel T P s =
        PMF.pure (restoredJointState T r s.physical) ∧
      (∀ᵐ omega ∂stationaryTrajMeasure P (T.execute r) (PMF.pure s.physical),
        ∃ N : ℕ, ∀ m ≥ N, omega m ∈ K) ∧
      (∀ y ∈ K,
        StaysIn (jointRepairKernel T P (restoredJointState T r y))
          (RecoveredJointTarget T K r)) := by
  rcases hs with ⟨hmode, r, hr, hcorr, hx⟩
  refine ⟨r, ?_, reconstructedProgram_eventually_always_target_ae T P K hr hx, ?_⟩
  · rcases hcorr with ⟨i, bad, hrep⟩
    rcases s with ⟨x, controller, rep, mode⟩
    simp only at hmode hrep ⊢
    subst mode
    subst rep
    exact jointRepairKernel_singleReplica_restore T P x controller r bad i
  · intro y hy
    exact jointRepairKernel_staysIn_recoveredTarget T P K hr hy

end
end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
