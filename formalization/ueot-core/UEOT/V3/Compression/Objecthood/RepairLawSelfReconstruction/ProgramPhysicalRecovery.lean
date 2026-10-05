import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.ProgramRecovery
import UEOT.V3.Compression.Objecthood.CanonicalStationaryRepair
import UEOT.V3.Compression.Objecthood.EventualAlwaysLegitimacy

/-!
# RLSR physical recovery adapter for an internal program

These theorems depend only on trusted execution of one decoded program and the
existing physical-recovery machinery.  They are intentionally separated from
both the legacy two-mode runtime and the preferred mode-free runtime.
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
variable [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Program-specific physical recovery basin.  The policy is exactly the trusted
execution of the decoded internal program. -/
def RepairProgramRecoverableAt
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    (r : Program) (x : X) : Prop :=
  x ∈ (policyCanonicalRepairCertificate P K (T.execute r)).basin

/-- Exact expected-hitting characterization of the program-specific basin. -/
theorem repairProgramRecoverableAt_iff
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    (r : Program) (x : X) :
    RepairProgramRecoverableAt T P K r x ↔
      expectedHittingTime (stationaryKernel P (T.execute r)) x K ≠ ∞ := by
  rfl

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

end
end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
