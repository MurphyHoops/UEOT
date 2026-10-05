import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.SafeJointRecovery
import UEOT.V3.Compression.Objecthood.AbsorbedRepairHittingSemantics
import UEOT.V3.Compression.Objecthood.ControllerRepair

/-!
# RLSR-T3 — repair outside, preserve inside

A physical repair certificate only needs to control dynamics until the first hit
of the target.  After entry, object identity needs a preserving controller.
This module patches those roles into one canonical policy and proves that the
patch keeps the exact expected hitting time while adding target preservation.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingBound
open UEOT.V3.Compression.Objecthood
open scoped ENNReal ProbabilityTheory

universe uX uA uP

noncomputable section

variable {X : Type uX} {A : Type uA} {Program : Type uP}
variable [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Finite-horizon tail-sum semantics are unchanged when two stationary
policies induce the same physical kernel outside the target. -/
theorem truncatedExpectedHittingTime_stationary_eq_of_policyKernel_eq_outside
    (P : X → A → PMF X) (K : Set X)
    (pi rho : X → A)
    (hout : ∀ x, x ∉ K → P x (pi x) = P x (rho x))
    (x : X) (N : ℕ) :
    truncatedExpectedHittingTime (stationaryKernel P pi) x K N =
      truncatedExpectedHittingTime (stationaryKernel P rho) x K N := by
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  unfold truncatedExpectedHittingTime
  apply Finset.sum_congr rfl
  intro n hn
  exact UEOT.V3.Compression.Objecthood.survivalProb_eq_of_eq_outside
    (stationaryKernel P pi) (stationaryKernel P rho) K hK
    (fun z hz => by
      change (P z (pi z)).toMeasure = (P z (rho z)).toMeasure
      exact congrArg (fun μ : PMF X => μ.toMeasure) (hout z hz)) n x

/-- Any two stationary policies inducing identical physical kernels outside the
target have exactly the same expected first-hitting time of that target. -/
theorem expectedHittingTime_stationary_eq_of_policyKernel_eq_outside
    (P : X → A → PMF X) (K : Set X)
    (pi rho : X → A)
    (hout : ∀ x, x ∉ K → P x (pi x) = P x (rho x))
    (x : X) :
    expectedHittingTime (stationaryKernel P pi) x K =
      expectedHittingTime (stationaryKernel P rho) x K := by
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  rw [expectedHittingTime_eq_iSup_truncatedExpectedHittingTime
      (stationaryKernel P pi) x K hK,
    expectedHittingTime_eq_iSup_truncatedExpectedHittingTime
      (stationaryKernel P rho) x K hK]
  exact iSup_congr fun N =>
    truncatedExpectedHittingTime_stationary_eq_of_policyKernel_eq_outside
      P K pi rho hout x N

/-- Canonical composite law: use one preserving viability witness inside `K`,
and the supplied recovery policy outside `K`. -/
noncomputable def repairThenPreservePolicy
    [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (rho : X → A) : X → A := by
  classical
  exact fun x => if x ∈ K then
    canonicalPreservingController P K hfix x
  else rho x

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- The composite policy is preserving on the target by construction. -/
theorem repairThenPreservePolicy_preserving
    [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (rho : X → A) :
    PreservingController P K (repairThenPreservePolicy P K hfix rho) := by
  intro x hx
  have hpres := canonicalPreservingController_preserving P K hfix
  simpa [repairThenPreservePolicy, hx] using hpres x hx

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- Outside the target the composite policy is literally the original recovery
policy. -/
theorem repairThenPreservePolicy_eq_outside
    [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (rho : X → A) {x : X} (hx : x ∉ K) :
    repairThenPreservePolicy P K hfix rho x = rho x := by
  simp [repairThenPreservePolicy, hx]

/-- Patching preservation inside the target does not change first-hitting-time
semantics at all. -/
theorem repairThenPreservePolicy_expectedHittingTime_eq
    [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (rho : X → A) (x : X) :
    expectedHittingTime
        (stationaryKernel P (repairThenPreservePolicy P K hfix rho)) x K =
      expectedHittingTime (stationaryKernel P rho) x K := by
  apply expectedHittingTime_stationary_eq_of_policyKernel_eq_outside
  intro z hz
  simp [repairThenPreservePolicy, hz]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- Dynamics-level implementation of the composite law automatically gives
carrier preservation; no second `hvalid` assumption is needed. -/
theorem repairProgramValid_of_dynamicsImplements_repairThenPreserve
    [Nonempty A]
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (rho : X → A) (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T P r
      (repairThenPreservePolicy P K hfix rho)) :
    RepairProgramValid T P K r := by
  intro x hx y hy
  have hpres := repairThenPreservePolicy_preserving P K hfix rho
  rw [himpl x] at hy
  exact hpres x hx hy

/-- Dynamics-level implementation of the composite law also preserves the exact
recovery basin of the original recovery policy. -/
theorem repairProgramRecoverableAt_of_dynamicsImplements_repairThenPreserve
    [Nonempty A]
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (rho : X → A) (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T P r
      (repairThenPreservePolicy P K hfix rho))
    {x : X}
    (hx : expectedHittingTime (stationaryKernel P rho) x K ≠ ⊤) :
    RepairProgramRecoverableAt T P K r x := by
  apply (repairProgramRecoverableAt_iff T P K r x).2
  calc
    expectedHittingTime (stationaryKernel P (T.execute r)) x K =
        expectedHittingTime
          (stationaryKernel P (repairThenPreservePolicy P K hfix rho)) x K := by
      apply expectedHittingTime_stationary_eq_of_policyKernel_eq_outside
      intro z hz
      exact himpl z
    _ = expectedHittingTime (stationaryKernel P rho) x K :=
      repairThenPreservePolicy_expectedHittingTime_eq P K hfix rho x
    _ ≠ ⊤ := hx

end
end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
