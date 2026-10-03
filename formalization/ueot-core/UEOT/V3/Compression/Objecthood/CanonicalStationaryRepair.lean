import UEOT.V3.Compression.Objecthood.PhysicalRecovery
import UEOT.V3.RecoveryHittingPoisson

/-!
# Track O / AR0 — canonical stationary-policy repair certificate

For a fixed deterministic stationary repair policy, the canonical expected
hitting time itself supplies the PhysicalRepairCertificate potential.
The unit-drift condition is not an added Lyapunov hypothesis: it is exactly the
canonical first-step identity for the stationary Markov kernel.

This stage deliberately fixes the policy. It does not yet claim basin closure,
policy patching, maximality, or completeness relative to history-dependent or
randomized policies.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingInitial
open UEOT.V3.RecoveryHittingPoisson
open scoped ENNReal

universe uX uA

noncomputable section

/-- **AR0 canonical certificate.** For a deterministic stationary policy pi,
the canonical expected hitting time of its induced Markov kernel is a
unit-drift physical repair potential. -/
noncomputable def policyCanonicalRepairCertificate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi : X → A) :
    PhysicalRepairCertificate P K where
  repairPolicy := pi
  potential := fun x => expectedHittingTime (stationaryKernel P pi) x K
  drift := 1
  target_measurable := (Set.toFinite K).measurableSet
  potential_measurable :=
    measurable_expectedHittingTime
      (stationaryKernel P pi) (Set.toFinite K).measurableSet
  drift_ne_zero := by simp
  drift_ne_top := by simp
  drift_condition := by
    intro z hz
    have hstep :=
      expectedHittingTime_first_step_ennreal
        (stationaryKernel P pi) z K (Set.toFinite K).measurableSet hz
    calc
      (∫⁻ y, expectedHittingTime (stationaryKernel P pi) y K
          ∂stationaryKernel P pi z) + 1 =
          1 + ∫⁻ y, expectedHittingTime (stationaryKernel P pi) y K
            ∂stationaryKernel P pi z := by
              rw [add_comm]
      _ = expectedHittingTime (stationaryKernel P pi) z K := hstep.symm
      _ ≤ expectedHittingTime (stationaryKernel P pi) z K := le_rfl

@[simp]
theorem policyCanonicalRepairCertificate_policy
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi : X → A) :
    (policyCanonicalRepairCertificate P K pi).repairPolicy = pi := rfl

@[simp]
theorem policyCanonicalRepairCertificate_potential
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi : X → A) (x : X) :
    (policyCanonicalRepairCertificate P K pi).potential x =
      expectedHittingTime (stationaryKernel P pi) x K := rfl

@[simp]
theorem policyCanonicalRepairCertificate_drift
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi : X → A) :
    (policyCanonicalRepairCertificate P K pi).drift = 1 := rfl

/-- The finite-potential basin of the AR0 certificate is literally the set of
states having finite canonical expected hitting time under the fixed policy. -/
theorem policyCanonicalRepairCertificate_mem_basin_iff
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi : X → A) (x : X) :
    x ∈ (policyCanonicalRepairCertificate P K pi).basin ↔
      expectedHittingTime (stationaryKernel P pi) x K ≠ ∞ := by
  rfl

end

end UEOT.V3.Compression.Objecthood
