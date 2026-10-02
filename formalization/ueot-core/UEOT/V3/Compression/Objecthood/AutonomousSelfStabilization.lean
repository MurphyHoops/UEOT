import UEOT.V3.Compression.Objecthood.PhysicalRecovery
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Track O / O5 — finite autonomous constitutive self-stabilization

O3 establishes controller-level closure plus convergence when the physical
state is already inside the P-PER winning kernel. O4 establishes physical
recovery to a target under an explicit P-REC repair policy. O5 combines these
into one autonomous hybrid dynamics with no informative external action.

Outside the winning kernel the internal transition uses the certified physical
repair policy. Inside the kernel it switches automatically to O2 controller
repair and constitutive closure. A single lifted Lyapunov potential then
certifies positive drift toward the full functional legitimate domain, so the
same hybrid trajectory has finite expected repair time and reaches legitimate
organization almost surely.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityStrategy
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.Compression.CrossTrack
open scoped ENNReal ProbabilityTheory

universe uX uA

noncomputable section

/-- Single autonomous repair dynamics.

* outside `K`: use the certified physical repair policy and preserve the stored
  controller while the physical carrier is being recovered;
* inside `K`: invoke O2 controller repair, which repairs the internal
  controller before selecting the physical action.

The external action remains `Unit`; the mode switch is a function of internal
state only. -/
def autonomousRepairLift
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K) :
    ConstitutiveState X A → Unit → PMF (ConstitutiveState X A) :=
  fun z _ => by
    classical
    exact if z.1 ∈ K then controllerRepairLift P K hfix z ()
      else PMF.map (fun y => (y, z.2)) (P z.1 (R.repairPolicy z.1))

/-- Lift the physical P-REC potential to reflexive constitutive state.

The additional `R.drift` unit outside legitimate organization pays exactly for
one controller-repair step after the physical state reaches `K`. -/
def autonomousRepairPotential
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (R : PhysicalRepairCertificate P K)
    (z : ConstitutiveState X A) : ℝ≥0∞ := by
  classical
  exact if z.1 ∈ K then
      if PreservingController P K z.2 then 0 else R.drift
    else R.potential z.1 + R.drift

/-- No external `Unit` value can affect the autonomous hybrid transition. -/
theorem autonomousRepairLift_external_action_irrelevant
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    (z : ConstitutiveState X A) (u v : Unit) :
    autonomousRepairLift P K hfix R z u =
      autonomousRepairLift P K hfix R z v := by
  cases u
  cases v
  rfl

/-- The lifted repair potential vanishes exactly on every state already known
to be legitimate (the converse is intentionally not needed). -/
theorem autonomousRepairPotential_eq_zero_of_legitimate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (R : PhysicalRepairCertificate P K)
    {z : ConstitutiveState X A}
    (hz : z ∈ legitimateConstitutiveDomain P K) :
    autonomousRepairPotential P K R z = 0 := by
  simp [autonomousRepairPotential, hz.1, hz.2]

/-- Once legitimate, the hybrid dynamics uses O2 and remains legitimate. -/
theorem autonomousRepairLift_staysIn_legitimate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    {z : ConstitutiveState X A}
    (hz : z ∈ legitimateConstitutiveDomain P K) :
    StaysIn (autonomousRepairLift P K hfix R z ())
      (legitimateConstitutiveDomain P K) := by
  simp [autonomousRepairLift, hz.1]
  exact controllerRepairLift_staysIn_legitimate P K hfix hz

/-- From any controller state whose physical coordinate is already in `K`, the
hybrid dynamics enters legitimate organization in one step. -/
theorem autonomousRepairLift_enters_legitimate_of_mem_K
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    {z : ConstitutiveState X A}
    (hx : z.1 ∈ K) :
    StaysIn (autonomousRepairLift P K hfix R z ())
      (legitimateConstitutiveDomain P K) := by
  simp [autonomousRepairLift, hx]
  exact controllerRepairLift_enters_legitimate P K hfix hx

/-- Outside `K`, integrating `W ∘ fst + drift` against the hybrid reflexive
transition is exactly the corresponding physical repair-kernel integral. -/
theorem autonomousRepairLift_lintegral_W_add_d_outside
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    (z : ConstitutiveState X A) (hz : z.1 ∉ K) :
    (∫⁻ w, (R.potential w.1 + R.drift)
      ∂stationaryKernel (autonomousRepairLift P K hfix R)
        noExternalControl z) =
    (∫⁻ y, (R.potential y + R.drift)
      ∂stationaryKernel P R.repairPolicy z.1) := by
  rw [stationaryKernel_apply, stationaryKernel_apply]
  simp only [autonomousRepairLift, hz, if_false]
  let f : X → ConstitutiveState X A := fun y => (y, z.2)
  have hf : Measurable f := measurable_of_finite f
  have hm :
      (P z.1 (R.repairPolicy z.1)).toMeasure.map f =
        (PMF.map f (P z.1 (R.repairPolicy z.1))).toMeasure :=
    PMF.toMeasure_map f (P z.1 (R.repairPolicy z.1)) hf
  rw [← hm]
  have hInt : Measurable (fun w : ConstitutiveState X A =>
      R.potential w.1 + R.drift) := measurable_of_finite _
  rw [lintegral_map hInt hf]

/-- Pointwise comparison used to inherit the physical P-REC drift. -/
theorem autonomousRepairPotential_le_W_add_d
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (R : PhysicalRepairCertificate P K)
    (z : ConstitutiveState X A) :
    autonomousRepairPotential P K R z ≤ R.potential z.1 + R.drift := by
  classical
  by_cases hx : z.1 ∈ K
  · by_cases hc : PreservingController P K z.2
    · simp [autonomousRepairPotential, hx, hc]
    · simp [autonomousRepairPotential, hx, hc]
  · simp [autonomousRepairPotential, hx]

/-- At a physically safe but controller-corrupted state, one hybrid step lands
entirely in zero-potential legitimate organization. -/
theorem autonomousRepair_lintegral_zero_inside_bad
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    (z : ConstitutiveState X A)
    (hx : z.1 ∈ K) :
    (∫⁻ w, autonomousRepairPotential P K R w
      ∂stationaryKernel (autonomousRepairLift P K hfix R)
        noExternalControl z) = 0 := by
  let Q := autonomousRepairLift P K hfix R
  let L := legitimateConstitutiveDomain P K
  have hs : StaysIn (Q z ()) L := by
    simpa [Q, L] using
      autonomousRepairLift_enters_legitimate_of_mem_K P K hfix R hx
  have hL : MeasurableSet L := (Set.toFinite L).measurableSet
  have hm : (Q z ()).toMeasure L = 1 :=
    (staysIn_iff_toMeasure_eq_one (Q z ()) hL).1 hs
  have hae : ∀ᵐ w ∂(Q z ()).toMeasure, w ∈ L := by
    apply (ae_mem_iff_measure_eq hL.nullMeasurableSet).2
    simpa using hm
  rw [stationaryKernel_apply]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hae] with w hw
  exact autonomousRepairPotential_eq_zero_of_legitimate P K R hw

/-- **O5 drift theorem.** The single autonomous hybrid dynamics satisfies the
same positive P-REC drift constant toward the full legitimate constitutive
domain. -/
theorem autonomousRepair_drift
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K) :
    ∀ z, z ∉ legitimateConstitutiveDomain P K →
      (∫⁻ w, autonomousRepairPotential P K R w
        ∂stationaryKernel (autonomousRepairLift P K hfix R)
          noExternalControl z) + R.drift ≤
        autonomousRepairPotential P K R z := by
  intro z hz
  classical
  by_cases hx : z.1 ∈ K
  · have hbad : ¬ PreservingController P K z.2 := by
      intro hc
      exact hz ⟨hx, hc⟩
    rw [autonomousRepair_lintegral_zero_inside_bad P K hfix R z hx]
    simp [autonomousRepairPotential, hx, hbad]
  · have hmono :
        (∫⁻ w, autonomousRepairPotential P K R w
          ∂stationaryKernel (autonomousRepairLift P K hfix R)
            noExternalControl z) ≤
        (∫⁻ w, (R.potential w.1 + R.drift)
          ∂stationaryKernel (autonomousRepairLift P K hfix R)
            noExternalControl z) :=
      lintegral_mono (autonomousRepairPotential_le_W_add_d P K R)
    rw [autonomousRepairLift_lintegral_W_add_d_outside
      P K hfix R z hx] at hmono
    have hsplit :
        (∫⁻ y, (R.potential y + R.drift)
          ∂stationaryKernel P R.repairPolicy z.1) =
        (∫⁻ y, R.potential y
          ∂stationaryKernel P R.repairPolicy z.1) + R.drift := by
      rw [lintegral_add_right R.potential measurable_const]
      simp
    rw [hsplit] at hmono
    have hphys := R.drift_condition z.1 hx
    have hadd := add_le_add hphys (le_refl R.drift)
    calc
      (∫⁻ w, autonomousRepairPotential P K R w
          ∂stationaryKernel (autonomousRepairLift P K hfix R)
            noExternalControl z) + R.drift
          ≤ ((∫⁻ y, R.potential y
              ∂stationaryKernel P R.repairPolicy z.1) + R.drift) +
              R.drift := add_le_add hmono (le_refl R.drift)
      _ ≤ R.potential z.1 + R.drift := by
          simpa [add_assoc] using hadd
      _ = autonomousRepairPotential P K R z := by
          simp [autonomousRepairPotential, hx]

/-- The O5 hybrid itself is a P-REC physical-repair certificate whose target is
the full legitimate constitutive domain. -/
def autonomousRepairPhysicalCertificate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K) :
    PhysicalRepairCertificate
      (autonomousRepairLift P K hfix R)
      (legitimateConstitutiveDomain P K) where
  repairPolicy := noExternalControl
  potential := autonomousRepairPotential P K R
  drift := R.drift
  target_measurable :=
    (Set.toFinite (legitimateConstitutiveDomain P K)).measurableSet
  potential_measurable := measurable_of_finite _
  drift_ne_zero := R.drift_ne_zero
  drift_ne_top := R.drift_ne_top
  drift_condition := autonomousRepair_drift P K hfix R

/-- Physical membership in the O4 repair basin implies membership in the O5
hybrid repair basin for any stored controller. -/
theorem mem_autonomousRepair_basin_of_physical_basin
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    {z : ConstitutiveState X A}
    (hz : z.1 ∈ R.basin) :
    z ∈ (autonomousRepairPhysicalCertificate P K hfix R).basin := by
  change R.potential z.1 ≠ ∞ at hz
  change autonomousRepairPotential P K R z ≠ ∞
  classical
  by_cases hx : z.1 ∈ K
  · by_cases hc : PreservingController P K z.2
    · simp [autonomousRepairPotential, hx, hc]
    · simp [autonomousRepairPotential, hx, hc, R.drift_ne_top]
  · simp [autonomousRepairPotential, hx, hz, R.drift_ne_top]

/-- Quantitative expected repair-time bound for the single autonomous hybrid
dynamics. -/
theorem autonomousRepair_expectedHittingTime_le
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    (z : ConstitutiveState X A) :
    expectedHittingTime
      (stationaryKernel (autonomousRepairLift P K hfix R)
        noExternalControl)
      z (legitimateConstitutiveDomain P K) ≤
    autonomousRepairPotential P K R z / R.drift :=
  (autonomousRepairPhysicalCertificate P K hfix R).expectedHittingTime_le z

/-- **O5 almost-sure autonomous repair.** Any reflexive state whose physical
coordinate belongs to the O4 repair basin reaches legitimate organization
almost surely under the same autonomous hybrid trajectory. -/
theorem autonomousRepair_eventually_legitimate_ae
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    {z : ConstitutiveState X A}
    (hz : z.1 ∈ R.basin) :
    ∀ᵐ omega ∂stationaryTrajMeasure
        (autonomousRepairLift P K hfix R) noExternalControl (PMF.pure z),
      ∃ n : ℕ, omega n ∈ legitimateConstitutiveDomain P K := by
  let C := autonomousRepairPhysicalCertificate P K hfix R
  have hzC : z ∈ C.basin := by
    simpa [C] using
      mem_autonomousRepair_basin_of_physical_basin P K hfix R hz
  simpa [C, autonomousRepairPhysicalCertificate] using
    C.stationaryTrajMeasure_eventually_hits_ae_of_mem_basin hzC

/-- O5 package: exact source winning-kernel provenance together with the
physical repair certificate that makes the unified autonomous hybrid
self-stabilizing on its certified basin. -/
structure SelfStabilizingConstitutiveCertificate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (V : Set X) where
  controller : ControllerSelfStabilizationCertificate P V
  physicalRepair : PhysicalRepairCertificate P controller.K

namespace SelfStabilizingConstitutiveCertificate

/-- The O5 package inherits autonomous almost-sure repair from every state in
the physical repair basin, independent of the stored controller. -/
theorem eventually_legitimate_ae
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    {P : X → A → PMF X} {V : Set X}
    (C : SelfStabilizingConstitutiveCertificate P V)
    {z : ConstitutiveState X A}
    (hz : z.1 ∈ C.physicalRepair.basin) :
    ∀ᵐ omega ∂stationaryTrajMeasure
        (autonomousRepairLift P C.controller.K
          C.controller.source_fixed C.physicalRepair)
        noExternalControl (PMF.pure z),
      ∃ n : ℕ,
        omega n ∈ legitimateConstitutiveDomain P C.controller.K :=
  autonomousRepair_eventually_legitimate_ae
    P C.controller.K C.controller.source_fixed C.physicalRepair hz

/-- The same O5 dynamics is closed after it reaches legitimate organization. -/
theorem closure
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    {P : X → A → PMF X} {V : Set X}
    (C : SelfStabilizingConstitutiveCertificate P V)
    {z : ConstitutiveState X A}
    (hz : z ∈ legitimateConstitutiveDomain P C.controller.K) :
    StaysIn
      (autonomousRepairLift P C.controller.K
        C.controller.source_fixed C.physicalRepair z ())
      (legitimateConstitutiveDomain P C.controller.K) :=
  autonomousRepairLift_staysIn_legitimate
    P C.controller.K C.controller.source_fixed C.physicalRepair hz

end SelfStabilizingConstitutiveCertificate

end

end UEOT.V3.Compression.Objecthood
