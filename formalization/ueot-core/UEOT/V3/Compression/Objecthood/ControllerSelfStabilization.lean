import UEOT.V3.Compression.Objecthood.ControllerRepair

/-!
# Track O / O3 — controller self-stabilization certificate

O1 supplied a functional legitimate organization and the closure/no-repair
boundary.  O2 supplied one-step autonomous controller repair while the physical
state remains in the P-PER winning kernel.  O3 packages those ingredients and
connects them to the repository's genuine Ionescu--Tulcea trajectory measure.

The resulting certificate is explicitly controller-level: physical recovery
from outside the winning kernel remains O4.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityStrategy
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.Compression.CrossTrack

universe uX uA

noncomputable section

/-- Genuine path-level closure after the one-step controller-repair transition.
The initial path law starts at the possibly corrupted state `z`; the certified
event begins at coordinate `1`, exactly matching one-step convergence. -/
theorem controllerRepairLift_all_times_after_one
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    {z : ConstitutiveState X A}
    (hx : z.1 ∈ K) :
    stationaryTrajMeasure
      (controllerRepairLift P K hfix) noExternalControl
      (PMF.pure z)
      {omega | ∀ n : ℕ,
        omega (n + 1) ∈ legitimateConstitutiveDomain P K} = 1 := by
  let Q := controllerRepairLift P K hfix
  let L := legitimateConstitutiveDomain P K
  have hmeas : MeasurableSet L := (Set.toFinite L).measurableSet
  apply UEOT.V3.ViabilityPath.all_times_safe_eq_one
    (μ := stationaryTrajMeasure Q noExternalControl (PMF.pure z))
    (Xn := fun n omega => omega (n + 1))
    L hmeas
  · intro n
    exact measurable_pi_apply (n + 1)
  · intro n
    have hcoord :
        (stationaryTrajMeasure Q noExternalControl (PMF.pure z)).map
          (fun omega : ℕ → ConstitutiveState X A => omega (n + 1)) L = 1 := by
      rw [stationaryTrajMeasure_coordinate]
      exact (staysIn_iff_toMeasure_eq_one _ hmeas).1
        (controllerRepairLift_all_marginals_after_one P K hfix hx n)
    rw [Measure.map_apply (measurable_pi_apply (n + 1)) hmeas] at hcoord
    exact hcoord

/-- Finite controller-self-stabilization certificate.

It records the exact source winning kernel, a nonvacuous seed, closure of the
functional legitimate domain, one-step convergence from every controller state
whose physical coordinate is in the kernel, and a genuine infinite path-law
witness from time `1` onward. -/
structure ControllerSelfStabilizationCertificate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (V : Set X) where
  K : Set X
  seed : X
  kernel_sub_domain : K ⊆ V
  seed_mem : seed ∈ K
  source_fixed : viabilityStep P K = K
  source_winning : K = winningSet P V
  closure :
    ∀ z ∈ legitimateConstitutiveDomain P K,
      StaysIn (controllerRepairLift P K source_fixed z ())
        (legitimateConstitutiveDomain P K)
  controller_convergence :
    ∀ z : ConstitutiveState X A, z.1 ∈ K →
      StaysIn (controllerRepairLift P K source_fixed z ())
        (legitimateConstitutiveDomain P K)
  path_after_one :
    ∀ z : ConstitutiveState X A, z.1 ∈ K →
      stationaryTrajMeasure
        (controllerRepairLift P K source_fixed) noExternalControl
        (PMF.pure z)
        {omega | ∀ n : ℕ,
          omega (n + 1) ∈ legitimateConstitutiveDomain P K} = 1

/-- Every nonempty finite P-PER winning kernel yields an O3 controller-level
self-stabilization certificate. -/
theorem exists_controllerSelfStabilizationCertificate_of_nonempty_winningSet
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (V : Set X)
    (hwin : (winningSet P V).Nonempty) :
    Nonempty (ControllerSelfStabilizationCertificate P V) := by
  obtain ⟨n, K, hiter, hKV, hfix, hwinning, _, _⟩ :=
    UEOT.V3.ViabilitySource.p_per_03 P V
  have hK : K.Nonempty := by
    rw [hwinning]
    exact hwin
  rcases hK with ⟨seed, hseed⟩
  refine ⟨{
    K := K
    seed := seed
    kernel_sub_domain := hKV
    seed_mem := hseed
    source_fixed := hfix
    source_winning := hwinning
    closure := ?_
    controller_convergence := ?_
    path_after_one := ?_
  }⟩
  · intro z hz
    exact controllerRepairLift_staysIn_legitimate P K hfix hz
  · intro z hz
    exact controllerRepairLift_enters_legitimate P K hfix hz
  · intro z hz
    exact controllerRepairLift_all_times_after_one P K hfix hz

end

end UEOT.V3.Compression.Objecthood
