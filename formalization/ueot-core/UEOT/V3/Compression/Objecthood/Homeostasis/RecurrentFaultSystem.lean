import UEOT.V3.Compression.Objecthood.GeneralCausalRepairSynthesis
import UEOT.V3.Compression.Objecthood.AutonomousSelfStabilization
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Track O / RH0 — recurrent-fault system and GCR repairable carrier

This module introduces the explicit recurrent fault model authorized by #248.
Repair and fault kernels remain separately typed; long-run burden/drift claims
begin only in later RH stages.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.CrossTrack
open scoped ENNReal BigOperators ProbabilityTheory

universe uZ uX uA
noncomputable section

/-- Generic finite recurrent-homeostasis carrier.  RH0 keeps repair and fault
kernels explicitly separate; burden/drift interaction is deferred to RH1/RH2. -/
structure RecurrentHomeostasisSystem
    (Z : Type uZ) [Fintype Z] where
  legitimate : Set Z
  carrier : Set Z
  repairKernel : Z → PMF Z
  faultKernel : Z → PMF Z
  faultHazard : NNReal
  faultHazard_le_one : faultHazard ≤ 1
  potential : Z → ENNReal
  repairDrift : ENNReal
  repairDrift_ne_zero : repairDrift ≠ 0
  repairDrift_ne_top : repairDrift ≠ ∞
  legitimate_subset_carrier : legitimate ⊆ carrier
  repair_stays_carrier :
    ∀ ⦃z : Z⦄, z ∈ carrier → StaysIn (repairKernel z) carrier
  fault_stays_carrier :
    ∀ ⦃z : Z⦄, z ∈ carrier → StaysIn (faultKernel z) carrier

/-- Non-deprecated finite PMF convex mixture. -/
noncomputable def recurrentFaultMix
    {Z : Type uZ} [Fintype Z]
    (Q F : PMF Z) (epsilon : NNReal) (hepsilon : epsilon ≤ 1) : PMF Z :=
  PMF.ofFintype
    (fun z => ((1 - epsilon : NNReal) : ENNReal) * Q z +
      (epsilon : ENNReal) * F z)
    (by
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      have hQ : ∑ z, Q z = 1 := by
        simpa [tsum_fintype] using PMF.tsum_coe Q
      have hF : ∑ z, F z = 1 := by
        simpa [tsum_fintype] using PMF.tsum_coe F
      rw [hQ, hF, mul_one, mul_one]
      rw [ENNReal.coe_sub]
      exact tsub_add_cancel_of_le (by exact_mod_cast hepsilon))

@[simp] theorem recurrentFaultMix_apply
    {Z : Type uZ} [Fintype Z]
    (Q F : PMF Z) (epsilon : NNReal) (hepsilon : epsilon ≤ 1) (z : Z) :
    recurrentFaultMix Q F epsilon hepsilon z =
      ((1 - epsilon : NNReal) : ENNReal) * Q z +
        (epsilon : ENNReal) * F z := by
  simp [recurrentFaultMix, PMF.ofFintype_apply]

/-- The actual recurrent-fault transition of a system. -/
noncomputable def RecurrentHomeostasisSystem.mixedKernel
    {Z : Type uZ} [Fintype Z]
    (S : RecurrentHomeostasisSystem Z) (z : Z) : PMF Z :=
  recurrentFaultMix (S.repairKernel z) (S.faultKernel z)
    S.faultHazard S.faultHazard_le_one

/-- If repair and fault rows preserve the declared carrier, their explicit
mixture preserves it too. -/
theorem RecurrentHomeostasisSystem.mixed_stays_carrier
    {Z : Type uZ} [Fintype Z]
    (S : RecurrentHomeostasisSystem Z)
    {z : Z} (hz : z ∈ S.carrier) :
    StaysIn (S.mixedKernel z) S.carrier := by
  intro y hy
  by_contra hyB
  have hQnot : y ∉ (S.repairKernel z).support :=
    fun hyQ => hyB (S.repair_stays_carrier hz hyQ)
  have hFnot : y ∉ (S.faultKernel z).support :=
    fun hyF => hyB (S.fault_stays_carrier hz hyF)
  have hQ0 : S.repairKernel z y = 0 := by
    simpa [PMF.mem_support_iff] using hQnot
  have hF0 : S.faultKernel z y = 0 := by
    simpa [PMF.mem_support_iff] using hFnot
  have hm : S.mixedKernel z y = 0 := by
    simp [RecurrentHomeostasisSystem.mixedKernel, recurrentFaultMix_apply, hQ0, hF0]
  exact (PMF.mem_support_iff _ _).1 hy hm

/-- Constitutive carrier inherited from the GCR-complete maximal repair basin. -/
def gcrHomeostaticCarrier
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X) : Set (ConstitutiveState X A) :=
  {z | GeneralCausalAlmostSureRepairable P K z.1}

theorem legitimate_subset_gcrHomeostaticCarrier
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X) :
    legitimateConstitutiveDomain P K ⊆ gcrHomeostaticCarrier P K := by
  intro z hz
  have hzStat :
      DeterministicStationaryFiniteExpectedRepairable P K z.1 := by
    refine ⟨maximalStationaryRepairPolicy P K, ?_⟩
    exact target_subset_stationaryRepairBasin P K
      (maximalStationaryRepairPolicy P K) hz.1
  exact (generalCausalAlmostSureRepairable_iff_deterministicStationary
    P K z.1).2 hzStat

/-- The already-proved autonomous repair kernel preserves the full GCR carrier.
No new repairability assumption is introduced by RH. -/
theorem autonomousRepairLift_staysIn_gcrHomeostaticCarrier
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    {z : ConstitutiveState X A}
    (hz : z ∈ gcrHomeostaticCarrier P K) :
    StaysIn
      (autonomousRepairLift P K hfix
        (maximalStationaryRepairCertificate P K) z ())
      (gcrHomeostaticCarrier P K) := by
  let piMax := maximalStationaryRepairPolicy P K
  have hzDet :
      DeterministicStationaryFiniteExpectedRepairable P K z.1 :=
    (generalCausalAlmostSureRepairable_iff_deterministicStationary
      P K z.1).1 hz
  have hzMax : z.1 ∈ StationaryRepairBasin P K piMax := by
    exact (deterministicStationaryRepairable_iff_mem_maximalBasin P K z.1).1 hzDet
  by_cases hzK : z.1 ∈ K
  · have hleg :=
      autonomousRepairLift_enters_legitimate_of_mem_K
        P K hfix (maximalStationaryRepairCertificate P K) hzK
    intro w hw
    exact legitimate_subset_gcrHomeostaticCarrier P K (hleg hw)
  · intro w hw
    have hmap :
        w ∈ (PMF.map (fun y => (y, z.2))
          (P z.1 (piMax z.1))).support := by
      simpa [autonomousRepairLift, hzK, piMax,
        maximalStationaryRepairCertificate] using hw
    rcases (PMF.mem_support_map_iff (fun y => (y, z.2)) (P z.1 (piMax z.1)) w).1 hmap with ⟨y, hy, rfl⟩
    have hyMax : y ∈ StationaryRepairBasin P K piMax :=
      stationaryRepairBasin_support_closed P K piMax hzMax hzK hy
    have hyDet :
        DeterministicStationaryFiniteExpectedRepairable P K y :=
      (deterministicStationaryRepairable_iff_mem_maximalBasin P K y).2 hyMax
    exact (generalCausalAlmostSureRepairable_iff_deterministicStationary
      P K y).2 hyDet

/-- On the GCR carrier, the existing autonomous repair potential is finite. -/
theorem autonomousRepairPotential_ne_top_on_gcrHomeostaticCarrier
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    {z : ConstitutiveState X A}
    (hz : z ∈ gcrHomeostaticCarrier P K) :
    autonomousRepairPotential P K (maximalStationaryRepairCertificate P K) z ≠ ∞ := by
  have hx :
      z.1 ∈ (maximalStationaryRepairCertificate P K).basin :=
    (mem_maximalStationaryRepairCertificate_basin_iff_generalCausal P K z.1).2 hz
  exact mem_autonomousRepair_basin_of_physical_basin
    P K hfix (maximalStationaryRepairCertificate P K) hx

/-- RH0 Objecthood specialization. Fault support closure is the new explicit
fault admissibility input; repair-side closure is inherited from GCR/AR. -/
noncomputable def objecthoodRecurrentHomeostasisSystem
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (F : ConstitutiveState X A → PMF (ConstitutiveState X A))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : ∀ ⦃z : ConstitutiveState X A⦄,
      z ∈ gcrHomeostaticCarrier P K →
        StaysIn (F z) (gcrHomeostaticCarrier P K)) :
    RecurrentHomeostasisSystem (ConstitutiveState X A) where
  legitimate := legitimateConstitutiveDomain P K
  carrier := gcrHomeostaticCarrier P K
  repairKernel := fun z =>
    autonomousRepairLift P K hfix (maximalStationaryRepairCertificate P K) z ()
  faultKernel := F
  faultHazard := epsilon
  faultHazard_le_one := hepsilon
  potential := autonomousRepairPotential P K (maximalStationaryRepairCertificate P K)
  repairDrift := (maximalStationaryRepairCertificate P K).drift
  repairDrift_ne_zero := (maximalStationaryRepairCertificate P K).drift_ne_zero
  repairDrift_ne_top := (maximalStationaryRepairCertificate P K).drift_ne_top
  legitimate_subset_carrier := legitimate_subset_gcrHomeostaticCarrier P K
  repair_stays_carrier := by
    intro z hz
    exact autonomousRepairLift_staysIn_gcrHomeostaticCarrier P K hfix hz
  fault_stays_carrier := hF

end
end UEOT.V3.Compression.Objecthood
