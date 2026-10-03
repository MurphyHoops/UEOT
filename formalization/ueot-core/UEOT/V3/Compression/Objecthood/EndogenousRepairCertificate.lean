import UEOT.V3.Compression.Objecthood.EndogenousRepairRank
import UEOT.V3.Compression.Objecthood.PhysicalRecovery

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.DynamicsKernel
open UEOT.V3.RecoveryHittingNonnegative
open scoped ENNReal ProbabilityTheory

universe uX uA

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A] [Nonempty A]

noncomputable def endogenousRepairPotential
    (P : X → A → PMF X) (K : Set X) (x : X) : ℝ≥0∞ := by
  classical
  if hx : StrongRepairable P K x then
    exact (repairRank P K x hx : ℝ≥0∞)
  else
    exact ∞

theorem endogenousRepairPotential_ne_top_iff
    (P : X → A → PMF X) (K : Set X) (x : X) :
    endogenousRepairPotential P K x ≠ ∞ ↔ StrongRepairable P K x := by
  classical
  constructor
  · intro hfin
    by_contra hx
    simp [endogenousRepairPotential, hx] at hfin
  · intro hx
    simp [endogenousRepairPotential, hx, ENNReal.natCast_ne_top]

theorem endogenousRepairPotential_eq_zero_of_mem
    (P : X → A → PMF X) (K : Set X) {x : X}
    (hxK : x ∈ K) :
    endogenousRepairPotential P K x = 0 := by
  classical
  have hx : StrongRepairable P K x := ⟨0, by simpa using hxK⟩
  have hr : repairRank P K x hx = 0 :=
    (repairRank_eq_zero_iff_mem P K x hx).2 hxK
  simp [endogenousRepairPotential, hx, hr]

theorem endogenousRepairPotential_le_rank_of_mem_iter
    (P : X → A → PMF X) (K : Set X) {x : X} {n : ℕ}
    (hx : x ∈ repairIter P K n) :
    endogenousRepairPotential P K x ≤ (n : ℝ≥0∞) := by
  classical
  have hxR : StrongRepairable P K x := ⟨n, hx⟩
  have hr : repairRank P K x hxR ≤ n :=
    repairRank_le_of_mem P K x hxR hx
  simp only [endogenousRepairPotential, dif_pos hxR]
  exact_mod_cast hr

theorem endogenousRepair_lintegral_le_previous_rank
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) (hxK : x ∉ K) :
    ∃ n : ℕ,
      repairRank P K x hx = n + 1 ∧
      (∫⁻ y, endogenousRepairPotential P K y
        ∂stationaryKernel P (descendingRepairAction P K) x) ≤
        (n : ℝ≥0∞) := by
  classical
  obtain ⟨n, hr, hs⟩ :=
    descendingRepairAction_staysIn_previous P K x hx hxK
  refine ⟨n, hr, ?_⟩
  rw [stationaryKernel_apply]
  have hRmeas : MeasurableSet (repairIter P K n) :=
    (Set.toFinite (repairIter P K n)).measurableSet
  have hmass :
      (P x (descendingRepairAction P K x)).toMeasure
        (repairIter P K n) = 1 :=
    (staysIn_iff_toMeasure_eq_one _ hRmeas).1 hs
  have hae : ∀ᵐ y ∂(P x (descendingRepairAction P K x)).toMeasure,
      y ∈ repairIter P K n := by
    apply (ae_mem_iff_measure_eq hRmeas.nullMeasurableSet).2
    simpa using hmass
  calc
    (∫⁻ y, endogenousRepairPotential P K y
        ∂(P x (descendingRepairAction P K x)).toMeasure)
        ≤ ∫⁻ _y, (n : ℝ≥0∞)
            ∂(P x (descendingRepairAction P K x)).toMeasure := by
          apply lintegral_mono_ae
          filter_upwards [hae] with y hy
          exact endogenousRepairPotential_le_rank_of_mem_iter P K hy
    _ = (n : ℝ≥0∞) := by simp

theorem endogenousRepair_drift
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) :
    ∀ z, z ∉ K →
      (∫⁻ y, endogenousRepairPotential P K y
        ∂stationaryKernel P (descendingRepairAction P K) z) + 1 ≤
        endogenousRepairPotential P K z := by
  intro z hzK
  classical
  by_cases hz : StrongRepairable P K z
  · obtain ⟨n, hr, hint⟩ :=
      endogenousRepair_lintegral_le_previous_rank P K z hz hzK
    calc
      (∫⁻ y, endogenousRepairPotential P K y
          ∂stationaryKernel P (descendingRepairAction P K) z) + 1
          ≤ (n : ℝ≥0∞) + 1 := add_le_add hint le_rfl
      _ = ((n + 1 : ℕ) : ℝ≥0∞) := by norm_num
      _ = endogenousRepairPotential P K z := by
        simp [endogenousRepairPotential, hz, hr]
  · simp [endogenousRepairPotential, hz]

noncomputable def endogenousPhysicalRepairCertificate
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) :
    PhysicalRepairCertificate P K where
  repairPolicy := descendingRepairAction P K
  potential := endogenousRepairPotential P K
  drift := 1
  target_measurable := (Set.toFinite K).measurableSet
  potential_measurable := measurable_of_finite _
  drift_ne_zero := one_ne_zero
  drift_ne_top := ENNReal.one_ne_top
  drift_condition := endogenousRepair_drift P K

theorem endogenousPhysicalRepair_basin_eq
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) :
    (endogenousPhysicalRepairCertificate P K).basin =
      {x | StrongRepairable P K x} := by
  ext x
  change endogenousRepairPotential P K x ≠ ∞ ↔ StrongRepairable P K x
  exact endogenousRepairPotential_ne_top_iff P K x

theorem endogenous_expectedHittingTime_le_rank
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) :
    expectedHittingTime
      (stationaryKernel P (descendingRepairAction P K)) x K ≤
      (repairRank P K x hx : ℝ≥0∞) := by
  let C := endogenousPhysicalRepairCertificate P K
  have h := C.expectedHittingTime_le x
  change expectedHittingTime
      (stationaryKernel P (descendingRepairAction P K)) x K ≤
    endogenousRepairPotential P K x / 1 at h
  simpa [endogenousRepairPotential, hx] using h

theorem endogenous_eventually_hits_ae
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) {x : X}
    (hx : StrongRepairable P K x) :
    ∀ᵐ omega ∂homTrajMeasure (Measure.dirac x)
        (stationaryKernel P (descendingRepairAction P K)),
      ∃ n : ℕ, omega n ∈ K := by
  let C := endogenousPhysicalRepairCertificate P K
  have hxC : x ∈ C.basin := by
    rw [endogenousPhysicalRepair_basin_eq]
    exact hx
  simpa [C, endogenousPhysicalRepairCertificate] using
    C.eventually_hits_ae_of_mem_basin hxC

end UEOT.V3.Compression.Objecthood
