import UEOT.V3.Compression.Objecthood.StationaryRepairBasin
namespace UEOT.V3.Compression.Objecthood
open Set MeasureTheory
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingPoisson
open scoped ENNReal
universe uX uA
noncomputable section

noncomputable def patchRepairPolicy
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi1 pi2 : X → A) : X → A :=
  fun x => if expectedHittingTime (stationaryKernel P pi1) x K ≤
      expectedHittingTime (stationaryKernel P pi2) x K then pi1 x else pi2 x

noncomputable def patchedStationaryRepairCertificate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi1 pi2 : X → A) :
    PhysicalRepairCertificate P K where
  repairPolicy := patchRepairPolicy P K pi1 pi2
  potential := fun x => min
    (expectedHittingTime (stationaryKernel P pi1) x K)
    (expectedHittingTime (stationaryKernel P pi2) x K)
  drift := 1
  target_measurable := (Set.toFinite K).measurableSet
  potential_measurable := measurable_of_finite _
  drift_ne_zero := by simp
  drift_ne_top := by simp
  drift_condition := by
    intro z hz
    let V1 := fun x => expectedHittingTime (stationaryKernel P pi1) x K
    let V2 := fun x => expectedHittingTime (stationaryKernel P pi2) x K
    by_cases hle : V1 z ≤ V2 z
    · have hstep := expectedHittingTime_first_step_ennreal
        (stationaryKernel P pi1) z K (Set.toFinite K).measurableSet hz
      have hmono :
          (∫⁻ y, min (V1 y) (V2 y) ∂stationaryKernel P pi1 z) ≤
            ∫⁻ y, V1 y ∂stationaryKernel P pi1 z :=
        lintegral_mono fun y => min_le_left _ _
      change
        (∫⁻ y, min (V1 y) (V2 y)
          ∂stationaryKernel P (patchRepairPolicy P K pi1 pi2) z) + 1 ≤
          min (V1 z) (V2 z)
      rw [show stationaryKernel P (patchRepairPolicy P K pi1 pi2) z =
          stationaryKernel P pi1 z by
        rw [stationaryKernel_apply, stationaryKernel_apply]
        simp [patchRepairPolicy, V1, V2, hle]]
      calc
        (∫⁻ y, min (V1 y) (V2 y) ∂stationaryKernel P pi1 z) + 1 =
            1 + (∫⁻ y, min (V1 y) (V2 y) ∂stationaryKernel P pi1 z) := by
              rw [add_comm]
        _ ≤ 1 + (∫⁻ y, V1 y ∂stationaryKernel P pi1 z) := by
              exact add_le_add_right hmono 1
        _ = V1 z := by simpa [V1] using hstep.symm
        _ = min (V1 z) (V2 z) := by symm; exact min_eq_left hle
    · have h21 : V2 z ≤ V1 z := le_of_not_ge hle
      have hstep := expectedHittingTime_first_step_ennreal
        (stationaryKernel P pi2) z K (Set.toFinite K).measurableSet hz
      have hmono :
          (∫⁻ y, min (V1 y) (V2 y) ∂stationaryKernel P pi2 z) ≤
            ∫⁻ y, V2 y ∂stationaryKernel P pi2 z :=
        lintegral_mono fun y => min_le_right _ _
      change
        (∫⁻ y, min (V1 y) (V2 y)
          ∂stationaryKernel P (patchRepairPolicy P K pi1 pi2) z) + 1 ≤
          min (V1 z) (V2 z)
      rw [show stationaryKernel P (patchRepairPolicy P K pi1 pi2) z =
          stationaryKernel P pi2 z by
        rw [stationaryKernel_apply, stationaryKernel_apply]
        simp [patchRepairPolicy, V1, V2, hle]]
      calc
        (∫⁻ y, min (V1 y) (V2 y) ∂stationaryKernel P pi2 z) + 1 =
            1 + (∫⁻ y, min (V1 y) (V2 y) ∂stationaryKernel P pi2 z) := by
              rw [add_comm]
        _ ≤ 1 + (∫⁻ y, V2 y ∂stationaryKernel P pi2 z) := by
              exact add_le_add_right hmono 1
        _ = V2 z := by simpa [V2] using hstep.symm
        _ = min (V1 z) (V2 z) := by symm; exact min_eq_right h21

 theorem patchedCertificate_basin_eq_union
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi1 pi2 : X → A) :
    (patchedStationaryRepairCertificate P K pi1 pi2).basin =
      StationaryRepairBasin P K pi1 ∪ StationaryRepairBasin P K pi2 := by
  ext x
  change
    min (expectedHittingTime (stationaryKernel P pi1) x K)
        (expectedHittingTime (stationaryKernel P pi2) x K) ≠ ∞ ↔
      expectedHittingTime (stationaryKernel P pi1) x K ≠ ∞ ∨
        expectedHittingTime (stationaryKernel P pi2) x K ≠ ∞
  constructor
  · intro hmin
    by_cases h1 : expectedHittingTime (stationaryKernel P pi1) x K = ∞
    · right
      intro h2
      exact hmin ((min_eq_top).2 ⟨h1, h2⟩)
    · exact Or.inl h1
  · intro h
    intro hmin
    have hb := (min_eq_top.mp hmin)
    rcases h with h1 | h2
    · exact h1 hb.1
    · exact h2 hb.2

 theorem union_subset_patch_basin
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi1 pi2 : X → A) :
    StationaryRepairBasin P K pi1 ∪ StationaryRepairBasin P K pi2 ⊆
      StationaryRepairBasin P K (patchRepairPolicy P K pi1 pi2) := by
  intro x hx
  let C := patchedStationaryRepairCertificate P K pi1 pi2
  have hxC : x ∈ C.basin := by
    rw [patchedCertificate_basin_eq_union P K pi1 pi2]
    exact hx
  have hfin := C.expectedHittingTime_ne_top_of_mem_basin hxC
  exact hfin

end
end UEOT.V3.Compression.Objecthood
