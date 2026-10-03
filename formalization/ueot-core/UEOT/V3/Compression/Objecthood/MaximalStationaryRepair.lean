import UEOT.V3.Compression.Objecthood.StationaryRepairPatching
namespace UEOT.V3.Compression.Objecthood
open Set Finset MeasureTheory
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingPoisson
open scoped ENNReal
universe uX uA
noncomputable section

noncomputable def stationaryRepairValue
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X) : ℝ≥0∞ := by
  letI : Fintype (X → A) := Fintype.ofFinite _
  exact (Finset.univ : Finset (X → A)).inf' Finset.univ_nonempty
    (fun pi => expectedHittingTime (stationaryKernel P pi) x K)

noncomputable def minimizingRepairPolicyAt
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X) : X → A := by
  letI : Fintype (X → A) := Fintype.ofFinite _
  exact Classical.choose (Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset (X → A)).Nonempty)
    (fun pi => expectedHittingTime (stationaryKernel P pi) x K))

theorem stationaryRepairValue_eq_minimizing
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X) :
    stationaryRepairValue P K x =
      expectedHittingTime
        (stationaryKernel P (minimizingRepairPolicyAt P K x)) x K := by
  letI : Fintype (X → A) := Fintype.ofFinite _
  unfold stationaryRepairValue minimizingRepairPolicyAt
  exact (Classical.choose_spec (Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset (X → A)).Nonempty)
    (fun pi => expectedHittingTime (stationaryKernel P pi) x K))).2

theorem stationaryRepairValue_le_policy
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X) (pi : X → A) :
    stationaryRepairValue P K x ≤
      expectedHittingTime (stationaryKernel P pi) x K := by
  letI : Fintype (X → A) := Fintype.ofFinite _
  unfold stationaryRepairValue
  exact Finset.inf'_le _ (Finset.mem_univ pi)

noncomputable def maximalStationaryRepairPolicy
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) : X → A :=
  fun x => minimizingRepairPolicyAt P K x x

 theorem maximalStationaryRepairKernel_at
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X) :
    stationaryKernel P (maximalStationaryRepairPolicy P K) x =
      stationaryKernel P (minimizingRepairPolicyAt P K x) x := by
  rfl

noncomputable def maximalStationaryRepairCertificate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) : PhysicalRepairCertificate P K where
  repairPolicy := maximalStationaryRepairPolicy P K
  potential := stationaryRepairValue P K
  drift := 1
  target_measurable := (Set.toFinite K).measurableSet
  potential_measurable := measurable_of_finite _
  drift_ne_zero := by simp
  drift_ne_top := by simp
  drift_condition := by
    intro z hz
    let piZ := minimizingRepairPolicyAt P K z
    have hstep := expectedHittingTime_first_step_ennreal
      (stationaryKernel P piZ) z K (Set.toFinite K).measurableSet hz
    have hmono :
        (∫⁻ y, stationaryRepairValue P K y ∂stationaryKernel P piZ z) ≤
          ∫⁻ y, expectedHittingTime (stationaryKernel P piZ) y K
            ∂stationaryKernel P piZ z :=
      lintegral_mono fun y => stationaryRepairValue_le_policy P K y piZ
    change
      (∫⁻ y, stationaryRepairValue P K y
        ∂stationaryKernel P (maximalStationaryRepairPolicy P K) z) + 1 ≤
        stationaryRepairValue P K z
    rw [maximalStationaryRepairKernel_at P K z]
    calc
      (∫⁻ y, stationaryRepairValue P K y ∂stationaryKernel P piZ z) + 1 =
          1 + (∫⁻ y, stationaryRepairValue P K y ∂stationaryKernel P piZ z) := by
            rw [add_comm]
      _ ≤ 1 + (∫⁻ y, expectedHittingTime (stationaryKernel P piZ) y K
            ∂stationaryKernel P piZ z) := by
          exact add_le_add_right hmono 1
      _ = expectedHittingTime (stationaryKernel P piZ) z K := hstep.symm
      _ = stationaryRepairValue P K z := by
          symm
          exact stationaryRepairValue_eq_minimizing P K z

 theorem mem_maximalCertificate_basin_iff_exists_policy
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X) :
    x ∈ (maximalStationaryRepairCertificate P K).basin ↔
      ∃ pi : X → A, x ∈ StationaryRepairBasin P K pi := by
  change stationaryRepairValue P K x ≠ ∞ ↔
    ∃ pi : X → A, expectedHittingTime (stationaryKernel P pi) x K ≠ ∞
  constructor
  · intro h
    refine ⟨minimizingRepairPolicyAt P K x, ?_⟩
    rw [← stationaryRepairValue_eq_minimizing P K x]
    exact h
  · rintro ⟨pi, hpi⟩
    exact ne_top_of_le_ne_top hpi (stationaryRepairValue_le_policy P K x pi)

 theorem maximalStationaryRepairBasin_eq_exists_policy
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) :
    StationaryRepairBasin P K (maximalStationaryRepairPolicy P K) =
      {x | ∃ pi : X → A, x ∈ StationaryRepairBasin P K pi} := by
  ext x
  constructor
  · intro hx
    exact ⟨maximalStationaryRepairPolicy P K, hx⟩
  · intro hx
    have hxC : x ∈ (maximalStationaryRepairCertificate P K).basin :=
      (mem_maximalCertificate_basin_iff_exists_policy P K x).2 hx
    exact (maximalStationaryRepairCertificate P K).expectedHittingTime_ne_top_of_mem_basin hxC

end
end UEOT.V3.Compression.Objecthood
