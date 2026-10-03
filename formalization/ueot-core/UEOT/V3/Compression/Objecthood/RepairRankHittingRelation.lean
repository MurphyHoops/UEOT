import UEOT.V3.Compression.Objecthood.StrongVsStochasticRepair
namespace UEOT.V3.Compression.Objecthood
open Set
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.RecoveryHittingNonnegative
open scoped ENNReal
universe uX uA
noncomputable section

theorem canonicalDescendingRepairPotential_le_rank
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) :
    (policyCanonicalRepairCertificate P K (descendingRepairAction P K)).potential x ≤
      (repairRank P K x hx : ℝ≥0∞) := by
  simpa using endogenous_expectedHittingTime_le_rank P K x hx

theorem strongRepairable_mem_descendingStationaryBasin
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) :
    x ∈ StationaryRepairBasin P K (descendingRepairAction P K) := by
  change expectedHittingTime
    (stationaryKernel P (descendingRepairAction P K)) x K ≠ ∞
  exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
    (endogenous_expectedHittingTime_le_rank P K x hx)

theorem stationaryRepairValue_le_rank_of_strongRepairable
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) :
    stationaryRepairValue P K x ≤ (repairRank P K x hx : ℝ≥0∞) := by
  exact (stationaryRepairValue_le_policy P K x (descendingRepairAction P K)).trans
    (endogenous_expectedHittingTime_le_rank P K x hx)

theorem strongRepairable_mem_maximalStationaryRepairBasin
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) :
    x ∈ StationaryRepairBasin P K (maximalStationaryRepairPolicy P K) := by
  rw [maximalStationaryRepairBasin_eq_exists_policy P K]
  exact ⟨descendingRepairAction P K,
    strongRepairable_mem_descendingStationaryBasin P K x hx⟩

end
end UEOT.V3.Compression.Objecthood
