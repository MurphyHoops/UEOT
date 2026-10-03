import UEOT.V3.Compression.Objecthood.CanonicalStationaryRepair

/-!
# Track O / AR1 — fixed-policy stochastic repair basin closure

The AR0 canonical certificate identifies the repair basin for a fixed
deterministic stationary policy with finite expected hitting time. AR1 records
the structural facts needed for policy synthesis: the target is already in the
basin, and every positive-probability one-step successor of a basin state
outside the target remains in the same basin.
-/

namespace UEOT.V3.Compression.Objecthood

open Set Finset MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingFirstStep
open UEOT.V3.RecoveryHittingInitial
open UEOT.V3.RecoveryHittingPoisson
open scoped ENNReal ProbabilityTheory

universe uX uA

noncomputable section

/-- If a path starts inside the target, its canonical extended hitting time is
zero. -/
theorem hittingValue_eq_zero_of_mem_target
    {X : Type uX} [MeasurableSpace X]
    (K : Set X) (omega : ℕ → X) (h0 : omega 0 ∈ K) :
    hittingValue K omega = 0 := by
  unfold hittingValue
  apply le_antisymm
  · refine iSup_le ?_
    intro N
    have hnot : ∀ n : ℕ, omega ∉ survivalSet K n := by
      intro n hn
      have hz := (mem_survivalSet_iff K n omega).1 hn 0 (Nat.zero_le n)
      exact hz h0
    simp [truncatedHittingValue, hnot]
  · exact bot_le

/-- Starting in the target gives zero canonical expected hitting time. -/
theorem expectedHittingTime_eq_zero_of_mem_target
    {X : Type uX} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (Q : Kernel X X) [IsMarkovKernel Q]
    (x : X) (K : Set X) (hx : x ∈ K) :
    expectedHittingTime Q x K = 0 := by
  letI : ∀ n, IsMarkovKernel (homHistoryKernel Q n) :=
    fun n => isMarkovKernel_homHistoryKernel Q n
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  rw [expectedHittingTime, homTrajMeasure_dirac_eq_markovPathLaw Q x]
  unfold UEOT.V3.RecoveryHitting.markovPathLaw
  rw [Kernel.lintegral_traj
    (κ := homHistoryKernel Q)
    (fun _ : Finset.Iic 0 => x) (measurable_hittingValue hK)]
  have hzero : ∀ omega : ℕ → X,
      hittingValue K
        (Function.updateFinset omega (Finset.Iic 0)
          (fun _ : Finset.Iic 0 => x)) = 0 := by
    intro omega
    apply hittingValue_eq_zero_of_mem_target K
    rw [UEOT.V3.RecoveryHittingPoisson.update_initial_zero]
    exact hx
  simp_rw [hzero]
  exact lintegral_zero

/-- A finite one-step expectation of the canonical hitting-time potential is
finite at every state carrying positive one-step mass. -/
theorem expectedHittingTime_ne_top_of_positive_oneStep_mass
    {X : Type uX} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (Q : Kernel X X) [IsMarkovKernel Q]
    (x y : X) (K : Set X) (hK : MeasurableSet K)
    (hy : Q x {y} ≠ 0)
    (hint : (∫⁻ z, expectedHittingTime Q z K ∂Q x) ≠ ∞) :
    expectedHittingTime Q y K ≠ ∞ := by
  have hae : ∀ᵐ z ∂Q x, expectedHittingTime Q z K < ∞ :=
    ae_lt_top (measurable_expectedHittingTime Q hK) hint
  rw [ae_iff] at hae
  intro htop
  have hsub : ({y} : Set X) ⊆
      {z | ¬ expectedHittingTime Q z K < ∞} := by
    intro z hz
    have hzy : z = y := by simpa using hz
    subst z
    simp [htop]
  have hzero : Q x ({y} : Set X) = 0 := measure_mono_null hsub hae
  exact hy hzero

/-- The stochastic repair basin of a fixed deterministic stationary policy is
the set of states with finite canonical expected target-hitting time. -/
def StationaryRepairBasin
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi : X → A) : Set X :=
  {x | expectedHittingTime (stationaryKernel P pi) x K ≠ ∞}

theorem stationaryRepairBasin_eq_canonicalCertificate_basin
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi : X → A) :
    StationaryRepairBasin P K pi =
      (policyCanonicalRepairCertificate P K pi).basin := by
  ext x
  exact (policyCanonicalRepairCertificate_mem_basin_iff P K pi x).symm

/-- **AR1 target inclusion.** Every target state belongs to every fixed-policy
stochastic repair basin because its hitting time is zero. -/
theorem target_subset_stationaryRepairBasin
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi : X → A) :
    K ⊆ StationaryRepairBasin P K pi := by
  intro x hx
  change expectedHittingTime (stationaryKernel P pi) x K ≠ ∞
  rw [expectedHittingTime_eq_zero_of_mem_target
    (stationaryKernel P pi) x K hx]
  simp

/-- **AR1 support closure.** Outside the target, every positive-probability
one-step successor of a finite-hitting state is again finite-hitting under the
same stationary policy. -/
theorem stationaryRepairBasin_support_closed
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (pi : X → A)
    {x y : X}
    (hx : x ∈ StationaryRepairBasin P K pi)
    (hxK : x ∉ K)
    (hy : y ∈ (P x (pi x)).support) :
    y ∈ StationaryRepairBasin P K pi := by
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have hint :
      (∫⁻ z, expectedHittingTime (stationaryKernel P pi) z K
        ∂stationaryKernel P pi x) ≠ ∞ :=
    first_step_lintegral_ne_top
      (stationaryKernel P pi) x K hK hxK hx
  apply expectedHittingTime_ne_top_of_positive_oneStep_mass
    (stationaryKernel P pi) x y K hK
  · rw [stationaryKernel_apply]
    rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton y)]
    exact (PMF.mem_support_iff _ _).1 hy
  · exact hint

end

end UEOT.V3.Compression.Objecthood
