import UEOT.V3.Compression.Objecthood.GeneralCausalStationaryCompleteness
import UEOT.V3.Compression.Objecthood.StochasticRepairSynthesis

/-!
# Track O / GCR7 — general-causal Objecthood repair synthesis

GCR6 closes the former AR6 general-causal boundary.  This stage feeds that
proved equivalence back into the existing AR7 maximal repair architecture
without changing the repair certificate, deletion primitive, or counted core.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.OmegaMinimalFailure
open UEOT.V3.Compression.CrossTrack
open scoped ENNReal ProbabilityTheory

universe uV uX uA

noncomputable section

/-- **GCR7 basin identification.**  The single AR3 maximal stationary repair
certificate has exactly the full general-causal almost-sure repairable basin
now proved by GCR6. -/
theorem maximalStationaryRepairCertificate_basin_eq_generalCausalRepairableSet
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X) :
    (maximalStationaryRepairCertificate P K).basin =
      {x | GeneralCausalAlmostSureRepairable P K x} := by
  calc
    (maximalStationaryRepairCertificate P K).basin =
        {x | DeterministicStationaryFiniteExpectedRepairable P K x} :=
      maximalStationaryRepairCertificate_basin_eq P K
    _ = {x | GeneralCausalAlmostSureRepairable P K x} :=
      (generalCausalRepairableSet_eq_deterministicStationaryRepairableSet P K).symm

theorem mem_maximalStationaryRepairCertificate_basin_iff_generalCausal
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X) (x : X) :
    x ∈ (maximalStationaryRepairCertificate P K).basin ↔
      GeneralCausalAlmostSureRepairable P K x := by
  rw [maximalStationaryRepairCertificate_basin_eq_generalCausalRepairableSet P K]
  rfl

/-- **GCR7 broad repair synthesis.**  AR7's maximal stationary architecture now
has the exact general-causal semantics proved by GCR6, while retaining the
target inclusion, support closure, strong-repair inclusion, and rank bound. -/
theorem stochasticObjecthood_generalCausalRepair_synthesis
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X) :
    let piMax := maximalStationaryRepairPolicy P K
    let BMax := StationaryRepairBasin P K piMax
    K ⊆ BMax ∧
      (∀ ⦃x y : X⦄, x ∈ BMax → x ∉ K →
        y ∈ (P x (piMax x)).support → y ∈ BMax) ∧
      BMax = {x | GeneralCausalAlmostSureRepairable P K x} ∧
      {x | StrongRepairable P K x} ⊆ BMax ∧
      (∀ (x : X) (hx : StrongRepairable P K x),
        stationaryRepairValue P K x ≤ (repairRank P K x hx : ℝ≥0∞)) := by
  dsimp only
  rcases stochasticObjecthood_stationaryRepair_synthesis P K with
    ⟨hK, hclosed, hB, hstrong, hrank⟩
  refine ⟨hK, hclosed, ?_, hstrong, hrank⟩
  calc
    StationaryRepairBasin P K (maximalStationaryRepairPolicy P K) =
        {x | DeterministicStationaryFiniteExpectedRepairable P K x} := by
      simpa [DeterministicStationaryFiniteExpectedRepairable] using hB
    _ = {x | GeneralCausalAlmostSureRepairable P K x} :=
      (generalCausalRepairableSet_eq_deterministicStationaryRepairableSet P K).symm

/-- A general-causal repairable damaged state is accepted directly by the
existing AR7 deletion/autonomous-repair theorem after the proved GCR6
equivalence; no new repair dynamics are introduced. -/
theorem generalCausalRepairable_failure_restores_legitimate
    {X : Type uX} {A : Type uA} {V : Type uV}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (Failure : Finset V → Prop)
    (hmono : FailureMonotone Failure)
    (damage : Finset V → ConstitutiveState X A)
    (D : Finset V)
    (hfail : Failure D)
    (hrepair : GeneralCausalAlmostSureRepairable P K (damage D).1) :
    ∃ C, C ∈ minimalFailures Failure ∧ C ⊆ D ∧
      (∀ᵐ omega ∂stationaryTrajMeasure
          (autonomousRepairLift P K hfix
            (maximalStationaryRepairCertificate P K))
          noExternalControl (PMF.pure (damage D)),
        ∃ n : ℕ, omega n ∈ legitimateConstitutiveDomain P K) := by
  have hstationary :
      DeterministicStationaryFiniteExpectedRepairable P K (damage D).1 :=
    (generalCausalAlmostSureRepairable_iff_deterministicStationary
      P K (damage D).1).1 hrepair
  exact stationaryRepairable_failure_restores_legitimate
    P K hfix Failure hmono damage D hfail hstationary

/-- **GCR7 ER0 resynthesis.**  General-causal repairability is sufficient for
eventual permanent legitimacy under the unchanged maximal AR repair
certificate. -/
theorem generalCausalRepairable_eventually_always_legitimate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    {z : ConstitutiveState X A}
    (hz : GeneralCausalAlmostSureRepairable P K z.1) :
    ∀ᵐ omega ∂stationaryTrajMeasure
        (autonomousRepairLift P K hfix (maximalStationaryRepairCertificate P K))
        noExternalControl (PMF.pure z),
      ∃ N : ℕ, ∀ m ≥ N, omega m ∈ legitimateConstitutiveDomain P K := by
  have hstationary :
      DeterministicStationaryFiniteExpectedRepairable P K z.1 :=
    (generalCausalAlmostSureRepairable_iff_deterministicStationary P K z.1).1 hz
  exact stationaryRepairable_eventually_always_legitimate
    P K hfix hstationary

end
end UEOT.V3.Compression.Objecthood
