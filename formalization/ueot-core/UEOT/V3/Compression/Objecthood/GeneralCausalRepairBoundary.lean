import UEOT.V3.Compression.Objecthood.RepairRankHittingRelation
import UEOT.V3.ReflexiveStatePathLaw

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.ReflexiveStateAugmentation
open UEOT.V3.ReflexiveStatePathLaw
open scoped ProbabilityTheory

universe uX uA

noncomputable section

/-- The controlled PMF model presented in the kernel form used by the exact
complete-history causal path-law infrastructure. -/
noncomputable def pmfControlledKernel
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) : Kernel (X × A) X :=
  Kernel.ofFunOfCountable fun za => (P za.1 za.2).toMeasure

instance pmfControlledKernel_isMarkov
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) : IsMarkovKernel (pmfControlledKernel P) := by
  unfold pmfControlledKernel
  constructor
  intro za
  change IsProbabilityMeasure (P za.1 za.2).toMeasure
  infer_instance

/-- An arbitrary causal randomized action policy together with the exact
Markov-kernel obligation needed by the Ionescu--Tulcea construction. -/
structure AdmissibleCausalRepairPolicy
    (X : Type uX) (A : Type uA)
    [MeasurableSpace X] [MeasurableSpace A] where
  policy : CausalPolicy X A
  markov : ∀ n, IsMarkovKernel (policy n)

/-- Exact physical-state path law for an admissible arbitrary causal randomized
policy in the PMF-controlled model. -/
noncomputable def causalRepairPathLaw
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A) : Measure (ℕ → X) := by
  letI : ∀ n, IsMarkovKernel (pi.policy n) := pi.markov
  exact reflexivePathLaw (Measure.dirac x) (pmfControlledKernel P) pi.policy

/-- Broad AR6 comparison class: arbitrary complete-history causal randomized
policies that hit the target almost surely under their exact path law. -/
def GeneralCausalAlmostSureRepairable
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X) (x : X) : Prop :=
  ∃ pi : AdmissibleCausalRepairPolicy X A,
    ∀ᵐ omega ∂causalRepairPathLaw P x pi, ∃ n : ℕ, omega n ∈ K

/-- The exact deterministic-stationary finite-expected-hitting class established
by AR0--AR5. -/
def DeterministicStationaryFiniteExpectedRepairable
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X) : Prop :=
  ∃ pi : X → A, x ∈ StationaryRepairBasin P K pi

/-- AR3 is complete for the deterministic-stationary finite-expectation class. -/
theorem deterministicStationaryRepairable_iff_mem_maximalBasin
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) (x : X) :
    DeterministicStationaryFiniteExpectedRepairable P K x ↔
      x ∈ StationaryRepairBasin P K (maximalStationaryRepairPolicy P K) := by
  rw [maximalStationaryRepairBasin_eq_exists_policy P K]
  rfl

/-- **G3 boundary statement.** This is the exact theorem still required to
identify general causal almost-sure reachability with the established maximal
stationary finite-expectation basin. AR6 names the proposition but deliberately
does not assume or assert it. -/
def GeneralCausalToStationaryCompleteness
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X) : Prop :=
  ∀ x : X,
    GeneralCausalAlmostSureRepairable P K x →
      DeterministicStationaryFiniteExpectedRepairable P K x

end

end UEOT.V3.Compression.Objecthood
