import UEOT.V3.Compression.Objecthood.FiniteStationaryHittingExpectation

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.DynamicsKernel
open UEOT.V3.RecoveryHittingNonnegative
open scoped ENNReal ProbabilityTheory

universe uX uA
noncomputable section

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

/-- **GCR6 closes the AR6 G3 boundary.** Arbitrary randomized complete-history
causal almost-sure repairability is witnessed by some deterministic stationary
policy with finite canonical expected target-hitting time. -/
theorem generalCausalToStationaryCompleteness
    (P : X → A → PMF X) (K : Set X) :
    GeneralCausalToStationaryCompleteness P K := by
  intro x hx
  rcases hx with ⟨pi, hHit⟩
  obtain ⟨g, hgHit⟩ :=
    exists_stationaryPolicy_ae_eventually_hits P K x pi hHit
  refine ⟨g, ?_⟩
  change expectedHittingTime (stationaryKernel P g) x K ≠ ∞
  exact stationary_expectedHittingTime_ne_top_of_ae_eventually_hits
    P g x K hgHit

/-- The reverse direction required by the frozen GCR6 contract uses the exact
GCR0 stationary path-law bridge, rather than treating deterministic stationary
policies as informally included in the general causal class. -/
theorem deterministicStationaryFiniteExpectedRepairable_to_generalCausal
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : DeterministicStationaryFiniteExpectedRepairable P K x) :
    GeneralCausalAlmostSureRepairable P K x := by
  rcases hx with ⟨g, hg⟩
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have hHit :
      ∀ᵐ omega ∂homTrajMeasure (Measure.dirac x) (stationaryKernel P g),
        ∃ n : ℕ, omega n ∈ K :=
    eventually_hits_ae_of_expectedHittingTime_ne_top
      (stationaryKernel P g) x K hK hg
  refine ⟨stationaryAdmissible g, ?_⟩
  rw [stationaryCausal_pathLaw_eq_stationaryTrajMeasure P g x]
  simpa [stationaryTrajMeasure, PMF.toMeasure_pure] using hHit

/-- Pointwise GCR6 equivalence between the AR6 broad arbitrary-causal class and
the AR0--AR5 deterministic-stationary finite-expectation class. -/
theorem generalCausalAlmostSureRepairable_iff_deterministicStationary
    (P : X → A → PMF X) (K : Set X) (x : X) :
    GeneralCausalAlmostSureRepairable P K x ↔
      DeterministicStationaryFiniteExpectedRepairable P K x := by
  constructor
  · exact generalCausalToStationaryCompleteness P K x
  · exact deterministicStationaryFiniteExpectedRepairable_to_generalCausal P K x

/-- **GCR6 set-level closure.** The full exact arbitrary-causal almost-sure
repairable set is exactly the deterministic-stationary finite-expected-hitting
repairable set. -/
theorem generalCausalRepairableSet_eq_deterministicStationaryRepairableSet
    (P : X → A → PMF X) (K : Set X) :
    {x : X | GeneralCausalAlmostSureRepairable P K x} =
      {x : X | DeterministicStationaryFiniteExpectedRepairable P K x} := by
  ext x
  exact generalCausalAlmostSureRepairable_iff_deterministicStationary P K x

end
end UEOT.V3.Compression.Objecthood
