import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverage
import UEOT.V3.HilbertMeanProductBlockIndependence

/-!
# Registered row sampling with fixed per-row allocations

Each registered row receives its own strictly positive sample count `N j`,
fixed before observing data. The actual product experiment proves all
coordinate laws and within-row independence. General calibration allows
cross-row dependence and reuses the existing single-row concentration bound.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples

open MeasureTheory ProbabilityTheory
open UEOT.V3.TotalVariation
open UEOT.V3.HilbertMeanProductBlockIndependence
open scoped BigOperators Classical

noncomputable section

universe uJ uX uΩ

/-- The complete registration and its sample allocation are fixed before data. -/
abbrev SampleCoordinate {J : Type uJ} (N : J → ℕ) := Σ j, Fin (N j)

/-- A real product experiment has exactly the allocated coordinates. -/
def productRowLaw
    {J : Type uJ} {X : Type uX} [Fintype J] [MeasurableSpace X]
    (row : J → PMF X) (N : J → ℕ) :
    Measure (SampleCoordinate N → X) :=
  Measure.pi (fun jk : SampleCoordinate N => (row jk.1).toMeasure)

instance productRowLaw_isProbability
    {J : Type uJ} {X : Type uX} [Fintype J] [MeasurableSpace X]
    (row : J → PMF X) (N : J → ℕ) :
    IsProbabilityMeasure (productRowLaw row N) := by
  unfold productRowLaw
  infer_instance

def productRowSample
    {J : Type uJ} {X : Type uX} {N : J → ℕ}
    (j : J) (k : Fin (N j)) (ω : SampleCoordinate N → X) : X :=
  ω ⟨j, k⟩

theorem productRowSample_measurable
    {J : Type uJ} {X : Type uX} [MeasurableSpace X] {N : J → ℕ}
    (j : J) (k : Fin (N j)) :
    Measurable (productRowSample (X := X) j k) :=
  measurable_pi_apply (⟨j, k⟩ : SampleCoordinate N)

theorem productRowSample_law
    {J : Type uJ} {X : Type uX} [Fintype J] [MeasurableSpace X]
    (row : J → PMF X) (N : J → ℕ) (j : J) (k : Fin (N j)) :
    (productRowLaw row N).map (productRowSample j k) = (row j).toMeasure := by
  exact (measurePreserving_eval
    (fun jk : SampleCoordinate N => (row jk.1).toMeasure) ⟨j, k⟩).map_eq

theorem productRowSample_independent
    {J : Type uJ} {X : Type uX} [Fintype J] [MeasurableSpace X]
    (row : J → PMF X) (N : J → ℕ) (j : J) :
    iIndepFun (productRowSample (X := X) (N := N) j) (productRowLaw row N) := by
  have hall := coordinate_iIndep
    (fun jk : SampleCoordinate N => (row jk.1).toMeasure)
  exact iIndepFun.precomp
    (g := fun k : Fin (N j) => (⟨j, k⟩ : SampleCoordinate N))
    (by intro k l h; simpa using h) hall

/-- Allocation-sensitive confidence budget; no minimum-count replacement. -/
def confidenceBudget
    {J : Type uJ} (X : Type uX) [Fintype X] [Fintype J]
    (N : J → ℕ) (rho : J → ℝ) : ℝ :=
  ∑ j, (Fintype.card (Finset X) : ℝ) *
    (2 * Real.exp (-2 * (N j : ℝ) * (rho j) ^ 2))

/-- Existing single-row calibration is reused for each registration.
The intersection uses only a union bound, so rows may share dependent data.
All sample counts and radii are deterministic inputs, independent of ω. -/
theorem registered_row_calibration
    {Ω : Type uΩ} {X : Type uX} {J : Type uJ}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    [Fintype X] [Fintype J]
    (N : J → ℕ) (hN : ∀ j, 0 < N j)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (row : J → PMF X) (sample : ∀ j, Fin (N j) → Ω → X) (rho : J → ℝ)
    (hmeas : ∀ j k, Measurable (sample j k))
    (hindep : ∀ j, iIndepFun (sample j) μ)
    (hlaw : ∀ j k, μ.map (sample j k) = (row j).toMeasure)
    (hrho : ∀ j, 0 ≤ rho j) :
    ∃ good : Set Ω, MeasurableSet good ∧
      μ.real goodᶜ ≤ confidenceBudget X N rho ∧
      ∀ ω ∈ good, ∀ j,
        tvDist (row j).toMeasure
          (empiricalResponsePMF (hN j) (sample j) ω).toMeasure ≤ rho j := by
  have hrow : ∀ j, ∃ good : Set Ω, MeasurableSet good ∧
      μ.real goodᶜ ≤ (Fintype.card (Finset X) : ℝ) *
        (2 * Real.exp (-2 * (N j : ℝ) * (rho j) ^ 2)) ∧
      ∀ ω ∈ good,
        tvDist (row j).toMeasure
          (empiricalResponsePMF (hN j) (sample j) ω).toMeasure ≤ rho j := by
    intro j
    obtain ⟨good, hg, hb, hc⟩ := coverage_registered_row_calibration (hN j) μ
      (fun _ : Unit => row j) (fun _ : Unit => sample j) (fun _ : Unit => rho j)
      (fun _ => hmeas j) (fun _ => hindep j) (fun _ => hlaw j) (fun _ => hrho j)
    exact ⟨good, hg, by simpa using hb, fun ω hω => hc ω hω ()⟩
  choose good hgood hbad hcal using hrow
  refine ⟨⋂ j, good j, MeasurableSet.iInter hgood, ?_, ?_⟩
  · have hcompl : (⋂ j, good j)ᶜ = ⋃ j, (good j)ᶜ := by
      ext ω
      simp
    rw [hcompl]
    exact (measureReal_iUnion_fintype_le _).trans
      (Finset.sum_le_sum fun j _ => hbad j)
  · intro ω hω j
    exact hcal j ω (Set.mem_iInter.mp hω j)

/-- Real coordinate laws discharge every sampling premise of calibration. -/
theorem product_experiment_calibration
    {J : Type uJ} {X : Type uX}
    [Fintype J] [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (row : J → PMF X) (N : J → ℕ) (hN : ∀ j, 0 < N j)
    (rho : J → ℝ) (hrho : ∀ j, 0 ≤ rho j) :
    ∃ good : Set (SampleCoordinate N → X), MeasurableSet good ∧
      (productRowLaw row N).real goodᶜ ≤ confidenceBudget X N rho ∧
      ∀ ω ∈ good, ∀ j,
        tvDist (row j).toMeasure
          (empiricalResponsePMF (hN j) (productRowSample j) ω).toMeasure ≤ rho j := by
  exact registered_row_calibration N hN (productRowLaw row N) row productRowSample rho
    productRowSample_measurable (productRowSample_independent row N)
    (productRowSample_law row N) hrho

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples
