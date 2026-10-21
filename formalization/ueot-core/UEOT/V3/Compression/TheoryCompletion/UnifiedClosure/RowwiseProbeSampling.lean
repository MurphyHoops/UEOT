import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples
import UEOT.V3.BoundedLossTwoSided

/-!
# Fixed-allocation rowwise scalar probe experiments

Each probe has its own actual data law and its own positive sample count,
fixed before sampling. The scalar Hoeffding bound is applied within each
row and then summed over probes. Cross-row independence is unnecessary.
This budget is for scalar means, not PMF total variation. The concrete
product experiment reuses the existing sigma-indexed sampling law; its
coordinates belong to separate experimental units.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RowwiseProbeSampling

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.BoundedLossSampling UEOT.V3.BoundedLossTwoSided
open VariableRegisteredSamples
open scoped BigOperators Classical

noncomputable section

universe uJ uX uΩ

/-- The common event is defined from the actual empirical and population means. -/
def coordinateGood
    {J : Type uJ} {X : Type uX} {Ω : Type uΩ}
    [MeasurableSpace X] {N : J → ℕ}
    (row : J → PMF X) (outcome : J → X → ℝ)
    (sample : ∀ j, Fin (N j) → Ω → X) (u : ℝ) : Set Ω :=
  {ω | ∀ j, |empiricalRisk (outcome j) (sample j) ω -
    trueRisk (row j).toMeasure (outcome j)| ≤ u}

/-- Allocation-sensitive scalar budget. There is no state-subset or candidate factor. -/
def scalarBudget {J : Type uJ} [Fintype J] (N : J → ℕ) (u : ℝ) : ℝ :=
  ∑ j, 2 * exp (-2 * (N j : ℝ) * u ^ 2)

theorem coordinateGood_measurable
    {J : Type uJ} {X : Type uX} {Ω : Type uΩ}
    [Fintype J] [MeasurableSpace X] [MeasurableSpace Ω] {N : J → ℕ}
    (row : J → PMF X) (outcome : J → X → ℝ)
    (sample : ∀ j, Fin (N j) → Ω → X) (u : ℝ)
    (hOutcome : ∀ j, Measurable (outcome j))
    (hSample : ∀ j k, Measurable (sample j k)) :
    MeasurableSet (coordinateGood row outcome sample u) := by
  have heq : coordinateGood row outcome sample u =
      ⋂ j, {ω | |empiricalRisk (outcome j) (sample j) ω -
        trueRisk (row j).toMeasure (outcome j)| ≤ u} := by
    ext ω
    simp [coordinateGood]
  rw [heq]
  apply MeasurableSet.iInter
  intro j
  have hemp : Measurable (fun ω => empiricalRisk (outcome j) (sample j) ω) := by
    unfold empiricalRisk
    exact (Finset.measurable_sum Finset.univ (fun k _ =>
      (hOutcome j).comp (hSample j k))).div_const _
  exact measurableSet_le (hemp.sub measurable_const).abs measurable_const

/-- One genuine common event controls all row means. Only the coordinates
within each row need to be independent under the same probability law. -/
theorem measure_coordinateGood_compl_le
    {J : Type uJ} {X : Type uX} {Ω : Type uΩ}
    [Fintype J] [MeasurableSpace X] [MeasurableSpace Ω]
    (N : J → ℕ) (hN : ∀ j, 0 < N j)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (row : J → PMF X) (outcome : J → X → ℝ)
    (sample : ∀ j, Fin (N j) → Ω → X)
    (hOutcome : ∀ j, Measurable (outcome j))
    (hOutcome01 : ∀ j x, outcome j x ∈ Set.Icc (0 : ℝ) 1)
    (hSample : ∀ j k, Measurable (sample j k))
    (hIndependent : ∀ j, iIndepFun (sample j) μ)
    (hLaw : ∀ j k, μ.map (sample j k) = (row j).toMeasure)
    (u : ℝ) (hu : 0 ≤ u) :
    μ.real (coordinateGood row outcome sample u)ᶜ ≤ min 1 (scalarBudget N u) := by
  apply le_min measureReal_le_one
  have heq : (coordinateGood row outcome sample u)ᶜ =
      ⋃ j, {ω | u < |empiricalRisk (outcome j) (sample j) ω -
        trueRisk (row j).toMeasure (outcome j)|} := by
    ext ω
    simp [coordinateGood, not_forall, not_le]
  rw [heq]
  exact (measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum fun j _ =>
      measure_empiricalRisk_bad_le (hN j) μ (row j).toMeasure
        (outcome j) (hOutcome j) (hOutcome01 j) (sample j)
        (hSample j) (hIndependent j) (hLaw j) hu)

/-- The sigma-indexed product law discharges every sampling premise.
Unlike the general theorem, this concrete experiment also has independent rows. -/
theorem product_probe_calibration
    {J : Type uJ} {X : Type uX} [Fintype J] [MeasurableSpace X]
    (row : J → PMF X) (N : J → ℕ) (hN : ∀ j, 0 < N j)
    (outcome : J → X → ℝ)
    (hOutcome : ∀ j, Measurable (outcome j))
    (hOutcome01 : ∀ j x, outcome j x ∈ Set.Icc (0 : ℝ) 1)
    (u : ℝ) (hu : 0 ≤ u) :
    MeasurableSet (coordinateGood row outcome (productRowSample (N := N)) u) ∧
      (productRowLaw row N).real
        (coordinateGood row outcome (productRowSample (N := N)) u)ᶜ ≤
          min 1 (scalarBudget N u) := by
  exact ⟨coordinateGood_measurable row outcome productRowSample u
      hOutcome productRowSample_measurable,
    measure_coordinateGood_compl_le N hN (productRowLaw row N) row outcome
      productRowSample hOutcome hOutcome01 productRowSample_measurable
      (productRowSample_independent row N) (productRowSample_law row N) u hu⟩

/-- Empty probe registration is valid for pure mean calibration. It does not
supply the nonempty observation field required by the N3 protocol. -/
theorem empty_probe_boundary
    {J : Type uJ} {X : Type uX} {Ω : Type uΩ}
    [Fintype J] [IsEmpty J] [MeasurableSpace X] {N : J → ℕ}
    (row : J → PMF X) (outcome : J → X → ℝ)
    (sample : ∀ j, Fin (N j) → Ω → X) (u : ℝ) :
    coordinateGood row outcome sample u = Set.univ ∧ scalarBudget N u = 0 := by
  simp [coordinateGood, scalarBudget]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RowwiseProbeSampling
