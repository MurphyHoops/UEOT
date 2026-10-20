/-!
Companion tail for the research prototype, NOT a production module.

Append this text after VariableRegisteredSamples.lean in a temporary combined
file, then use the same `lake env lean` environment. There is intentionally no
import here, so the companion does not depend on a separately installed
prototype .olean. It checks two concrete interface boundaries without
enumerating samples or asserting a new scientific witness.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamplesBoundaryCheck

open MeasureTheory ProbabilityTheory UEOT.V3.TotalVariation
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples
open scoped Classical

noncomputable section

universe uΩ

local instance : MeasurableSpace Bool := ⊤

private def twoRowCount (j : Bool) : ℕ := if j then 2 else 1

private theorem twoRowCount_pos (j : Bool) : 0 < twoRowCount j := by
  cases j <;> decide

-- These coordinates must have DIFFERENT Fin domains. In particular the
-- last true-row coordinate has explicit type Fin 2 and cannot be a Fin 1.
#check productRowSample (X := Bool) (N := twoRowCount) false (0 : Fin 1)
#check productRowSample (X := Bool) (N := twoRowCount) true (1 : Fin 2)

-- Check the whole constructed-experiment endpoint with one and two actual
-- coordinates. The rows and radii remain arbitrary: this tests the dependent
-- allocation interface, not a hand-picked numerical probability result.
example (row : Bool → PMF Bool) (rho : Bool → ℝ)
    (hrho : ∀ j, 0 ≤ rho j) :
    ∃ good : Set (SampleCoordinate twoRowCount → Bool), MeasurableSet good ∧
      (productRowLaw row twoRowCount).real goodᶜ ≤ confidenceBudget Bool twoRowCount rho ∧
      ∀ ω ∈ good, ∀ j,
        tvDist (row j).toMeasure
          (empiricalResponsePMF (twoRowCount_pos j)
            (productRowSample (X := Bool) (N := twoRowCount) j) ω).toMeasure ≤ rho j := by
  exact product_experiment_calibration row twoRowCount twoRowCount_pos rho hrho

-- Empty registration has no positive-count obligation. Giving the EMPTY
-- family the constant zero count must be admissible, although a nonempty row
-- with N = 0 is not admitted by the calibration theorem.
example {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ good : Set Ω, MeasurableSet good ∧ μ.real goodᶜ ≤ 0 := by
  let N : Empty → ℕ := fun _ => 0
  let hN : ∀ j : Empty, 0 < N j := by
    intro j
    cases j
  let row : Empty → PMF Bool := fun j => nomatch j
  let sample : ∀ j : Empty, Fin (N j) → Ω → Bool := fun j => nomatch j
  let rho : Empty → ℝ := fun _ => 0
  obtain ⟨good, hgood, hbad, _hcal⟩ := registered_row_calibration N hN μ row sample rho
    (by intro j; cases j)
    (by intro j; cases j)
    (by intro j; cases j)
    (by intro j; cases j)
  exact ⟨good, hgood, by simpa [confidenceBudget] using hbad⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamplesBoundaryCheck
