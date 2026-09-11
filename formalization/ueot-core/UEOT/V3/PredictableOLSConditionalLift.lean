import UEOT.V3.PredictableOLSMultiplier
import Mathlib.Tactic

/-!
# P-INV-05 — conditional to unconditional sub-Gaussian lift

For the first predictable score increment, the source theorem gives a
conditional sub-Gaussian hypothesis with respect to the initial past
sigma-algebra.  Mathlib's finite-sum martingale theorem asks for an
unconditional sub-Gaussian hypothesis at index zero.  Under a probability
measure the latter follows from the former by the tower property.

We obtain this cleanly from Mathlib's
`HasSubgaussianMGF.add_of_hasCondSubgaussianMGF`, adding the zero random
variable on the trimmed measure.
-/

namespace UEOT.V3.PredictableOLSConditionalLift

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe uΩ

variable {Ω : Type uΩ} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Conditional sub-Gaussianity implies unconditional sub-Gaussianity under a
probability measure.  No triviality assumption on the conditioning
sigma-algebra is needed. -/
theorem HasCondSubgaussianMGF.toHasSubgaussianMGF
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasCondSubgaussianMGF m hm X c μ) :
    HasSubgaussianMGF X c μ := by
  have hzero : HasSubgaussianMGF (fun _ : Ω => (0 : ℝ)) 0 (μ.trim hm) := by
    simp
  have hsum := HasSubgaussianMGF.add_of_hasCondSubgaussianMGF hm hzero hX
  simpa using hsum

end UEOT.V3.PredictableOLSConditionalLift
