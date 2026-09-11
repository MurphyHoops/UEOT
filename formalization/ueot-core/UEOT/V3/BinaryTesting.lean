import UEOT.V3.TotalVariation
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Linarith

/-!
# P-INV-01 — binary testing lower bound

The frozen source considers two models with equal prior probability.  If `A`
is the measurable decision region on which the test selects model 1, then the
average error is

`(1/2) * (P₀(A) + P₁(Aᶜ))`.

This first layer proves the universal lower bound in terms of source total
variation.  A separate Radon–Nikodym/Hahn layer will construct an optimal
measurable region and attain the bound on a general measurable space.
-/

namespace UEOT.V3.BinaryTesting

open MeasureTheory
open UEOT.V3.TotalVariation

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- Equal-prior average error of the binary test that chooses model 1 on `A`
and model 0 on its complement. -/
noncomputable def binaryRisk (P₀ P₁ : Measure X) (A : Set X) : ℝ :=
  (1 / 2 : ℝ) * (P₀.real A + P₁.real Aᶜ)

/-- The source algebraic form of the equal-prior error. -/
theorem binaryRisk_eq_half_one_sub_diff
    (P₀ P₁ : Measure X)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (A : Set X) (hA : MeasurableSet A) :
    binaryRisk P₀ P₁ A =
      (1 / 2 : ℝ) * (1 - (P₁.real A - P₀.real A)) := by
  have hcompl := probReal_add_probReal_compl (μ := P₁) hA
  unfold binaryRisk
  linarith

/-- Every measurable binary test has error at least
`(1/2) * (1 - D_TV(P₀,P₁))`.  This is the lower-bound half of P-INV-01. -/
theorem binaryRisk_lower_bound
    (P₀ P₁ : Measure X)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (A : Set X) (hA : MeasurableSet A) :
    (1 / 2 : ℝ) * (1 - tvDist P₀ P₁) ≤ binaryRisk P₀ P₁ A := by
  have htv := tvEvent_le P₀ P₁ A hA
  rw [abs_sub_comm] at htv
  have hdiff : P₁.real A - P₀.real A ≤ tvDist P₀ P₁ :=
    (le_abs_self (P₁.real A - P₀.real A)).trans htv
  rw [binaryRisk_eq_half_one_sub_diff P₀ P₁ A hA]
  linarith

end UEOT.V3.BinaryTesting
