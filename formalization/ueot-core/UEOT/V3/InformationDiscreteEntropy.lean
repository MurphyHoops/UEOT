import UEOT.V3.InformationEntropyBound
import UEOT.V3.InformationEntropy
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# P-INFO-01 finite discrete copy-KL / Shannon bridge

This module isolates the only genuinely discrete step left in the entropy
bound.  For a finite measurable state space, the diagonal/copy law is written
as a density with respect to the independent product law.  The density is
`1 / μ {m}` on the diagonal and zero off it.  The KL-to-Shannon calculation is
built on top of this identity rather than postulated.
-/

namespace UEOT.V3.InformationDiscreteEntropy

open MeasureTheory InformationTheory
open UEOT.V3.InformationEntropyBound
open scoped ENNReal

universe uM

variable {M : Type uM}
variable [Fintype M] [MeasurableSpace M] [MeasurableSingletonClass M]

/-- Radon--Nikodym density of the diagonal copy law relative to two independent
copies, on a finite discrete state space. -/
noncomputable def copyDensity (μ : Measure M) : M × M → ℝ≥0∞ :=
  fun z => if z.1 = z.2 then (μ {z.1})⁻¹ else 0

lemma measurable_copyDensity (μ : Measure M) : Measurable (copyDensity μ) := by
  exact measurable_of_finite _

/-- The diagonal law is exactly the independent product law tilted by the
copy density.  This is the measure-level core of the discrete entropy bridge. -/
theorem prod_withDensity_copyDensity_eq_copyJoint
    (μ : Measure M) [IsProbabilityMeasure μ] :
    (μ.prod μ).withDensity (copyDensity μ) = copyJoint μ := by
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [Measure.withDensity_apply _ (measurableSet_singleton (a, b))]
  rw [lintegral_singleton]
  have hprod : (μ.prod μ) ({(a, b)} : Set (M × M)) = μ {a} * μ {b} := by
    rw [show ({(a, b)} : Set (M × M)) = ({a} : Set M) ×ˢ ({b} : Set M) by ext z; simp]
    exact Measure.prod_prod _ _
  rw [hprod]
  unfold copyJoint
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton (a, b))]
  by_cases hab : a = b
  · subst b
    simp only [copyDensity, if_pos rfl]
    rw [show ((fun m : M => (m, m)) ⁻¹' ({(a, a)} : Set (M × M))) = ({a} : Set M) by
      ext m
      simp]
    by_cases ha : μ {a} = 0
    · simp [ha]
    · rw [ENNReal.inv_mul_cancel ha (measure_ne_top μ {a})]
      simp
  · simp only [copyDensity, if_neg hab]
    rw [show ((fun m : M => (m, m)) ⁻¹' ({(a, b)} : Set (M × M))) = (∅ : Set M) by
      ext m
      simp [hab]]
    simp

/-- Absolute continuity needed by the KL/Radon--Nikodym API follows from the
explicit density representation. -/
theorem copyJoint_absolutelyContinuous_prod
    (μ : Measure M) [IsProbabilityMeasure μ] :
    copyJoint μ ≪ μ.prod μ := by
  rw [← prod_withDensity_copyDensity_eq_copyJoint μ]
  exact Measure.withDensity_absolutelyContinuous _ _

/-- The abstract Mathlib Radon--Nikodym derivative agrees almost everywhere
with the explicit finite-discrete copy density. -/
theorem rnDeriv_copyJoint_prod
    (μ : Measure M) [IsProbabilityMeasure μ] :
    (copyJoint μ).rnDeriv (μ.prod μ) =ᵐ[μ.prod μ] copyDensity μ := by
  rw [← prod_withDensity_copyDensity_eq_copyJoint μ]
  exact Measure.rnDeriv_withDensity (μ.prod μ) (measurable_copyDensity μ)

end UEOT.V3.InformationDiscreteEntropy
