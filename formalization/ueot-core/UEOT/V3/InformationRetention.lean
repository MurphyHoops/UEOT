import UEOT.V3.InformationStatistic

/-!
# P-INFO-01 retention corollaries

This layer records direct consequences of the exact deterministic-statistic
chain identity.  It deliberately reuses the conditional-KL residual defined in
`InformationStatistic` rather than introducing a subtraction-based surrogate.
-/

namespace UEOT.V3.InformationRetention

open MeasureTheory InformationTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open UEOT.V3.InformationCore
open UEOT.V3.InformationStatistic

universe uH uM uY

variable {H : Type uH} {M : Type uM} {Y : Type uY}
variable [MeasurableSpace H] [MeasurableSpace M] [MeasurableSpace Y]

/-- Vanishing conditional-information residual is sufficient for exact
information retention by a deterministic statistic. -/
theorem mutualInfo_statistic_eq_of_conditional_eq_zero
    [StandardBorelSpace H] [Nonempty H]
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (f : H → M) (hf : Measurable f)
    (hzero : conditionalMutualInfoStatistic μ f = 0) :
    mutualInfo (statisticJoint μ f hf) = mutualInfo μ := by
  rw [mutualInfo_eq_statistic_add_conditional μ f hf, hzero, add_zero]

/-- Quantitative retention written as a two-sided sandwich: deterministic data
processing supplies the upper side, while a conditional residual at most ε
supplies the lower side in addition form. -/
theorem mutualInfo_statistic_retention_sandwich
    [StandardBorelSpace H] [Nonempty H]
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (f : H → M) (hf : Measurable f)
    {ε : ENNReal}
    (hε : conditionalMutualInfoStatistic μ f ≤ ε) :
    mutualInfo (statisticJoint μ f hf) ≤ mutualInfo μ ∧
      mutualInfo μ ≤ mutualInfo (statisticJoint μ f hf) + ε := by
  exact ⟨mutualInfo_statistic_le μ f hf,
    mutualInfo_statistic_ge_sub_of_conditional_le μ f hf hε⟩

end UEOT.V3.InformationRetention
