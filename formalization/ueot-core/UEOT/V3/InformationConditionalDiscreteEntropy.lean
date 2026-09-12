import UEOT.V3.InformationDiscreteEntropy
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# P-INFO-03 — countable conditional entropy foundation

This module defines `H(C|U)` for a countable discrete random element `C` by
true disintegration over `U`.  It does not define conditional entropy by the
difference `H(C)-I(C;U)`, which would introduce an unintended finiteness
assumption on the unconditional entropy.

For a probability law `ρ` on `U × C`, the conditional law `P(C|U=u)` is the
standard-Borel conditional kernel.  The entropy of each fiber is the extended
Shannon sum

`∑' c, ofReal (negMulLog (P(C=c|U=u)))`,

and `H(C|U)` is its `P_U`-average as an `ENNReal` lintegral.  This representation
allows the source hypothesis `H(C|U) < ∞` to be stated directly without any
`∞ - ∞` subtraction.
-/

namespace UEOT.V3.InformationConditionalDiscreteEntropy

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe uU uC

variable {U : Type uU} {C : Type uC}
variable [MeasurableSpace U] [MeasurableSpace C]
variable [StandardBorelSpace U] [StandardBorelSpace C]
variable [Countable C] [MeasurableSingletonClass C] [Nonempty C]

/-- The true conditional law `P(C|U)` of a countable discrete random element. -/
noncomputable def conditionalDiscreteKernel
    (ρ : Measure (U × C)) [IsProbabilityMeasure ρ] : Kernel U C :=
  ρ.condKernel

instance conditionalDiscreteKernel_isMarkov
    (ρ : Measure (U × C)) [IsProbabilityMeasure ρ] :
    IsMarkovKernel (conditionalDiscreteKernel ρ) := by
  unfold conditionalDiscreteKernel
  infer_instance

/-- The Shannon contribution of one countable state inside a fixed `U` fiber. -/
noncomputable def conditionalDiscreteEntropyTerm
    (ρ : Measure (U × C)) [IsProbabilityMeasure ρ]
    (c : C) (u : U) : ENNReal :=
  ENNReal.ofReal
    (Real.negMulLog (((conditionalDiscreteKernel ρ) u {c}).toReal))

lemma measurable_conditionalDiscreteEntropyTerm
    (ρ : Measure (U × C)) [IsProbabilityMeasure ρ]
    (c : C) :
    Measurable (conditionalDiscreteEntropyTerm ρ c) := by
  unfold conditionalDiscreteEntropyTerm
  have hp : Measurable (fun u => ((conditionalDiscreteKernel ρ) u {c}).toReal) :=
    ((conditionalDiscreteKernel ρ).measurable_coe (measurableSet_singleton c)).ennreal_toReal
  exact (Real.continuous_negMulLog.measurable.comp hp).ennreal_ofReal

/-- Extended Shannon entropy of the conditional law `P(C|U=u)`. -/
noncomputable def conditionalDiscreteEntropyFiber
    (ρ : Measure (U × C)) [IsProbabilityMeasure ρ]
    (u : U) : ENNReal :=
  ∑' c : C, conditionalDiscreteEntropyTerm ρ c u

lemma measurable_conditionalDiscreteEntropyFiber
    (ρ : Measure (U × C)) [IsProbabilityMeasure ρ] :
    Measurable (conditionalDiscreteEntropyFiber ρ) := by
  unfold conditionalDiscreteEntropyFiber
  exact Measurable.tsum fun c => measurable_conditionalDiscreteEntropyTerm ρ c

lemma conditionalDiscreteEntropyFiber_nonneg
    (ρ : Measure (U × C)) [IsProbabilityMeasure ρ]
    (u : U) :
    0 ≤ conditionalDiscreteEntropyFiber ρ u := by
  exact bot_le

/-- **Genuine countable conditional entropy `H(C|U)`.**

The value is extended-real and may be infinite.  The frozen P-INFO-03 source
assumption `H(C|U)<∞` is represented by `conditionalDiscreteEntropy ρ ≠ ⊤`. -/
noncomputable def conditionalDiscreteEntropy
    (ρ : Measure (U × C)) [IsProbabilityMeasure ρ] : ENNReal :=
  ∫⁻ u, conditionalDiscreteEntropyFiber ρ u ∂ρ.fst

lemma conditionalDiscreteEntropy_ne_top_iff_lt_top
    (ρ : Measure (U × C)) [IsProbabilityMeasure ρ] :
    conditionalDiscreteEntropy ρ ≠ ⊤ ↔ conditionalDiscreteEntropy ρ < ⊤ := by
  exact lt_top_iff_ne_top.symm

end

end UEOT.V3.InformationConditionalDiscreteEntropy
