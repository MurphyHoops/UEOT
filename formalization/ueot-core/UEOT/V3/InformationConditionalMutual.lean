import UEOT.V3.InformationCore
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# General conditional mutual information by true disintegration

This module generalizes the KL/reference construction already validated in the
P-INFO-04 binary stack.  For a probability law `ρ` on `U × (X × Y)`:

* `conditionalJointKernel ρ = P(X,Y|U)`;
* `conditionalIndependenceKernel ρ = P(X|U) × P(Y|U)` fiberwise;
* `conditionalMutualInfo ρ` is the KL divergence from the true joint law to
  `P_U ⊗ P(X|U) ⊗ P(Y|U)`.

The definition is extended-real valued and contains no entropy subtraction, so
it remains meaningful without finiteness assumptions.  It is the canonical
interface intended for P-INFO-03 and, after that proof stabilizes, P-INT-01.
-/

namespace UEOT.V3.InformationConditionalMutual

noncomputable section

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe uU uX uY

variable {U : Type uU} {X : Type uX} {Y : Type uY}
variable [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]
variable [StandardBorelSpace U] [StandardBorelSpace X] [StandardBorelSpace Y]
variable [Nonempty X] [Nonempty Y]

/-- The true conditional law `P(X,Y|U)`. -/
noncomputable def conditionalJointKernel
    (ρ : Measure (U × (X × Y))) [IsProbabilityMeasure ρ] :
    Kernel U (X × Y) :=
  ρ.condKernel

instance conditionalJointKernel_isMarkov
    (ρ : Measure (U × (X × Y))) [IsProbabilityMeasure ρ] :
    IsMarkovKernel (conditionalJointKernel ρ) := by
  unfold conditionalJointKernel
  infer_instance

/-- The fiberwise conditional-independence reference
`P(X|U) × P(Y|U)`. -/
noncomputable def conditionalIndependenceKernel
    (ρ : Measure (U × (X × Y))) [IsProbabilityMeasure ρ] :
    Kernel U (X × Y) :=
  (conditionalJointKernel ρ).fst ×ₖ (conditionalJointKernel ρ).snd

instance conditionalIndependenceKernel_isMarkov
    (ρ : Measure (U × (X × Y))) [IsProbabilityMeasure ρ] :
    IsMarkovKernel (conditionalIndependenceKernel ρ) := by
  unfold conditionalIndependenceKernel
  infer_instance

/-- Canonical measure-theoretic conditional mutual information `I(X;Y|U)`.

It is a single KL divergence against the true `U` marginal and the fiberwise
conditional-independence reference. -/
noncomputable def conditionalMutualInfo
    (ρ : Measure (U × (X × Y))) [IsProbabilityMeasure ρ] : ENNReal :=
  klDiv ρ (ρ.fst ⊗ₘ conditionalIndependenceKernel ρ)

lemma conditionalMutualInfo_nonneg
    (ρ : Measure (U × (X × Y))) [IsProbabilityMeasure ρ] :
    0 ≤ conditionalMutualInfo ρ := by
  exact bot_le

/-- If the true law is exactly its conditional-independence reference, the
conditional mutual information vanishes. -/
theorem conditionalMutualInfo_eq_zero_of_eq_reference
    (ρ : Measure (U × (X × Y))) [IsProbabilityMeasure ρ]
    (hρ : ρ = ρ.fst ⊗ₘ conditionalIndependenceKernel ρ) :
    conditionalMutualInfo ρ = 0 := by
  unfold conditionalMutualInfo
  rw [hρ]
  simp

end

end UEOT.V3.InformationConditionalMutual
