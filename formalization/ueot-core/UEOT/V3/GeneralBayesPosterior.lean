import Mathlib.Probability.Kernel.Posterior
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# P-REF-02 — general-observation posterior interface

This module isolates the measure-theoretic part of Core 3 §27.2 that does not
require a discrete observation space. A current belief is represented by a
probability measure on the latent state `Z`; a controlled transition kernel and
observation kernel are frozen at action `a`. The predicted latent law, next
observation law, and regular posterior kernel are then canonical functions of
`(belief,a)`.

The posterior is Mathlib's Standard-Borel disintegration/posterior kernel. The
main identity below states that the observation marginal together with this
posterior reconstructs the joint next-latent/observation law (up to the standard
coordinate swap). Thus no finiteness or discreteness assumption is imposed on
the observation space.

The explicit positive-denominator Bayes fraction and zero-denominator
`modelConflict` interface remain in `FiniteBayesBelief` as the discrete formula
specialization required by the frozen source.
-/

namespace UEOT.V3.GeneralBayesPosterior

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe uZ uA uY uW

variable {Z : Type uZ} {A : Type uA} {Y : Type uY} {W : Type uW}
variable [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
variable [MeasurableSpace A] [MeasurableSpace Y] [MeasurableSpace W]

/-- Freeze a controlled kernel at one action. -/
def fixedActionKernel (κ : Kernel (Z × A) W) (a : A) : Kernel Z W :=
  κ.comap (fun z => (z, a)) (measurable_id.prodMk measurable_const)

instance fixedActionKernel_isMarkov
    (κ : Kernel (Z × A) W) [IsMarkovKernel κ] (a : A) :
    IsMarkovKernel (fixedActionKernel κ a) := by
  unfold fixedActionKernel
  infer_instance

/-- Predicted next-latent law determined by current belief and action. -/
noncomputable def predictedLaw
    (b : Measure Z) (P : Kernel (Z × A) Z) (a : A) : Measure Z :=
  fixedActionKernel P a ∘ₘ b

/-- Predictive next-observation law determined by current belief and action. -/
noncomputable def observationLaw
    (b : Measure Z) (P : Kernel (Z × A) Z)
    (O : Kernel (Z × A) Y) (a : A) : Measure Y :=
  fixedActionKernel O a ∘ₘ predictedLaw b P a

/-- Joint law of next latent state and observation. -/
noncomputable def jointLaw
    (b : Measure Z) (P : Kernel (Z × A) Z)
    (O : Kernel (Z × A) Y) (a : A) : Measure (Z × Y) :=
  predictedLaw b P a ⊗ₘ fixedActionKernel O a

/-- A Markov prediction of a probability belief is again a probability law. -/
instance predictedLaw_isProbability
    (b : Measure Z) [IsProbabilityMeasure b]
    (P : Kernel (Z × A) Z) [IsMarkovKernel P] (a : A) :
    IsProbabilityMeasure (predictedLaw b P a) := by
  unfold predictedLaw
  infer_instance

/-- Regular posterior of the next latent state given the next observation.
The latent state is Standard Borel, exactly the condition needed by Mathlib's
posterior/disintegration theorem. -/
noncomputable def posteriorKernel
    (b : Measure Z) [IsProbabilityMeasure b]
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (a : A) : Kernel Y Z :=
  (fixedActionKernel O a)†(predictedLaw b P a)

/-- The predictive observation marginal is the observation kernel composed with
the predicted latent law. This theorem is intentionally definitional: it makes
explicit that no history variable beyond `(b,a)` enters the law. -/
theorem observationLaw_eq
    (b : Measure Z) (P : Kernel (Z × A) Z)
    (O : Kernel (Z × A) Y) (a : A) :
    observationLaw b P O a = fixedActionKernel O a ∘ₘ predictedLaw b P a := rfl

/-- **General P-REF-02 posterior factorization.** The observation marginal and
regular posterior reconstruct the same joint law as the predicted latent law
followed by the observation kernel. Hence both the observation law and updated
belief kernel are canonical functions of `(b,a)` for an arbitrary measurable
observation space. -/
theorem posterior_reconstructs_joint
    (b : Measure Z) [IsProbabilityMeasure b]
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (a : A) :
    observationLaw b P O a ⊗ₘ posteriorKernel b P O a =
      (jointLaw b P O a).map Prod.swap := by
  change
    (fixedActionKernel O a ∘ₘ predictedLaw b P a) ⊗ₘ
        ((fixedActionKernel O a)†(predictedLaw b P a)) =
      (predictedLaw b P a ⊗ₘ fixedActionKernel O a).map Prod.swap
  exact ProbabilityTheory.compProd_posterior_eq_map_swap
    (κ := fixedActionKernel O a) (μ := predictedLaw b P a)

/-- Applying the posterior after drawing an observation recovers the predicted
latent law. This is the posterior analogue of Bayes consistency and is useful
for the belief-state control reduction. -/
theorem posterior_comp_observation
    (b : Measure Z) [IsProbabilityMeasure b]
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (a : A) :
    posteriorKernel b P O a ∘ₘ observationLaw b P O a = predictedLaw b P a := by
  change
    ((fixedActionKernel O a)†(predictedLaw b P a)) ∘ₘ
        fixedActionKernel O a ∘ₘ predictedLaw b P a = predictedLaw b P a
  exact ProbabilityTheory.posterior_comp_self
    (κ := fixedActionKernel O a) (μ := predictedLaw b P a)

end UEOT.V3.GeneralBayesPosterior
