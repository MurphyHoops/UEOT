import UEOT.V3.GeneralBayesPosterior
import UEOT.V3.PredictionDependent
import UEOT.V3.PredictionUpdate

/-!
# Theory Completion P10 — general-state Objecthood interface

Core v3 already contains the Standard-Borel/countable-protocol predictive-state
minimality theorem.  P10 therefore does not redo P-PRED-01.  This module closes
a narrower genuine general-state gap: for a Standard-Borel latent state and an
arbitrary measurable observation space, the regular posterior is a measurable
next-belief readout, its observation law is probabilistic, and averaging the
posterior against that observation law returns the predicted latent law.

The result is fixed at a current belief/action.  Joint measurability in the
current belief and action, needed for a full Markov kernel on the whole belief
space, is deliberately left as a stronger boundary.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open MeasureTheory ProbabilityTheory
open UEOT.V3.GeneralBayesPosterior

universe uZ uA uY

variable {Z : Type uZ} {A : Type uA} {Y : Type uY}
variable [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
variable [MeasurableSpace A] [MeasurableSpace Y]

/-- Observation prediction from a probability belief remains a probability law
without any finite/discrete observation assumption. -/
instance generalObservationLaw_isProbability
    (b : Measure Z) [IsProbabilityMeasure b]
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (a : A) :
    IsProbabilityMeasure (observationLaw b P O a) := by
  unfold observationLaw
  infer_instance

/-- The regular posterior is a measurable map from the general observation
space into the canonical measurable space of probability measures on `Z`. -/
theorem measurable_generalPosterior_readout
    (b : Measure Z) [IsProbabilityMeasure b]
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (a : A) :
    Measurable (fun y => posteriorKernel b P O a y) :=
  (posteriorKernel b P O a).measurable

/-- Distribution of the next posterior belief after sampling the next
observation.  This is a law on the general measure-valued belief space. -/
noncomputable def posteriorBeliefLaw
    (b : Measure Z) [IsProbabilityMeasure b]
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (a : A) : Measure (Measure Z) :=
  (observationLaw b P O a).map (fun y => posteriorKernel b P O a y)

instance posteriorBeliefLaw_isProbability
    (b : Measure Z) [IsProbabilityMeasure b]
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (a : A) :
    IsProbabilityMeasure (posteriorBeliefLaw b P O a) := by
  unfold posteriorBeliefLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_generalPosterior_readout b P O a).aemeasurable).2 inferInstance

/-- General-state Bayesian consistency: averaging the updated latent-state
posterior over the predictive observation law exactly recovers the predicted
latent law.  This is the measure-theoretic recursion identity behind the
measure-valued next-belief law. -/
theorem generalPosterior_barycenter_consistency
    (b : Measure Z) [IsProbabilityMeasure b]
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (a : A) :
    posteriorKernel b P O a ∘ₘ observationLaw b P O a =
      predictedLaw b P a :=
  posterior_comp_observation b P O a

/-- **P10 terminal theorem.**  For one arbitrary probability belief/action,
regular Bayesian updating over a general measurable observation space gives a
measurable posterior readout, a probability law on next beliefs, and exact
barycenter consistency.  No `Fintype Y` or discrete observation hypothesis is
used. -/
theorem p10_terminal_generalState_belief_update
    (b : Measure Z) [IsProbabilityMeasure b]
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (a : A) :
    Measurable (fun y => posteriorKernel b P O a y) ∧
    IsProbabilityMeasure (posteriorBeliefLaw b P O a) ∧
    posteriorKernel b P O a ∘ₘ observationLaw b P O a =
      predictedLaw b P a := by
  exact ⟨measurable_generalPosterior_readout b P O a,
    posteriorBeliefLaw_isProbability b P O a,
    generalPosterior_barycenter_consistency b P O a⟩

end UEOT.V3.Compression.TheoryCompletion
