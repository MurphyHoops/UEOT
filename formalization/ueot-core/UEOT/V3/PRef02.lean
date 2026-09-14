import UEOT.V3.FiniteBayesBelief
import UEOT.V3.GeneralBayesPosterior

/-!
# P-REF-02 — belief sufficiency source-facing assembly

This module assembles the two complementary interfaces required by frozen Core
3 §27.2.

* `p_ref_02_general_joint` and `p_ref_02_general_update` express the
  observation-law / posterior-kernel sufficiency for an arbitrary measurable
  observation space, using the Standard-Borel posterior/disintegration theorem.
* `p_ref_02_discrete_*` exposes the finite latent-state Bayes fraction and the
  mandatory zero-evidence `modelConflict` behavior from the source formula.
* `p_ref_02_discounted_step` records that one-step bounded-discount control data
  are functions of the current belief and action only; the Bellman theory itself
  belongs to the control layer and is not reproved here.

Scope boundary: these are model-internal sufficiency statements. Parameter
or mechanism drift, or interventions that change the declared transition or
observation kernels, require state augmentation or an explicit error interface.
-/

namespace UEOT.V3.PRef02

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe uZ uA uY uTheta uX

/-- General-observation part of P-REF-02: the predictive observation marginal
and regular posterior reconstruct the same one-step joint law determined by the
current belief and action. -/
theorem p_ref_02_general_joint
    {Z : Type uZ} {A : Type uA} {Y : Type uY}
    [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableSpace A] [MeasurableSpace Y]
    (b : Measure Z) [IsProbabilityMeasure b]
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (a : A) :
    GeneralBayesPosterior.observationLaw b P O a ⊗ₘ
        GeneralBayesPosterior.posteriorKernel b P O a =
      (GeneralBayesPosterior.jointLaw b P O a).map Prod.swap :=
  GeneralBayesPosterior.posterior_reconstructs_joint b P O a

/-- General-observation part of P-REF-02: averaging the updated posterior over
the predictive observation law recovers the predicted latent law. -/
theorem p_ref_02_general_update
    {Z : Type uZ} {A : Type uA} {Y : Type uY}
    [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableSpace A] [MeasurableSpace Y]
    (b : Measure Z) [IsProbabilityMeasure b]
    (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) Y) [IsMarkovKernel O]
    (a : A) :
    GeneralBayesPosterior.posteriorKernel b P O a ∘ₘ
        GeneralBayesPosterior.observationLaw b P O a =
      GeneralBayesPosterior.predictedLaw b P a :=
  GeneralBayesPosterior.posterior_comp_observation b P O a

section DiscreteFormula

variable {Theta : Type uTheta} {X : Type uX} {A : Type uA} {Y : Type uY}
variable [Fintype Theta] [Fintype X] [Fintype Y]

/-- The denominator in the displayed finite Bayes formula is exactly the
predictive observation law and is normalized. -/
theorem p_ref_02_discrete_observation
    (M : FiniteBayesBelief.Model Theta X A Y)
    (b : FiniteBayesBelief.Belief Theta X) (a : A) :
    (∑ y : Y, FiniteBayesBelief.evidence M b a y) = 1 :=
  FiniteBayesBelief.evidence_sum_one M b a

/-- Positive-evidence specialization of the frozen Bayes formula. -/
theorem p_ref_02_discrete_posterior
    (M : FiniteBayesBelief.Model Theta X A Y)
    (b : FiniteBayesBelief.Belief Theta X) (a : A) (y : Y)
    (h : FiniteBayesBelief.evidence M b a y ≠ 0)
    (theta : Theta) (x' : X) :
    (FiniteBayesBelief.posterior M b a y h).mass theta x' =
      FiniteBayesBelief.jointObservationMass M b a y theta x' /
        FiniteBayesBelief.evidence M b a y :=
  FiniteBayesBelief.posterior_mass M b a y h theta x'

/-- Zero denominator is an explicit model conflict, never an arbitrary
posterior. -/
theorem p_ref_02_discrete_modelConflict
    (M : FiniteBayesBelief.Model Theta X A Y)
    (b : FiniteBayesBelief.Belief Theta X) (a : A) (y : Y) :
    FiniteBayesBelief.updateResult M b a y =
        FiniteBayesBelief.UpdateResult.modelConflict ↔
      FiniteBayesBelief.evidence M b a y = 0 :=
  FiniteBayesBelief.updateResult_eq_modelConflict_iff M b a y

/-- One-step discounted control quantity in belief coordinates. Both the
conditional expected reward and the continuation law are functions of `(b,a)`;
this is the source's reduction interface, not a duplicate Bellman theorem. -/
theorem p_ref_02_discounted_step
    (M : FiniteBayesBelief.Model Theta X A Y)
    (r : Theta → X → A → ℝ) (beta : ℝ)
    (V : FiniteBayesBelief.Belief Theta X → ℝ)
    (b : FiniteBayesBelief.Belief Theta X) (a : A) :
    FiniteBayesBelief.beliefControlStep M r beta V b a =
      FiniteBayesBelief.beliefReward r b a +
        beta * FiniteBayesBelief.continuationExpectation M b a V := rfl

end DiscreteFormula

end UEOT.V3.PRef02
