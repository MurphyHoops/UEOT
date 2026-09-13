import UEOT.V3.InformationConditionalMutualKLDecomposition
import UEOT.V3.InformationRecoverableDiscrete

/-!
# P-INFO-03 — conditional recoverability identity

This module lifts the countable recoverability identity to true `U`-fibers.
For a probability law on `U × (C × M)`, if one measurable decoder `d(U,M)`
recovers the countable state `C` in almost every conditional `U=u` fiber,
then the canonical conditional mutual information is exactly the `U`-average
of the Shannon entropy of the conditional `C` law.

This is the information-theoretic equality required by the lower-bound half of
P-INFO-03 after zero predictive distortion has been converted into measurable
recoverability of the canonical predictive core.
-/

namespace UEOT.V3.InformationConditionalRecoverableDiscrete

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationConditionalMutual
open UEOT.V3.InformationConditionalMutualKLDecomposition
open UEOT.V3.InformationRecoverableDiscrete
open UEOT.V3.InformationDiscreteEntropy

universe uU uC uM

variable {U : Type uU} {C : Type uC} {M : Type uM}
variable [MeasurableSpace U] [MeasurableSpace C] [MeasurableSpace M]
variable [StandardBorelSpace U] [StandardBorelSpace C] [StandardBorelSpace M]
variable [Countable C] [MeasurableSingletonClass C]
variable [Nonempty C] [Nonempty M]

/-- Freeze the side-information value `u` in a decoder that may use `(U,M)`. -/
def decoderAt (d : U × M → C) (u : U) : M → C :=
  fun m => d (u, m)

lemma measurable_decoderAt
    (d : U × M → C) (hd : Measurable d) (u : U) :
    Measurable (decoderAt d u) := by
  unfold decoderAt
  exact hd.comp (measurable_const.prodMk measurable_id)

/-- Fiberwise law-level recoverability of `C` from `(U,M)`.

The same measurable decoder is used in every fiber; only the side-information
value `u` is frozen.  This is the conditional form of the recoverability
hypothesis used by `InformationRecoverableDiscrete`. -/
def FiberRecoverable
    (ρ : Measure (U × (C × M))) [IsProbabilityMeasure ρ]
    (d : U × M → C) : Prop :=
  ∀ᵐ u ∂ρ.fst,
    (conditionalJointKernel ρ u).map (decodedCopyMap (decoderAt d u)) =
      UEOT.V3.InformationEntropyBound.copyJoint
        (conditionalJointKernel ρ u).fst

/-- Conditional entropy of the countable `C` coordinate, expressed directly
through the genuine conditional joint kernel `P(C,M|U=u)`. -/
noncomputable def conditionalCoreEntropy
    (ρ : Measure (U × (C × M))) [IsProbabilityMeasure ρ] : ENNReal :=
  ∫⁻ u,
    discreteShannonEntropy (conditionalJointKernel ρ u).fst ∂ρ.fst

/-- **Conditional recoverability identity.**

If `C` is measurably recoverable from `(U,M)` in almost every true conditional
fiber and the canonical conditional mutual information is finite, then

`I(C;M|U) = ∫ H(P(C|U=u)) dP_U(u)`.

No entropy subtraction is used. -/
theorem conditionalMutualInfo_eq_conditionalCoreEntropy_of_recoverable
    (ρ : Measure (U × (C × M))) [IsProbabilityMeasure ρ]
    (d : U × M → C) (hd : Measurable d)
    (hfin : conditionalMutualInfo ρ ≠ ⊤)
    (hrec : FiberRecoverable ρ d) :
    conditionalMutualInfo ρ = conditionalCoreEntropy ρ := by
  rw [conditionalMutualInfo_eq_lintegral_fiberMutualInfo_of_ne_top ρ hfin]
  unfold conditionalCoreEntropy
  apply lintegral_congr_ae
  filter_upwards [hrec] with u hu
  exact mutualInfo_eq_discreteShannonEntropy_of_recoverable
    (conditionalJointKernel ρ u)
    (decoderAt d u)
    (measurable_decoderAt d hd u)
    hu

end

end UEOT.V3.InformationConditionalRecoverableDiscrete
