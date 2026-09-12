import UEOT.V3.InformationCore
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Conditional binary information foundation

This module provides the source-faithful conditional-information objects needed
by the conditional binary clause of P-INFO-04.  The construction is based on
true disintegration over `U`; it does **not** define conditional entropy by a
subtraction such as `H(B) - I(B;U)`.

For a joint law on `U × (M × Fin 2)`:

* `conditionalBinaryKernel` is `P(M,B | U)`;
* `conditionalBinaryReferenceKernel` is the fiberwise product
  `P(M|U) × P(B|U)`;
* `conditionalBinaryMutualInfo` is the KL divergence from the true joint law
  to `P_U ⊗ P(M|U) ⊗ P(B|U)`;
* `conditionalBinaryEntropy` is the average binary entropy of `P(B=1|U=u)`.

The binary entropy is real-valued and automatically finite; the conditional
mutual information remains extended-real valued.
-/

namespace UEOT.V3.InformationConditionalBinary

open MeasureTheory InformationTheory ProbabilityTheory
open UEOT.V3.InformationCore
open scoped ENNReal ProbabilityTheory

universe uU uM

variable {U : Type uU} {M : Type uM}
variable [MeasurableSpace U] [MeasurableSpace M]
variable [StandardBorelSpace U] [StandardBorelSpace M]
variable [Nonempty M]

/-- The true conditional law `P(M,B | U)` for a binary variable `B : Fin 2`. -/
noncomputable def conditionalBinaryKernel
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    Kernel U (M × Fin 2) :=
  ρ.condKernel

instance conditionalBinaryKernel_isMarkov
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    IsMarkovKernel (conditionalBinaryKernel ρ) := by
  unfold conditionalBinaryKernel
  infer_instance

/-- Fiberwise conditional-independence reference `P(M|U) × P(B|U)`. -/
noncomputable def conditionalBinaryReferenceKernel
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    Kernel U (M × Fin 2) :=
  (conditionalBinaryKernel ρ).fst ×ₖ (conditionalBinaryKernel ρ).snd

instance conditionalBinaryReferenceKernel_isMarkov
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    IsMarkovKernel (conditionalBinaryReferenceKernel ρ) := by
  unfold conditionalBinaryReferenceKernel
  infer_instance

/-- Canonical conditional mutual information `I(M;B|U)` as a single global
KL divergence against the fiberwise conditional-independence reference. -/
noncomputable def conditionalBinaryMutualInfo
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] : ENNReal :=
  klDiv ρ (ρ.fst ⊗ₘ conditionalBinaryReferenceKernel ρ)

/-- Conditional probability `P(B=1 | U=u)`. -/
noncomputable def conditionalBitOneProb
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) : ℝ :=
  ((conditionalBinaryKernel ρ).snd u).real ({1} : Set (Fin 2))

theorem measurable_conditionalBitOneProb
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    Measurable (conditionalBitOneProb ρ) := by
  unfold conditionalBitOneProb
  exact ENNReal.measurable_toReal.comp
    ((conditionalBinaryKernel ρ).snd.measurable_coe (measurableSet_singleton 1))

theorem conditionalBitOneProb_nonneg
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) :
    0 ≤ conditionalBitOneProb ρ u := by
  exact measureReal_nonneg

theorem conditionalBitOneProb_le_one
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) :
    conditionalBitOneProb ρ u ≤ 1 := by
  exact measureReal_le_one

/-- Fiber binary entropy `H(B | U=u)`. -/
noncomputable def conditionalBinaryEntropyFiber
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) : ℝ :=
  Real.binEntropy (conditionalBitOneProb ρ u)

theorem measurable_conditionalBinaryEntropyFiber
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    Measurable (conditionalBinaryEntropyFiber ρ) := by
  unfold conditionalBinaryEntropyFiber
  exact Real.binEntropy_continuous.measurable.comp
    (measurable_conditionalBitOneProb ρ)

theorem conditionalBinaryEntropyFiber_nonneg
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) :
    0 ≤ conditionalBinaryEntropyFiber ρ u := by
  unfold conditionalBinaryEntropyFiber
  exact Real.binEntropy_nonneg
    (conditionalBitOneProb_nonneg ρ u)
    (conditionalBitOneProb_le_one ρ u)

theorem conditionalBinaryEntropyFiber_le_log_two
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) :
    conditionalBinaryEntropyFiber ρ u ≤ Real.log 2 := by
  exact Real.binEntropy_le_log_two

/-- Source-level conditional binary entropy `H(B|U)`, defined as the true
fiber entropy average. -/
noncomputable def conditionalBinaryEntropy
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] : ℝ :=
  ∫ u, conditionalBinaryEntropyFiber ρ u ∂ρ.fst

end UEOT.V3.InformationConditionalBinary
