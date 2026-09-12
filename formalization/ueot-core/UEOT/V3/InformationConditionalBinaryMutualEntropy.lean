import UEOT.V3.InformationConditionalBinaryKLDecomposition
import UEOT.V3.InformationConditionalBinaryEntropyLift
import UEOT.V3.InformationConditionalBinaryFiberMI
import UEOT.V3.InformationPInfo04Conditional

/-!
# Conditional binary mutual information = entropy drop

This is the final representation bridge for the conditional-binary clause of
P-INFO-04.  The source-faithful KL conditional mutual information is identified,
without entropy subtraction in the definition, with the finite real entropy
form `H(B|U) - H(B|M,U)`.
-/

namespace UEOT.V3.InformationConditionalBinaryMutualEntropy

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationCore
open UEOT.V3.InformationConditionalBinary
open UEOT.V3.InformationPInfo04Conditional
open UEOT.V3.InformationConditionalBinaryKLDecomposition
open UEOT.V3.InformationConditionalBinaryEntropyLift
open UEOT.V3.InformationConditionalBinaryFiberMI

universe uU uM

variable {U : Type uU} {M : Type uM}
variable [MeasurableSpace U] [MeasurableSpace M]
variable [StandardBorelSpace U] [StandardBorelSpace M]
variable [Nonempty M]

/-- The nested posterior-entropy fiber is integrable over the true `U` law. -/
theorem integrable_conditionalBinaryPosteriorEntropyFiber
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    Integrable (conditionalBinaryPosteriorEntropyFiber ρ) ρ.fst := by
  unfold conditionalBinaryPosteriorEntropyFiber
  simpa using (integrable_nestedPosteriorBinaryEntropy ρ).integral_compProd

/-- The real fiber information drop integrates to the source entropy form. -/
theorem integral_conditionalBinaryEntropyDrop_eq_informationEntropyForm
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    (∫ u, conditionalBinaryEntropyFiber ρ u -
        conditionalBinaryPosteriorEntropyFiber ρ u ∂ρ.fst) =
      conditionalBinaryInformationEntropyForm ρ := by
  have hH := integrable_conditionalBinaryEntropyFiber ρ
  have hpost := integrable_conditionalBinaryPosteriorEntropyFiber ρ
  rw [integral_sub hH hpost]
  unfold conditionalBinaryInformationEntropyForm conditionalBinaryEntropy
  rw [conditionalBinaryEntropyGivenUM_eq_integral_posteriorEntropyFiber]

/-- **Finite conditional binary KL/entropy bridge.**

Whenever the canonical KL conditional mutual information is finite, it equals
the ENNReal embedding of `H(B|U) - H(B|M,U)`.  No subtraction of extended-real
information quantities is used. -/
theorem conditionalBinaryMutualInfo_eq_ofReal_entropyForm_of_ne_top
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (hfin : conditionalBinaryMutualInfo ρ ≠ ⊤) :
    conditionalBinaryMutualInfo ρ =
      ENNReal.ofReal (conditionalBinaryInformationEntropyForm ρ) := by
  let g : U → ℝ := fun u =>
    conditionalBinaryEntropyFiber ρ u -
      conditionalBinaryPosteriorEntropyFiber ρ u
  have hH := integrable_conditionalBinaryEntropyFiber ρ
  have hpost := integrable_conditionalBinaryPosteriorEntropyFiber ρ
  have hg : Integrable g ρ.fst := hH.sub hpost
  have hgnonneg : ∀ u, 0 ≤ g u := by
    intro u
    unfold g
    rw [conditionalBinaryPosteriorEntropyFiber_eq_fiberPosteriorIntegral]
    exact fiber_entropy_drop_nonneg ρ u
  rw [conditionalBinaryMutualInfo_eq_lintegral_fiberMutualInfo_of_ne_top ρ hfin]
  calc
    (∫⁻ u, mutualInfo (conditionalBinaryKernel ρ u) ∂ρ.fst) =
        ∫⁻ u, ENNReal.ofReal (g u) ∂ρ.fst := by
      apply lintegral_congr
      intro u
      rw [← ENNReal.ofReal_toReal (fiberMutualInfo_ne_top ρ u)]
      congr 1
      unfold g
      rw [fiberMutualInfo_toReal_eq_entropy_drop]
      rw [conditionalBinaryPosteriorEntropyFiber_eq_fiberPosteriorIntegral]
    _ = ENNReal.ofReal (∫ u, g u ∂ρ.fst) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal hg
        (Filter.Eventually.of_forall hgnonneg)
    _ = ENNReal.ofReal (conditionalBinaryInformationEntropyForm ρ) := by
      congr 1
      unfold g
      exact integral_conditionalBinaryEntropyDrop_eq_informationEntropyForm ρ

/-- **P-INFO-04 conditional binary source theorem.**

For a measurable decoder with error at most `ε ≤ 1/2`, the canonical
conditional mutual information obeys the frozen-source lower bound
`I(M;B|U) ≥ H(B|U) - h₂(ε)`.  The `I=∞` case is handled separately, so no
finiteness assumption is exposed in the source contract. -/
theorem p_info_04_conditional_binary
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (d : U × M → Fin 2) (hd : Measurable d)
    (ε : ℝ)
    (herr : conditionalBinaryDecoderError ρ d ≤ ε)
    (hhalf : ε ≤ (2 : ℝ)⁻¹) :
    ENNReal.ofReal (conditionalBinaryEntropy ρ - Real.binEntropy ε) ≤
      conditionalBinaryMutualInfo ρ := by
  by_cases htop : conditionalBinaryMutualInfo ρ = ⊤
  · rw [htop]
    exact le_top
  · rw [conditionalBinaryMutualInfo_eq_ofReal_entropyForm_of_ne_top ρ htop]
    exact ENNReal.ofReal_mono
      (conditionalBinaryInformationEntropyForm_ge_sourceBound
        ρ d hd ε herr hhalf)

end UEOT.V3.InformationConditionalBinaryMutualEntropy
