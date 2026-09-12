import UEOT.V3.InformationConditionalBinary
import UEOT.V3.InformationKernelKL
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
# Conditional binary KL decomposition

For the source-faithful conditional mutual information
`I(M;B|U) = KL(P_{U,M,B} || P_U ⊗ P_{M|U} ⊗ P_{B|U})`, finite global KL
implies the required fiberwise absolute continuity.  The common-base KL
formula then identifies the global quantity with the `U`-average of the
fiber mutual informations.
-/

namespace UEOT.V3.InformationConditionalBinaryKLDecomposition

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationCore
open UEOT.V3.InformationKernelKL
open UEOT.V3.InformationConditionalBinary

universe uU uM

variable {U : Type uU} {M : Type uM}
variable [MeasurableSpace U] [MeasurableSpace M]
variable [StandardBorelSpace U] [StandardBorelSpace M]
variable [Nonempty M]

/-- Finite canonical conditional binary information implies fiberwise absolute
continuity of `P(M,B|U=u)` with respect to
`P(M|U=u) × P(B|U=u)` for `P_U`-a.e. `u`. -/
theorem conditionalBinaryKernel_ac_reference_ae_of_ne_top
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (hfin : conditionalBinaryMutualInfo ρ ≠ ⊤) :
    ∀ᵐ u ∂ρ.fst,
      conditionalBinaryKernel ρ u ≪ conditionalBinaryReferenceKernel ρ u := by
  have hfin' :
      klDiv ρ (ρ.fst ⊗ₘ conditionalBinaryReferenceKernel ρ) ≠ ⊤ := by
    simpa [conditionalBinaryMutualInfo] using hfin
  have hglobal :
      ρ ≪ ρ.fst ⊗ₘ conditionalBinaryReferenceKernel ρ :=
    (InformationTheory.klDiv_ne_top_iff.mp hfin').1
  have hdis : ρ.fst ⊗ₘ conditionalBinaryKernel ρ = ρ := by
    simpa [conditionalBinaryKernel] using
      (Measure.disintegrate ρ ρ.condKernel)
  have hglobal' :
      ρ.fst ⊗ₘ conditionalBinaryKernel ρ ≪
        ρ.fst ⊗ₘ conditionalBinaryReferenceKernel ρ := by
    rw [hdis]
    exact hglobal
  exact hglobal'.kernel_of_compProd

/-- Finite canonical conditional binary mutual information is the average
fiber KL divergence. -/
theorem conditionalBinaryMutualInfo_eq_lintegral_fiberKL_of_ne_top
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (hfin : conditionalBinaryMutualInfo ρ ≠ ⊤) :
    conditionalBinaryMutualInfo ρ =
      ∫⁻ u,
        klDiv (conditionalBinaryKernel ρ u)
          (conditionalBinaryReferenceKernel ρ u) ∂ρ.fst := by
  have hdis : ρ.fst ⊗ₘ conditionalBinaryKernel ρ = ρ := by
    simpa [conditionalBinaryKernel] using
      (Measure.disintegrate ρ ρ.condKernel)
  have hac := conditionalBinaryKernel_ac_reference_ae_of_ne_top ρ hfin
  unfold conditionalBinaryMutualInfo
  calc
    klDiv ρ (ρ.fst ⊗ₘ conditionalBinaryReferenceKernel ρ) =
        klDiv (ρ.fst ⊗ₘ conditionalBinaryKernel ρ)
          (ρ.fst ⊗ₘ conditionalBinaryReferenceKernel ρ) := by
      rw [hdis]
    _ = ∫⁻ u,
        klDiv (conditionalBinaryKernel ρ u)
          (conditionalBinaryReferenceKernel ρ u) ∂ρ.fst :=
      klDiv_compProd_right_eq_lintegral
        (μ := ρ.fst)
        (κ := conditionalBinaryKernel ρ)
        (η := conditionalBinaryReferenceKernel ρ) hac

/-- Fiberwise KL against the conditional-independence reference is exactly the
ordinary mutual information of the conditional law `P(M,B|U=u)`. -/
theorem fiberKL_eq_mutualInfo
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) :
    klDiv (conditionalBinaryKernel ρ u)
        (conditionalBinaryReferenceKernel ρ u) =
      mutualInfo (conditionalBinaryKernel ρ u) := by
  simp [conditionalBinaryReferenceKernel, mutualInfo,
    Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply]

/-- Finite canonical conditional binary mutual information is the `U`-average
of the ordinary mutual information of each true conditional fiber. -/
theorem conditionalBinaryMutualInfo_eq_lintegral_fiberMutualInfo_of_ne_top
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (hfin : conditionalBinaryMutualInfo ρ ≠ ⊤) :
    conditionalBinaryMutualInfo ρ =
      ∫⁻ u, mutualInfo (conditionalBinaryKernel ρ u) ∂ρ.fst := by
  rw [conditionalBinaryMutualInfo_eq_lintegral_fiberKL_of_ne_top ρ hfin]
  apply lintegral_congr
  intro u
  exact fiberKL_eq_mutualInfo ρ u

end UEOT.V3.InformationConditionalBinaryKLDecomposition
