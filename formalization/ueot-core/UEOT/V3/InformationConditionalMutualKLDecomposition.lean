import UEOT.V3.InformationConditionalMutual
import UEOT.V3.InformationKernelKL
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
# General conditional mutual-information KL decomposition

This is the type-generic form of the decomposition already machine-checked for
the P-INFO-04 binary clause.  Finite global conditional mutual information
implies fiberwise absolute continuity and identifies the global KL quantity with
the `U`-average of ordinary fiber mutual informations.
-/

namespace UEOT.V3.InformationConditionalMutualKLDecomposition

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationCore
open UEOT.V3.InformationKernelKL
open UEOT.V3.InformationConditionalMutual

universe uU uX uY

variable {U : Type uU} {X : Type uX} {Y : Type uY}
variable [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]
variable [StandardBorelSpace U] [StandardBorelSpace X] [StandardBorelSpace Y]
variable [Nonempty X] [Nonempty Y]

/-- Finite canonical conditional information implies fiberwise absolute
continuity of the true conditional joint law with respect to the conditional
independence reference. -/
theorem conditionalJointKernel_ac_reference_ae_of_ne_top
    (ρ : Measure (U × (X × Y))) [IsProbabilityMeasure ρ]
    (hfin : conditionalMutualInfo ρ ≠ ⊤) :
    ∀ᵐ u ∂ρ.fst,
      conditionalJointKernel ρ u ≪ conditionalIndependenceKernel ρ u := by
  have hfin' :
      klDiv ρ (ρ.fst ⊗ₘ conditionalIndependenceKernel ρ) ≠ ⊤ := by
    simpa [conditionalMutualInfo] using hfin
  have hglobal :
      ρ ≪ ρ.fst ⊗ₘ conditionalIndependenceKernel ρ :=
    (InformationTheory.klDiv_ne_top_iff.mp hfin').1
  have hdis : ρ.fst ⊗ₘ conditionalJointKernel ρ = ρ := by
    simpa [conditionalJointKernel] using
      (Measure.disintegrate ρ ρ.condKernel)
  have hglobal' :
      ρ.fst ⊗ₘ conditionalJointKernel ρ ≪
        ρ.fst ⊗ₘ conditionalIndependenceKernel ρ := by
    rw [hdis]
    exact hglobal
  exact hglobal'.kernel_of_compProd

/-- Finite canonical conditional mutual information is the average fiber KL. -/
theorem conditionalMutualInfo_eq_lintegral_fiberKL_of_ne_top
    (ρ : Measure (U × (X × Y))) [IsProbabilityMeasure ρ]
    (hfin : conditionalMutualInfo ρ ≠ ⊤) :
    conditionalMutualInfo ρ =
      ∫⁻ u,
        klDiv (conditionalJointKernel ρ u)
          (conditionalIndependenceKernel ρ u) ∂ρ.fst := by
  have hdis : ρ.fst ⊗ₘ conditionalJointKernel ρ = ρ := by
    simpa [conditionalJointKernel] using
      (Measure.disintegrate ρ ρ.condKernel)
  have hac := conditionalJointKernel_ac_reference_ae_of_ne_top ρ hfin
  unfold conditionalMutualInfo
  calc
    klDiv ρ (ρ.fst ⊗ₘ conditionalIndependenceKernel ρ) =
        klDiv (ρ.fst ⊗ₘ conditionalJointKernel ρ)
          (ρ.fst ⊗ₘ conditionalIndependenceKernel ρ) := by
      rw [hdis]
    _ = ∫⁻ u,
        klDiv (conditionalJointKernel ρ u)
          (conditionalIndependenceKernel ρ u) ∂ρ.fst :=
      klDiv_compProd_right_eq_lintegral
        (μ := ρ.fst)
        (κ := conditionalJointKernel ρ)
        (η := conditionalIndependenceKernel ρ) hac

/-- Fiber KL against the conditional-independence reference is ordinary mutual
information of the conditional joint law. -/
theorem fiberKL_eq_mutualInfo
    (ρ : Measure (U × (X × Y))) [IsProbabilityMeasure ρ]
    (u : U) :
    klDiv (conditionalJointKernel ρ u)
        (conditionalIndependenceKernel ρ u) =
      mutualInfo (conditionalJointKernel ρ u) := by
  simp only [conditionalIndependenceKernel, Kernel.prod_apply,
    Kernel.fst_apply, Kernel.snd_apply, mutualInfo, Measure.fst, Measure.snd]

/-- Finite canonical conditional mutual information is the `U`-average of
ordinary mutual information in the true conditional fibers. -/
theorem conditionalMutualInfo_eq_lintegral_fiberMutualInfo_of_ne_top
    (ρ : Measure (U × (X × Y))) [IsProbabilityMeasure ρ]
    (hfin : conditionalMutualInfo ρ ≠ ⊤) :
    conditionalMutualInfo ρ =
      ∫⁻ u, mutualInfo (conditionalJointKernel ρ u) ∂ρ.fst := by
  rw [conditionalMutualInfo_eq_lintegral_fiberKL_of_ne_top ρ hfin]
  apply lintegral_congr
  intro u
  exact fiberKL_eq_mutualInfo ρ u

end

end UEOT.V3.InformationConditionalMutualKLDecomposition
