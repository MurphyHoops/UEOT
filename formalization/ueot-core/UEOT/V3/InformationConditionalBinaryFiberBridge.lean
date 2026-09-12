import UEOT.V3.InformationPInfo04Conditional
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Conditional binary fiber/disintegration bridge

This module identifies the global posterior `P(B | U,M)` used by the
source-facing conditional Fano layer with the second-stage conditional kernel
obtained by first conditioning `(M,B)` on `U` and then conditioning `B` on `M`
inside each `U`-fiber.
-/

namespace UEOT.V3.InformationConditionalBinaryFiberBridge

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open UEOT.V3.InformationConditionalBinary
open UEOT.V3.InformationPInfo04Conditional

universe uU uM

variable {U : Type uU} {M : Type uM}
variable [MeasurableSpace U] [MeasurableSpace M]
variable [StandardBorelSpace U] [StandardBorelSpace M]
variable [Nonempty M]

/-- Reassociating the true joint law is exactly the iterated composition
product obtained from `P(M,B|U)` and its second-stage conditional kernel
`P(B|U,M)`. -/
theorem binaryUMJoint_eq_iteratedCompProd
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    binaryUMJoint ρ =
      (ρ.fst ⊗ₘ (conditionalBinaryKernel ρ).fst) ⊗ₘ
        Kernel.condKernel (conditionalBinaryKernel ρ) := by
  have hρ : ρ.fst ⊗ₘ conditionalBinaryKernel ρ = ρ := by
    simpa [conditionalBinaryKernel] using
      (Measure.disintegrate ρ ρ.condKernel)
  have hk :
      (conditionalBinaryKernel ρ).fst ⊗ₖ
          Kernel.condKernel (conditionalBinaryKernel ρ) =
        conditionalBinaryKernel ρ :=
    (conditionalBinaryKernel ρ).disintegrate _
  unfold binaryUMJoint
  calc
    Measure.map reassocUMB ρ =
        Measure.map reassocUMB (ρ.fst ⊗ₘ conditionalBinaryKernel ρ) :=
      congrArg (Measure.map reassocUMB) hρ.symm
    _ = Measure.map reassocUMB
          (ρ.fst ⊗ₘ ((conditionalBinaryKernel ρ).fst ⊗ₖ
            Kernel.condKernel (conditionalBinaryKernel ρ))) := by
      rw [hk]
    _ = (ρ.fst ⊗ₘ (conditionalBinaryKernel ρ).fst) ⊗ₘ
          Kernel.condKernel (conditionalBinaryKernel ρ) := by
      simpa [reassocUMB] using
        (Measure.compProd_assoc
          (μ := ρ.fst)
          (κ := (conditionalBinaryKernel ρ).fst)
          (η := Kernel.condKernel (conditionalBinaryKernel ρ)))

/-- The `(U,M)` marginal of the reassociated joint is the composition product
`P_U ⊗ P(M|U)`. -/
theorem binaryUMJoint_fst_eq_compProd
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    (binaryUMJoint ρ).fst =
      ρ.fst ⊗ₘ (conditionalBinaryKernel ρ).fst := by
  rw [binaryUMJoint_eq_iteratedCompProd]
  simpa using
    (Measure.fst_compProd
      (μ := ρ.fst ⊗ₘ (conditionalBinaryKernel ρ).fst)
      (κ := Kernel.condKernel (conditionalBinaryKernel ρ)))

/-- The global posterior used by the source-Fano module is almost everywhere
the kernel-level second-stage conditional kernel. -/
theorem posteriorBitGivenUM_ae_eq_kernelCondKernel
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    posteriorBitGivenUM ρ =ᵐ[(binaryUMJoint ρ).fst]
      Kernel.condKernel (conditionalBinaryKernel ρ) := by
  have hdis :
      binaryUMJoint ρ =
        (binaryUMJoint ρ).fst ⊗ₘ
          Kernel.condKernel (conditionalBinaryKernel ρ) := by
    calc
      binaryUMJoint ρ =
          (ρ.fst ⊗ₘ (conditionalBinaryKernel ρ).fst) ⊗ₘ
            Kernel.condKernel (conditionalBinaryKernel ρ) :=
        binaryUMJoint_eq_iteratedCompProd ρ
      _ = (binaryUMJoint ρ).fst ⊗ₘ
            Kernel.condKernel (conditionalBinaryKernel ρ) := by
        rw [binaryUMJoint_fst_eq_compProd]
  have h := ProbabilityTheory.eq_condKernel_of_measure_eq_compProd
    (ρ := binaryUMJoint ρ)
    (Kernel.condKernel (conditionalBinaryKernel ρ)) hdis
  filter_upwards [h] with x hx
  simpa [posteriorBitGivenUM] using hx.symm

/-- At fixed `u`, the kernel-level second-stage conditional law coincides
`P(M|U=u)`-a.e. with the ordinary conditional kernel of the fiber measure
`P(M,B|U=u)`. -/
theorem kernelCondKernel_ae_eq_fiberCondKernel
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) :
    (fun m => Kernel.condKernel (conditionalBinaryKernel ρ) (u, m))
      =ᵐ[(conditionalBinaryKernel ρ).fst u]
        (conditionalBinaryKernel ρ u).condKernel := by
  exact Kernel.condKernel_apply_eq_condKernel (conditionalBinaryKernel ρ) u

end UEOT.V3.InformationConditionalBinaryFiberBridge
