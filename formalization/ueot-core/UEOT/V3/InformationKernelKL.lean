import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# P-INFO-02 foundation — shared-base kernel KL integral

Mathlib's current KL chain rule deliberately stops at the composition-product
residual

`KL(μ ⊗ₘ κ || μ ⊗ₘ η)`

and its own source file records the integral representation

`∫⁻ x, KL(κ x || η x) ∂μ`

as a TODO.  P-INFO-02 needs exactly that bridge.

The two lemmas below are a minimal attributed adaptation of the Apache-2.0
formalization in
`Jiyuan-Tan/CausalSmith/Causalean/Mathlib/InformationTheory/KLBind.lean`
(Copyright (c) 2026 Jiyuan Tan).  The upstream project uses Lean 4.33.0;
UEOT is pinned to Lean 4.33.1.  No new KL definition is introduced here.
-/

namespace UEOT.V3.InformationKernelKL

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe uX uY

variable {X : Type uX} {Y : Type uY}
variable [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {κ η : Kernel X Y}

/-- The RN derivative of two composition products with the same base measure is
fiberwise the kernel RN derivative, under a.e. fiber absolute continuity. -/
theorem rnDeriv_compProd_right_of_ae_ac
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ᵐ x ∂μ, κ x ≪ η x) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
      fun p : X × Y => Kernel.rnDeriv κ η p.1 p.2 := by
  have hκ_eq : κ =ᵐ[μ] Kernel.withDensity η (Kernel.rnDeriv κ η) := by
    filter_upwards [hκη] with x hx
    exact (Kernel.withDensity_rnDeriv_eq (κ := κ) (η := η) (a := x) hx).symm
  have hcomp :
      μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity
        (fun p : X × Y => Kernel.rnDeriv κ η p.1 p.2) := by
    calc
      μ ⊗ₘ κ = μ ⊗ₘ Kernel.withDensity η (Kernel.rnDeriv κ η) :=
        Measure.compProd_congr hκ_eq
      _ = (μ ⊗ₘ η).withDensity
          (fun p : X × Y => Kernel.rnDeriv κ η p.1 p.2) := by
        rw [Measure.compProd_withDensity]
        exact Kernel.measurable_rnDeriv κ η
  rw [hcomp]
  have hwd := Measure.rnDeriv_withDensity_left_of_absolutelyContinuous
    (μ := μ ⊗ₘ η) (ν := μ ⊗ₘ η)
    (f := fun p : X × Y => Kernel.rnDeriv κ η p.1 p.2)
    Measure.AbsolutelyContinuous.rfl
    (Kernel.measurable_rnDeriv κ η).aemeasurable
  refine hwd.trans ?_
  filter_upwards [Measure.rnDeriv_self (μ ⊗ₘ η)] with p hp
  rw [hp, mul_one]

/-- Exact shared-base conditional-KL identity:

`KL(μ ⊗ₘ κ || μ ⊗ₘ η) = ∫⁻ x, KL(κ x || η x) ∂μ`.

This is the missing integral form needed to turn the KL residual in
`InformationStatistic` into an average fiberwise divergence. -/
theorem klDiv_compProd_right_eq_lintegral
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ᵐ x ∂μ, κ x ≪ η x) :
    InformationTheory.klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) =
      ∫⁻ x, InformationTheory.klDiv (κ x) (η x) ∂μ := by
  classical
  have hcomp_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.AbsolutelyContinuous.compProd_right hκη
  rw [InformationTheory.klDiv_eq_lintegral_klFun, if_pos hcomp_ac]
  trans ∫⁻ p : X × Y,
      ENNReal.ofReal
        (InformationTheory.klFun
          ((Kernel.rnDeriv κ η p.1 p.2).toReal)) ∂(μ ⊗ₘ η)
  · refine lintegral_congr_ae ?_
    filter_upwards [rnDeriv_compProd_right_of_ae_ac
      (μ := μ) (κ := κ) (η := η) hκη] with p hp
    rw [hp]
  · rw [Measure.lintegral_compProd]
    · refine lintegral_congr_ae ?_
      filter_upwards [hκη] with x hx
      rw [InformationTheory.klDiv_eq_lintegral_klFun, if_pos hx]
      refine lintegral_congr_ae ?_
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure
        (κ := κ) (η := η) (a := x)] with y hy
      rw [hy]
    · fun_prop

end UEOT.V3.InformationKernelKL
