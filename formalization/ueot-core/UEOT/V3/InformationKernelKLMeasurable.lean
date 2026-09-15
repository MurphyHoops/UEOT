import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Measurability foundations for finite product kernels and fiber KL

P-COMP-01 needs two measure-theoretic facts that are not yet exposed by the
pinned Mathlib API in the exact form required by the frozen UEOT Core source:

1. a finite product of a measurably varying family of probability measures is
   itself measurable as a measure-valued map;
2. for finite kernels with countably generated target, the fiberwise
   Kullback--Leibler divergence is measurable in the source parameter.

The first proof is a minimal adaptation of the Apache-2.0 formalization in
`TauCetiProject/TauCeti`,
`TauCeti/MeasureTheory/Measure/ProductKernel.lean` (2026, Tau Ceti
contributors).  The second is a minimal adaptation of the Apache-2.0
formalization in `LeanMachineLearning/LML`,
`LeanMachineLearning/ForMathlib/InformationTheory/KullbackLeibler/ChainRule.lean`
(2026, Rémy Degenne).

No new KL or product-measure definition is introduced here; both lemmas are
bridges over the pinned Mathlib definitions.
-/

namespace UEOT.V3.InformationKernelKLMeasurable

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory

universe uΩ uI uX uY

/-- Finite products of probability measures depend measurably on their finite
family of factors.  This is the Giry-measurability bridge needed to turn block
marginals of a Markov kernel into a genuine finite product kernel. -/
theorem measurable_probabilityMeasure_pi
    {I : Type uI} [Fintype I]
    {X : I → Type uX} [∀ i, MeasurableSpace (X i)] :
    Measurable
      (ProbabilityMeasure.pi :
        (∀ i, ProbabilityMeasure (X i)) →
          ProbabilityMeasure (∀ i, X i)) := by
  have hcore : Measurable fun p : ∀ i, ProbabilityMeasure (X i) =>
      (ProbabilityMeasure.pi p).toMeasure := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (S := Set.pi univ ''
        Set.pi univ (fun i => {s : Set (X i) | MeasurableSet s}))
      generateFrom_pi.symm isPiSystem_pi ?_
    rintro _ ⟨B, hB, rfl⟩
    have hBmeas : ∀ i, MeasurableSet (B i) :=
      fun i => hB i (mem_univ i)
    simp_rw [ProbabilityMeasure.toMeasure_pi, Measure.pi_pi]
    exact Finset.measurable_prod Finset.univ fun i _ =>
      (Measure.measurable_coe (hBmeas i)).comp
        (measurable_subtype_coe.comp (measurable_pi_apply i))
  exact hcore.subtype_mk

/-- A finite dependent product of measurably varying probability measures is a
measurable measure-valued map. -/
theorem measurable_probabilityMeasure_pi_toMeasure
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {I : Type uI} [Fintype I]
    {X : I → Type uX} [∀ i, MeasurableSpace (X i)]
    (ν : ∀ i, Ω → ProbabilityMeasure (X i))
    (hν : ∀ i, Measurable (ν i)) :
    Measurable fun ω =>
      (ProbabilityMeasure.pi (fun i => ν i ω)).toMeasure := by
  have hPi : Measurable (fun ω i => ν i ω) :=
    measurable_pi_iff.mpr hν
  exact
    (measurable_subtype_coe.comp measurable_probabilityMeasure_pi).comp hPi

/-- For finite kernels with countably generated target, fiberwise KL is a
measurable extended-real-valued function of the source parameter. -/
theorem measurable_klDiv_kernel
    {X : Type uX} {Y : Type uY}
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (κ η : Kernel X Y) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable fun x => klDiv (κ x) (η x) := by
  classical
  have hMeasIntegral : Measurable fun x =>
      ∫⁻ y, ENNReal.ofReal
        (klFun (Kernel.rnDeriv κ η x y).toReal) ∂(η x) :=
    Measurable.lintegral_kernel_prod_right
      ((measurable_klFun.comp
        (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal)
  have hEq : ∀ x, klDiv (κ x) (η x) =
      if κ x ≪ η x then
        ∫⁻ y, ENNReal.ofReal
          (klFun (Kernel.rnDeriv κ η x y).toReal) ∂(η x)
      else ∞ := by
    intro x
    split_ifs with hac
    · rw [klDiv_eq_lintegral_klFun_of_ac hac]
      refine lintegral_congr_ae ?_
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure
        (κ := κ) (η := η) (a := x)] with y hy
      rw [hy]
    · exact klDiv_of_not_ac hac
  simp_rw [hEq]
  exact Measurable.ite
    (Kernel.measurableSet_absolutelyContinuous κ η)
    hMeasIntegral measurable_const

end

end UEOT.V3.InformationKernelKLMeasurable
