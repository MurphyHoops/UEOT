import UEOT.V3.InformationPinsker
import UEOT.V3.InformationKernelTV
import UEOT.V3.InformationKernelKL
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# P-INFO-02 — averaged Pinsker inequality for Markov kernels

This module is the first genuinely compositional P-INFO-02 layer.  It combines
three already machine-checked ingredients:

* measure-level Pinsker (`InformationPinsker`);
* measurability of UEOT's pointwise kernel TV (`InformationKernelTV`);
* the shared-base KL identity (`InformationKernelKL`).

For a probability base law `μ` and Markov kernels `κ,η`, finite shared-base KL
controls the average predictive total-variation defect:

`∫ x, TV(κ x, η x) dμ ≤ sqrt(KL(μ ⊗ₘ κ || μ ⊗ₘ η) / 2)`.

This theorem is deliberately source-agnostic.  The final P-INFO-02 semantic
bridge identifying the relevant shared-base KL with the canonical conditional
information residual remains separate.
-/

namespace UEOT.V3.InformationKernelPinsker

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.TotalVariation
open UEOT.V3.InformationPinsker
open UEOT.V3.InformationKernelTV
open UEOT.V3.InformationKernelKL

universe uX uY

variable {X : Type uX} {Y : Type uY}
variable [MeasurableSpace X] [MeasurableSpace Y]

/-- A jointly measurable RN-density representation of the fiber KL.  Under
`κ x ≪ η x` it agrees with `klDiv (κ x) (η x)`. -/
noncomputable def fiberKL
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (κ η : Kernel X Y) (x : X) : ℝ≥0∞ :=
  ∫⁻ y,
    ENNReal.ofReal
      (klFun ((Kernel.rnDeriv κ η x y).toReal)) ∂(η x)

/-- The RN-density representation of fiber KL is measurable in the base point. -/
theorem measurable_fiberKL
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (κ η : Kernel X Y) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fiberKL κ η) := by
  unfold fiberKL
  refine Measurable.lintegral_kernel_prod_right (κ := η) ?_
  exact measurable_klFun.comp
      (Kernel.measurable_rnDeriv κ η).ennreal_toReal
    |>.ennreal_ofReal

/-- On fibers where absolute continuity holds, the measurable RN representation
is exactly Mathlib's `klDiv`. -/
theorem fiberKL_eq_klDiv_ae
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (μ : Measure X) (κ η : Kernel X Y)
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ᵐ x ∂μ, κ x ≪ η x) :
    fiberKL κ η =ᵐ[μ] fun x => klDiv (κ x) (η x) := by
  filter_upwards [hκη] with x hx
  unfold fiberKL
  rw [klDiv_eq_lintegral_klFun, if_pos hx]
  refine lintegral_congr_ae ?_
  filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure
    (κ := κ) (η := η) (a := x)] with y hy
  rw [hy]

/-- **Averaged kernel Pinsker.**  For Markov kernels over a probability base,
finite shared-base KL controls the expected pointwise TV defect with the sharp
Pinsker/Jensen constant `1/2`. -/
theorem integral_tvDist_le_sqrt_klDiv_compProd
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hκη : ∀ᵐ x ∂μ, κ x ≪ η x)
    (hfin : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ⊤) :
    (∫ x, tvDist (κ x) (η x) ∂μ) ≤
      Real.sqrt ((klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal / 2) := by
  let K : X → ℝ≥0∞ := fiberKL κ η
  let k : X → ℝ := fun x => (K x).toReal / 2

  have hKmeas : Measurable K := by
    simpa [K] using measurable_fiberKL κ η
  have hKae : K =ᵐ[μ] fun x => klDiv (κ x) (η x) := by
    simpa [K] using fiberKL_eq_klDiv_ae μ κ η hκη

  have hKLlin : ∫⁻ x, K x ∂μ = klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) := by
    rw [lintegral_congr_ae hKae]
    exact (klDiv_compProd_right_eq_lintegral
      (μ := μ) (κ := κ) (η := η) hκη).symm
  have hKlin_fin : (∫⁻ x, K x ∂μ) ≠ ∞ := by
    rw [hKLlin]
    exact hfin
  have hKlt : ∀ᵐ x ∂μ, K x < ∞ :=
    ae_lt_top hKmeas hKlin_fin
  have hKreal_int : Integrable (fun x => (K x).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hKmeas.aemeasurable hKlin_fin
  have hk_int : Integrable k μ := by
    simpa [k] using hKreal_int.div_const 2
  have hk_meas : Measurable k := by
    dsimp [k]
    exact hKmeas.ennreal_toReal.div_const 2
  have hk_nonneg : ∀ᵐ x ∂μ, 0 ≤ k x := by
    exact Filter.Eventually.of_forall fun x => by
      dsimp [k]
      positivity
  have hk_integral :
      (∫ x, k x ∂μ) = (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal / 2 := by
    dsimp [k]
    rw [integral_div]
    have htoReal :
        (∫ x, (K x).toReal ∂μ) = (∫⁻ x, K x ∂μ).toReal :=
      integral_toReal hKmeas.aemeasurable hKlt
    rw [htoReal, hKLlin]

  have hsqrt_meas : AEStronglyMeasurable (fun x => Real.sqrt (k x)) μ :=
    (Real.continuous_sqrt.measurable.comp hk_meas).aestronglyMeasurable
  have hsqrt_int : Integrable (fun x => Real.sqrt (k x)) μ := by
    refine Integrable.mono'
      (hk_int.add (integrable_const (1 : ℝ))) hsqrt_meas ?_
    filter_upwards [hk_nonneg] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    change Real.sqrt (k x) ≤ k x + 1
    have hs2 : (Real.sqrt (k x)) ^ 2 = k x := Real.sq_sqrt hx
    nlinarith [sq_nonneg (Real.sqrt (k x) - 1)]

  have htv_meas : Measurable fun x => tvDist (κ x) (η x) :=
    measurable_tvDist_kernel κ η
  have htv_int : Integrable (fun x => tvDist (κ x) (η x)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      htv_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tvDist_nonneg (κ x) (η x))]
      exact tvDist_le_one (κ x) (η x)

  have hpoint : ∀ᵐ x ∂μ, tvDist (κ x) (η x) ≤ Real.sqrt (k x) := by
    filter_upwards [hκη, hKae, hKlt] with x hac hEq hLt
    have hfiberfin : klDiv (κ x) (η x) ≠ ⊤ := by
      rw [← hEq]
      exact ne_of_lt hLt
    have hp := pinskerBound_of_ac_of_ne_top (κ x) (η x) hac hfiberfin
    unfold PinskerBound at hp
    simpa [k, hEq] using hp

  have hint_le :
      (∫ x, tvDist (κ x) (η x) ∂μ) ≤ ∫ x, Real.sqrt (k x) ∂μ :=
    integral_mono_ae htv_int hsqrt_int hpoint

  have hjensen :
      (∫ x, Real.sqrt (k x) ∂μ) ≤ Real.sqrt (∫ x, k x ∂μ) := by
    have hsqrt_concave := Real.strictConcaveOn_sqrt.concaveOn
    have h := hsqrt_concave.le_map_integral
      Real.continuous_sqrt.continuousOn isClosed_Ici
      hk_nonneg hk_int
      (by simpa [Function.comp_def] using hsqrt_int)
    simpa [Function.comp_def] using h

  calc
    (∫ x, tvDist (κ x) (η x) ∂μ)
        ≤ ∫ x, Real.sqrt (k x) ∂μ := hint_le
    _ ≤ Real.sqrt (∫ x, k x ∂μ) := hjensen
    _ = Real.sqrt ((klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal / 2) := by
      rw [hk_integral]

end UEOT.V3.InformationKernelPinsker
