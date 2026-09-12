import UEOT.V3.InformationConditionalBinaryFiberBridge
import UEOT.V3.InformationBinaryEntropy
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic.NormNum

/-!
# Conditional binary posterior-entropy lift

The parameterized conditional measure `(conditionalBinaryKernel ρ u).condKernel`
is not used as a globally measurable object.  Instead we work with the genuine
kernel-level second-stage conditional kernel
`Kernel.condKernel (conditionalBinaryKernel ρ) (u,m)`, which is jointly
measurable in `(u,m)`, and use the nested-disintegration bridge to identify it
with the ordinary fiber conditional law almost everywhere.
-/

namespace UEOT.V3.InformationConditionalBinaryEntropyLift

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open UEOT.V3.InformationConditionalBinary
open UEOT.V3.InformationPInfo04Conditional
open UEOT.V3.InformationConditionalBinaryFiberBridge
open UEOT.V3.InformationBinaryConditionalMean
open UEOT.V3.InformationBinaryEntropy

universe uU uM

variable {U : Type uU} {M : Type uM}
variable [MeasurableSpace U] [MeasurableSpace M]
variable [StandardBorelSpace U] [StandardBorelSpace M]
variable [Nonempty M]

/-- Jointly measurable posterior success probability `P(B=1|U=u,M=m)`, using
the kernel-level nested conditional law rather than a parameterized family of
measure-level `condKernel`s. -/
noncomputable def nestedPosteriorBitOneProb
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (z : U × M) : ℝ :=
  (Kernel.condKernel (conditionalBinaryKernel ρ) z).real
    ({1} : Set (Fin 2))

lemma measurable_nestedPosteriorBitOneProb
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    Measurable (nestedPosteriorBitOneProb ρ) := by
  unfold nestedPosteriorBitOneProb
  exact ENNReal.measurable_toReal.comp
    ((Kernel.condKernel (conditionalBinaryKernel ρ)).measurable_coe
      (measurableSet_singleton 1))

/-- Jointly measurable posterior binary entropy at `(u,m)`. -/
noncomputable def nestedPosteriorBinaryEntropy
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (z : U × M) : ℝ :=
  Real.binEntropy (nestedPosteriorBitOneProb ρ z)

lemma measurable_nestedPosteriorBinaryEntropy
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    Measurable (nestedPosteriorBinaryEntropy ρ) := by
  unfold nestedPosteriorBinaryEntropy
  exact Real.binEntropy_continuous.measurable.comp
    (measurable_nestedPosteriorBitOneProb ρ)

lemma nestedPosteriorBinaryEntropy_nonneg
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (z : U × M) :
    0 ≤ nestedPosteriorBinaryEntropy ρ z := by
  unfold nestedPosteriorBinaryEntropy nestedPosteriorBitOneProb
  exact Real.binEntropy_nonneg measureReal_nonneg measureReal_le_one

lemma nestedPosteriorBinaryEntropy_le_log_two
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (z : U × M) :
    nestedPosteriorBinaryEntropy ρ z ≤ Real.log 2 := by
  unfold nestedPosteriorBinaryEntropy
  exact Real.binEntropy_le_log_two

/-- The globally measurable posterior entropy, integrated over the true
`(U,M)` composition-product marginal, is integrable. -/
theorem integrable_nestedPosteriorBinaryEntropy
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    Integrable (nestedPosteriorBinaryEntropy ρ)
      (ρ.fst ⊗ₘ (conditionalBinaryKernel ρ).fst) := by
  have hmeas := measurable_nestedPosteriorBinaryEntropy ρ
  refine Integrable.mono' (integrable_const (Real.log 2))
    hmeas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun z => ?_
  have hnonneg := nestedPosteriorBinaryEntropy_nonneg ρ z
  have hle := nestedPosteriorBinaryEntropy_le_log_two ρ z
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hlog] using hle

/-- Posterior entropy inside a fixed `U=u` fiber, expressed using the globally
measurable nested conditional kernel. -/
noncomputable def conditionalBinaryPosteriorEntropyFiber
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) : ℝ :=
  ∫ m, nestedPosteriorBinaryEntropy ρ (u, m)
    ∂(conditionalBinaryKernel ρ).fst u

lemma stronglyMeasurable_conditionalBinaryPosteriorEntropyFiber
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    StronglyMeasurable (conditionalBinaryPosteriorEntropyFiber ρ) := by
  unfold conditionalBinaryPosteriorEntropyFiber
  exact (measurable_nestedPosteriorBinaryEntropy ρ).stronglyMeasurable.integral_kernel_prod_right'

/-- At each fixed `u`, the globally measurable nested posterior entropy agrees
almost everywhere with the entropy obtained from the ordinary conditional
kernel of the fiber law `P(M,B|U=u)`. -/
theorem nestedPosteriorBinaryEntropy_ae_eq_fiberPosteriorEntropy
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) :
    (fun m => nestedPosteriorBinaryEntropy ρ (u, m))
      =ᵐ[(conditionalBinaryKernel ρ).fst u]
        fun m => Real.binEntropy
          (posteriorBitOneProb (conditionalBinaryKernel ρ u) m) := by
  filter_upwards [kernelCondKernel_ae_eq_fiberCondKernel ρ u] with m hm
  unfold nestedPosteriorBinaryEntropy nestedPosteriorBitOneProb posteriorBitOneProb
  rw [hm]

/-- Therefore the fiber posterior entropy can be evaluated using the ordinary
measure-level conditional kernel required by the unconditional binary MI
identity. -/
theorem conditionalBinaryPosteriorEntropyFiber_eq_fiberPosteriorIntegral
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (u : U) :
    conditionalBinaryPosteriorEntropyFiber ρ u =
      ∫ m, Real.binEntropy
        (posteriorBitOneProb (conditionalBinaryKernel ρ u) m)
        ∂(conditionalBinaryKernel ρ).fst u := by
  unfold conditionalBinaryPosteriorEntropyFiber
  exact integral_congr_ae
    (nestedPosteriorBinaryEntropy_ae_eq_fiberPosteriorEntropy ρ u)

/-- The source quantity `H(B|M,U)` is the `U`-average of the fixed-`u`
posterior entropies.  This is the Fubini bridge needed to lift the
unconditional binary MI identity to conditional mutual information. -/
theorem conditionalBinaryEntropyGivenUM_eq_integral_posteriorEntropyFiber
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    conditionalBinaryEntropyGivenUM ρ =
      ∫ u, conditionalBinaryPosteriorEntropyFiber ρ u ∂ρ.fst := by
  letI : Nonempty U := ⟨(nonempty_of_isProbabilityMeasure ρ).some.1⟩
  have hpost := posteriorBitGivenUM_ae_eq_kernelCondKernel ρ
  rw [binaryUMJoint_fst_eq_compProd] at hpost
  have hglobal :
      conditionalBinaryEntropyGivenUM ρ =
        ∫ z, nestedPosteriorBinaryEntropy ρ z
          ∂(ρ.fst ⊗ₘ (conditionalBinaryKernel ρ).fst) := by
    unfold conditionalBinaryEntropyGivenUM posteriorBitGivenUM
    rw [posteriorConditionalEntropy_fin2_eq_binEntropy_integral
      (binaryUMJoint ρ)]
    rw [binaryUMJoint_fst_eq_compProd]
    apply integral_congr_ae
    filter_upwards [hpost] with z hz
    simp [posteriorBitOneProb, nestedPosteriorBinaryEntropy,
      nestedPosteriorBitOneProb, posteriorBitGivenUM, hz]
  rw [hglobal]
  exact Measure.integral_compProd (integrable_nestedPosteriorBinaryEntropy ρ)

end UEOT.V3.InformationConditionalBinaryEntropyLift
