import UEOT.V3.InformationKernelTV

/-!
# Zero average total variation implies equality of kernels

The zero-distortion step in P-INFO-03 begins with the source fact that a
nonnegative average total-variation distortion can vanish only when the two
predictive kernels coincide almost everywhere.  This module isolates that
measure-theoretic bridge using UEOT's canonical event-supremum `tvDist` and the
kernel-TV measurability theorem already validated for P-INFO-02.
-/

namespace UEOT.V3.InformationZeroTV

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.TotalVariation
open UEOT.V3.InformationKernelTV

universe uX uY

variable {X : Type uX} {Y : Type uY}
variable [MeasurableSpace X] [MeasurableSpace Y]

/-- For probability measures, zero UEOT total variation is equivalent to
measure equality. -/
theorem measure_eq_of_tvDist_eq_zero
    (μ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hzero : tvDist μ ν = 0) :
    μ = ν := by
  apply Measure.ext
  intro A hA
  have hle := tvEvent_le μ ν A hA
  rw [hzero] at hle
  have habs : |μ.real A - ν.real A| = 0 :=
    le_antisymm hle (abs_nonneg _)
  have hreal : μ.real A = ν.real A := by
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  exact (measureReal_eq_measureReal_iff).mp hreal

/-- Zero extended expectation of pointwise kernel TV forces equality of the
Markov kernels almost everywhere under the averaging measure.

Using `ENNReal.ofReal` is harmless here because `tvDist` is nonnegative.  This
form avoids introducing any extra integrability assumption at zero distortion. -/
theorem ae_kernel_eq_of_lintegral_tvDist_eq_zero
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure X)
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hzero :
      (∫⁻ x, ENNReal.ofReal (tvDist (κ x) (η x)) ∂μ) = 0) :
    κ =ᵐ[μ] η := by
  have hmeas :
      Measurable fun x => ENNReal.ofReal (tvDist (κ x) (η x)) :=
    (measurable_tvDist_kernel κ η).ennreal_ofReal
  have hae0 :
      (fun x => ENNReal.ofReal (tvDist (κ x) (η x))) =ᵐ[μ] 0 :=
    (lintegral_eq_zero_iff' hmeas.aemeasurable).mp hzero
  filter_upwards [hae0] with x hx
  have hle0 : tvDist (κ x) (η x) ≤ 0 := by
    apply ENNReal.ofReal_eq_zero.mp
    simpa using hx
  have htv0 : tvDist (κ x) (η x) = 0 :=
    le_antisymm hle0 (tvDist_nonneg (κ x) (η x))
  exact measure_eq_of_tvDist_eq_zero (κ x) (η x) htv0

end

end UEOT.V3.InformationZeroTV
