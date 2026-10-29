import UEOT

namespace ReusedFrozenAuthorConsumer0
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology MeasureTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianIntegralCrossVariation BrownianPredictableInputs BrownianIntegralContinuousVersion
open BrownianProjectiveSource BrownianQuadraticVariation
#check crossEnergyClass_coe
#check fullInput_partition_crossVariation
#check fullInput_partition_crossVariation_inMeasure
#print axioms productClass_polarization
#print axioms crossEnergyClass_coe
#print axioms gridCross_coe
#print axioms fullInput_partition_crossVariation
#print axioms fullInput_partition_crossVariation_inMeasure
example (T : ℝ≥0) (f g : fullPredictableL2 T) :
    TendstoInMeasure sourceLaw (fun n ω => ∑ i : Fin (n+1),
      (continuousIntegralProcess T f (uniformClock T n i.succ) ω-
        continuousIntegralProcess T f (uniformClock T n i.castSucc) ω)*
      (continuousIntegralProcess T g (uniformClock T n i.succ) ω-
        continuousIntegralProcess T g (uniformClock T n i.castSucc) ω)) atTop (crossTimeEnergy T f g T) :=
  fullInput_partition_crossVariation_inMeasure T (fun n => n+1) (uniformClock T)
    (uniformClock_mono T) (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T) f g
end ReusedFrozenAuthorConsumer0

namespace ReusedFrozenAuthorConsumer1
open MeasureTheory ProbabilityTheory
open scoped NNReal MeasureTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianPredictableInputs BrownianMartingaleSource
open BrownianIntegralProductCompensator
#check continuousIntegralProcess_add_ae
#check crossTimeEnergy_stronglyAdapted
#check compensatedProduct_martingale
#print axioms continuousIntegralProcess_add_ae
#print axioms crossEnergyIntegrand_stronglyMeasurable_past
#print axioms crossTimeEnergy_polarization
#print axioms compensatedProduct_martingale
example (T : ℝ≥0) (f g : fullPredictableL2 T) :
    Martingale (compensatedProduct T f g) naturalFiltration sourceLaw :=
  compensatedProduct_martingale T f g
example (f g : fullPredictableL2 0) :
    Martingale (compensatedProduct 0 f g) naturalFiltration sourceLaw :=
  compensatedProduct_martingale 0 f g
end ReusedFrozenAuthorConsumer1

namespace ReusedFrozenAuthorConsumer2
open MeasureTheory ProbabilityTheory
open scoped NNReal MeasureTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianPredictableInputs BrownianMartingaleSource
open BrownianPredictableMultiplier BrownianIntegralContinuousVersion
#check continuousMultiplier_coe
#check functionOfIntegralInput_coe
#print axioms inputMultiplier_coe
#print axioms inputMultiplier_norm_le
#print axioms continuousMultiplier
#print axioms functionOfIntegralInput_coe
#print axioms functionOfIntegralInput_martingale
example (T : ℝ≥0) (f : fullPredictableL2 T) :
    Martingale (continuousIntegralProcess T (functionOfIntegralInput T f Real.sin
      Real.continuous_sin 1 (by norm_num) (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)))
      naturalFiltration sourceLaw := functionOfIntegralInput_martingale T f Real.sin
      Real.continuous_sin 1 (by norm_num) (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)
end ReusedFrozenAuthorConsumer2

namespace ReusedFrozenAuthorConsumer3
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianBoundedMultiplierLimit
#check boundedMultiplier_tendsto
#check boundedMultipliedIntegral_tendsto
#print axioms boundedCoefficient_memLp
#print axioms boundedMultiplier_tendsto
#print axioms boundedMultipliedIntegral_tendsto
end ReusedFrozenAuthorConsumer3

namespace ReusedFrozenAuthorConsumer4
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianLeftMultiplierInputs
#check recordCoefficient_predictable
#check sampledMultiplier_tendsto
#check sampledMultipliedIntegral_tendsto
#print axioms recordCoefficient_bound
#print axioms sampledMultiplier_tendsto
#print axioms sampledMultipliedIntegral_tendsto
end ReusedFrozenAuthorConsumer4

namespace ReusedFrozenAuthorConsumer5
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianSimplePastMultiplier
#check simplePastInput_coe
#check simplePastInput_integral_coe
#print axioms simplePastInput_coe
#print axioms simplePastInput_integral_coe
end ReusedFrozenAuthorConsumer5

namespace ReusedFrozenAuthorConsumer6
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal MeasureTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianMartingaleSource BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralContinuousVersion BrownianBoundedPastMultiplier
#check windowMultiplier_integral_coe
#print axioms pastApprox_bound
#print axioms windowMultiplier_approx_tendsto
#print axioms ambientPastApprox_fiber
#print axioms windowMultiplier_integral_coe
example (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (f : fullPredictableL2 T) :
    (predictableIntegral T (windowMultiplier T s t hst htT (fun _ => (1 : ℝ)) stronglyMeasurable_const
      1 (by norm_num) (fun _ => by norm_num) f) : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw]
      fun ω => continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω := by
  simpa only [one_mul] using windowMultiplier_integral_coe T s t hst htT (fun _ => (1 : ℝ))
    stronglyMeasurable_const 1 (by norm_num) (fun _ => by norm_num) f
end ReusedFrozenAuthorConsumer6

namespace ReusedFrozenAuthorConsumer7
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology MeasureTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianPredictableInputs BrownianQuadraticVariation
open BrownianWeightedIncrementBinding BrownianPredictableMultiplier BrownianIntegralContinuousVersion
#check sampledMultiplier_integral_coe
#check weightedIncrementSum_tendstoInMeasure
#check functionOfIntegral_weightedIncrement_tendstoInMeasure
#print axioms sampledMultiplier_decomposition
#print axioms sampledMultiplier_integral_coe
#print axioms weightedIncrementSum_tendstoInMeasure
#print axioms functionOfIntegral_weightedIncrement_tendstoInMeasure
example (T : ℝ≥0) (f : fullPredictableL2 T) :
    TendstoInMeasure sourceLaw (fun n => weightedIncrementSum T (uniformClock T n)
      (fun u ω => Real.sin (continuousIntegralProcess T f u ω)) f) atTop
      (continuousIntegralProcess T (functionOfIntegralInput T f Real.sin Real.continuous_sin
        1 (by norm_num) (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)) T) :=
  functionOfIntegral_weightedIncrement_tendstoInMeasure T (fun n => n+1) (uniformClock T)
    (uniformClock_mono T) (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T)
    f Real.sin Real.continuous_sin 1 (by norm_num)
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)
end ReusedFrozenAuthorConsumer7

namespace ReusedFrozenAuthorConsumer8
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianSampledCellIncrement
#check sampled_cell_increment
#check gridCross_sampled_coe
#print axioms localize_sampled_cell
#print axioms sampled_cell_increment
#print axioms gridCross_sampled_coe
end ReusedFrozenAuthorConsumer8

namespace ReusedFrozenAuthorConsumer9
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianVaryingInputQV
#check partition_QV_of_input_tendsto
#check partition_crossVariation_of_input_tendsto
#print axioms partition_QV_of_input_tendsto
#print axioms partition_crossVariation_of_input_tendsto
end ReusedFrozenAuthorConsumer9

namespace ReusedFrozenAuthorConsumer10
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology MeasureTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianPredictableInputs BrownianQuadraticVariation BrownianIntegralContinuousVersion
open BrownianSampledCellIncrement BrownianIntegralWeightedQV
#check weighted_QV_class_tendsto
#check weighted_QV_tendstoInMeasure
#print axioms weightedTimeIntegrand_integrable
#print axioms crossEnergyClass_multiplied_eq_weighted
#print axioms weighted_QV_tendstoInMeasure
#print axioms functionOfIntegral_weighted_QV_tendstoInMeasure
example (T : ℝ≥0) (f : fullPredictableL2 T) :
    TendstoInMeasure sourceLaw (fun n => weightedSquareSum T (uniformClock T n)
      (fun u ω => Real.sin (continuousIntegralProcess T f u ω)) f) atTop
      (weightedTimeEnergy T (fun u ω => Real.sin (continuousIntegralProcess T f u ω)) f) :=
  functionOfIntegral_weighted_QV_tendstoInMeasure T (fun n => n+1) (uniformClock T)
    (uniformClock_mono T) (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T)
    f Real.sin Real.continuous_sin 1 (by norm_num)
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)
end ReusedFrozenAuthorConsumer10

namespace IndependentSameInputSelfPair
open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianPredictableInputs BrownianIntegralTimeTruncation
open BrownianIntegralCrossVariation BrownianIntegralSquareL1 BrownianIntegralEnergyL1
noncomputable section
example (T s : ℝ≥0) (f : fullPredictableL2 T) : crossEnergyClass T s f f = energyClass T s f := by
  unfold crossEnergyClass
  rw [energyClass_eq_marginal_square]
  congr 1
end
end IndependentSameInputSelfPair
