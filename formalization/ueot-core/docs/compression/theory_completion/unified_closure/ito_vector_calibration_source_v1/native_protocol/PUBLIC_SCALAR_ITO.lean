import UEOT

-- Public-root consumer of the actual source; retained original independent discriminator.
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianPredictableInputs BrownianIntegralContinuousVersion
open BrownianScalarItoSource
open scoped NNReal Topology MeasureTheory
#check actual_scalar_ito
#print axioms finite_taylor_telescope
#print axioms actual_scalar_ito
example (T : ℝ≥0) (f : fullPredictableL2 T) :
    (fun ω => Real.sin (continuousIntegralProcess T f T ω)) =ᵐ[sourceLaw] fun ω =>
      Real.sin 0+continuousIntegralProcess T (itoInput T f Real.sin (by fun_prop) 1 (by norm_num)
        (fun x => by simpa only [Real.deriv_sin,Real.norm_eq_abs] using Real.abs_cos_le_one x)) T ω+
      (1/2 : ℝ)*itoSecondEnergy T f Real.sin ω := by
  exact actual_scalar_ito T f Real.sin (by fun_prop) 1 1 (by norm_num) (by norm_num)
    (fun x => by simpa only [Real.deriv_sin,Real.norm_eq_abs] using Real.abs_cos_le_one x)
    (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_iteratedDeriv_sin_le_one 2 x)
open BrownianTimeIntegrand BrownianPredictableMultiplier BrownianIntegralWeightedQV
example (T : ℝ≥0) (f : fullPredictableL2 T) (ω : ℝ≥0 → ℝ) :
    itoSecondEnergy T f Real.sin ω =
      -weightedTimeEnergy T (fun u ω => Real.sin (continuousIntegralProcess T f u ω)) f ω := by
  have hd : iteratedDeriv 2 Real.sin = -Real.sin := by simpa using Real.iteratedDeriv_even_sin 1
  unfold itoSecondEnergy weightedTimeEnergy weightedTimeIntegrand
  simp only [hd,Pi.neg_apply,neg_mul,integral_neg]
example (T : ℝ≥0) (f : fullPredictableL2 T) :
    (itoInput T f Real.sin (by fun_prop) 1 (by norm_num)
      (fun x => by simpa only [Real.deriv_sin,Real.norm_eq_abs] using Real.abs_cos_le_one x) : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T]
      fun p => Real.cos (continuousIntegralProcess T f (Real.toNNReal p.1) p.2)*(f : Lp ℝ 2 (inputLaw T)) p := by
  simpa only [itoInput,Real.deriv_sin] using functionOfIntegralInput_coe T f (deriv Real.sin) (by simpa only [Real.deriv_sin] using Real.continuous_cos)
    1 (by norm_num) (fun x => by simpa only [Real.deriv_sin,Real.norm_eq_abs] using Real.abs_cos_le_one x)

namespace IndependentItoIdentityInput
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianPredictableInputs BrownianPredictableMultiplier BrownianScalarItoSource BrownianTimeIntegrand
open scoped NNReal
example (T : ℝ≥0) (f : fullPredictableL2 T) :
    (itoInput T f (fun x : ℝ => x) (by fun_prop) 1 (by norm_num) (by intro x; simp) : Lp ℝ 2 (inputLaw T))
      =ᵐ[inputLaw T] (f : Lp ℝ 2 (inputLaw T)) := by
  simpa only [itoInput,deriv_id'',one_mul] using
    functionOfIntegralInput_coe T f (deriv (fun x : ℝ => x)) (by simpa using continuous_const)
      1 (by norm_num) (by intro x; simp)
end IndependentItoIdentityInput
