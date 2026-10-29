import UEOT
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open BrownianFiniteGaussianTiltSource BrownianConstantGirsanovSource BrownianPredictableDensity
open scoped NNReal Topology ProbabilityTheory MeasureTheory ENNReal
noncomputable section
#check actualTerminalData
#check actual_p_kl_05
#check baseline_returns_actual_integral
#print axioms baseline_returns_actual_integral
#print axioms controlledIntegralProcess_martingale
#print axioms actualTerminalData
#print axioms actual_p_kl_05
example : UEOT.V3.GirsanovPathKL.TerminalGirsanovData sourceLaw (tiltedLaw 2 1) 1 (constantControl 2) :=
  actualTerminalData 2 1
example : klDiv (tiltedLaw 2 1) sourceLaw=2 := by
  convert actual_fullSpaceKL 2 1 using 1
  norm_num
example : klDiv (tiltedLaw 2 1) sourceLaw=2 ∧
    klDiv ((tiltedLaw 2 1).map (process 1)) (sourceLaw.map (process 1)) ≤ 2 := by
  convert actual_p_kl_05 2 1 (process 1) (measurable_process 1) using 1 <;> norm_num
example (u : ℝ) (T : ℝ≥0) :
    klDiv ((tiltedLaw u T).map (fun ω => fun t => process t ω))
      (sourceLaw.map (fun ω => fun t => process t ω)) ≤ ENNReal.ofReal ((1/2 : ℝ)*u^2*(T : ℝ)) :=
  actual_observedPathKL u T _ (measurable_pi_lambda _ measurable_process)
example (u : ℝ) : klDiv (tiltedLaw u 0) sourceLaw=0 := by
  simpa using actual_fullSpaceKL u 0
example (T : ℝ≥0) : klDiv (tiltedLaw 0 T) sourceLaw=0 := by
  simpa using actual_fullSpaceKL 0 T
example (ω : ℝ≥0 → ℝ) : UEOT.V3.GirsanovPathKL.controlEnergy 1 (constantControl 2) ω=4 := by
  simpa only [NNReal.coe_one,mul_one,show (2 : ℝ)^2=4 by norm_num] using constantControl_energy 2 1 ω
example (u : ℝ) (T : ℝ≥0) :
    (predictableIntegral T (baselineInput u T) : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw] baselineIntegral u T :=
  baseline_returns_actual_integral u T
example (u : ℝ) (T : ℝ≥0) :
    (actualTerminalData u T).controlledIntegralProcess 0=0 := (actualTerminalData u T).controlledIntegral_initial
example : IsBrownianReal (shiftedProcess 2 1) (tiltedLaw 2 1) := shiftedProcess_isBrownian 2 1

end

-- The finite density horizon is inside this source increment. Clipped drift
-- beyond T and ENTIRE ORIGINAL past independence are actual consumers.
example : HasLaw (shiftedProcess 2 (3/2) 2-shiftedProcess 2 (3/2) 1)
    (gaussianReal 0 1) (tiltedLaw 2 (3/2)) := by
  convert (shiftedProcess_isPreBrownian 2 (3/2)).hasLaw_sub 2 1 using 1
  congr 1
  apply NNReal.coe_injective
  norm_num [coe_nndist,Real.dist_eq]
example : IndepFun (shiftedIncrement 2 1 1 2)
    (fun ω (r : Iic (1 : ℝ≥0)) => process r ω) (tiltedLaw 2 1) :=
  shiftedIncrement_indep_original_past 2 1 1 2 (by norm_num)
example (ω : ℝ≥0 → ℝ) : shiftedProcess 2 1 2 ω=process 2 ω-2 := by
  simpa only [NNReal.coe_one,mul_one] using shiftedProcess_after 2 1 2 (by norm_num) ω
