import UEOT
namespace IndependentIdentityReused0
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianGaussianTiltSource
open scoped NNReal Topology ProbabilityTheory MeasureTheory
#check gaussian_exponential_tilt
#check terminal_hasLaw_tilted
#print axioms gaussian_exponential_tilt
#print axioms terminal_hasLaw_tilted
#print axioms shifted_terminal_second_moment
#print axioms tiltedLaw_zero
example : HasLaw (process 1) (gaussianReal 2 1) (tiltedLaw 2 1) := by
  simpa only [NNReal.coe_one,mul_one] using terminal_hasLaw_tilted 2 1
example : (∫ ω, process 1 ω ∂tiltedLaw 2 1)=2 := by simpa using tilted_terminal_mean 2 1
example : (∫ ω, process 1 ω-2 ∂tiltedLaw 2 1)=0 := by simpa using shifted_terminal_mean 2 1
example : (∫ ω, (process 1 ω-2)^2 ∂tiltedLaw 2 1)=1 := by simpa using shifted_terminal_second_moment 2 1
example (u : ℝ) : tiltedLaw u 0=sourceLaw := tiltedLaw_zero u
example (T : ℝ≥0) : tiltedLaw 0 T=sourceLaw := tiltedLaw_zero_control T
example (u : ℝ) : (gaussianReal 0 0).withDensity (gaussianTiltWeight u 0)=Measure.dirac 0 := by
  simpa using gaussian_exponential_tilt u 0
example (ω : ℝ≥0 → ℝ) : 2*process 1 ω=2*(process 1 ω-2)+4 := by
  simpa only [NNReal.coe_one,mul_one,show (2 : ℝ)^2=4 by norm_num] using constant_terminal_integral_shift 2 1 ω
end IndependentIdentityReused0

namespace IndependentIdentityReused1
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open BrownianGaussianTiltSource BrownianFiniteGaussianTiltSource
open scoped NNReal Topology ProbabilityTheory MeasureTheory
#check shiftedProcess_isBrownian
#check shifted_indep_original_past
#check shiftedProcess_martingale
#print axioms residual_indep_terminal
#print axioms shifted_finite_map
#print axioms shiftedProcess_isBrownian
#print axioms shifted_indep_original_past
#print axioms shiftedProcess_martingale
example : IsBrownianReal (shiftedProcess 2 1) (tiltedLaw 2 1) := shiftedProcess_isBrownian 2 1
example : HasLaw (fun ω => ({0,1,2} : Finset ℝ≥0).restrict (shiftedProcess 2 1 · ω))
    (BrownianReal.projectiveFamily {0,1,2}) (tiltedLaw 2 1) :=
  (shiftedProcess_isPreBrownian 2 1).hasLaw {0,1,2}
example : HasLaw (shiftedProcess 2 1 2) (gaussianReal 0 2) (tiltedLaw 2 1) :=
  (shiftedProcess_isPreBrownian 2 1).hasLaw_eval 2
example (ω : ℝ≥0 → ℝ) : shiftedProcess 2 1 2 ω=process 2 ω-2 := by
  simpa only [NNReal.coe_one,mul_one] using shiftedProcess_after 2 1 2 (by norm_num) ω
example : IndepFun (shiftedIncrement 2 1 1 2) (fun ω (r : Iic (1 : ℝ≥0)) => process r ω) (tiltedLaw 2 1) :=
  shiftedIncrement_indep_original_past 2 1 1 2 (by norm_num)
example : Martingale (shiftedProcess 2 1) naturalFiltration (tiltedLaw 2 1) := shiftedProcess_martingale 2 1
example : IsBrownianReal (shiftedProcess 2 0) (tiltedLaw 2 0) := shiftedProcess_isBrownian 2 0
example : IsBrownianReal (shiftedProcess 0 1) (tiltedLaw 0 1) := shiftedProcess_isBrownian 0 1
/-- The finite density horizon lies strictly inside this actual increment. -/
example : HasLaw (shiftedProcess 2 (3/2) 2-shiftedProcess 2 (3/2) 1) (gaussianReal 0 1) (tiltedLaw 2 (3/2)) := by
  convert (shiftedProcess_isPreBrownian 2 (3/2)).hasLaw_sub 2 1 using 1
  congr 1
  apply NNReal.coe_injective
  norm_num [coe_nndist,Real.dist_eq]
end IndependentIdentityReused1

namespace IndependentIdentityReused2
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
end IndependentIdentityReused2

namespace IndependentSameMeasureAndHorizon
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianGaussianTiltSource
open BrownianFiniteGaussianTiltSource BrownianConstantGirsanovSource
open scoped NNReal Topology ProbabilityTheory MeasureTheory ENNReal
noncomputable section
-- The original RN theorem is exactly the SAME density and measure used by source record.
example (u : ℝ) (T : ℝ≥0) :
    (tiltedLaw u T).rnDeriv sourceLaw =ᵐ[tiltedLaw u T]
      fun ω => ENNReal.ofReal (exponentialProcess u T ω) :=
  (actualTerminalData u T).rnDeriv_eq_density
example (u : ℝ) (T : ℝ≥0) :
    (actualTerminalData u T).density = fun ω => ENNReal.ofReal (exponentialProcess u T ω) := rfl
example (u : ℝ) (T : ℝ≥0) :
    (actualTerminalData u T).changeOfMeasure = (rfl : tiltedLaw u T=sourceLaw.withDensity (fun ω => ENNReal.ofReal (exponentialProcess u T ω))) := rfl
-- Original Ft is retained, even for increments crossing the terminal density horizon.
example : (tiltedLaw 2 (3/2))[shiftedIncrement 2 (3/2) 1 2 | naturalFiltration 1]
    =ᵐ[tiltedLaw 2 (3/2)] fun _ => 0 := condExp_shiftedIncrement 2 (3/2) 1 2 (by norm_num)
example (ω : ℝ≥0 → ℝ) : shiftedIncrement 2 (3/2 : ℝ≥0) 1 2 ω = process 2 ω-process 1 ω-1 := by
  have hl : (1 : ℝ≥0) ≤ 3/2 := by exact_mod_cast (by norm_num : (1 : ℝ) ≤ 3/2)
  have hr : (3/2 : ℝ≥0) ≤ 2 := by exact_mod_cast (by norm_num : (3/2 : ℝ) ≤ 2)
  unfold shiftedIncrement
  rw [shiftedProcess_after 2 (3/2) 2 hr,shiftedProcess_before 2 (3/2) 1 hl]
  norm_num
  ring
-- Clipping is substantive: replacing W2 by B2-2*2 afterT1 gives nonzero mean.
theorem unclipped_after_horizon_not_centered : (∫ ω, (process 2 ω-4) ∂tiltedLaw 2 1) = -2 := by
  have hW := (shiftedProcess_isPreBrownian 2 1).integral_eval 2
  have hi := ((shiftedProcess_isPreBrownian 2 1).integrable_eval 2).sub (integrable_const (2 : ℝ))
  have he : (fun ω => process 2 ω-4) = fun ω => shiftedProcess 2 1 2 ω-2 := by
    funext ω
    rw [shiftedProcess_after 2 1 2 (by norm_num)]
    norm_num
    ring
  rw [he,integral_sub ((shiftedProcess_isPreBrownian 2 1).integrable_eval 2) (integrable_const _),hW,integral_const]
  simp
-- Signed control and original p_kl_05, not only positive-control normalization.
example : klDiv (tiltedLaw (-2) 1) sourceLaw=2 := by
  convert actual_fullSpaceKL (-2) 1 using 1
  norm_num
example (u : ℝ) (T : ℝ≥0) :
    (actualTerminalData u T).controlledFiltration 0=naturalFiltration 0 := rfl
example (u : ℝ) (T : ℝ≥0) :
    (actualTerminalData u T).controlledFiltration 1=naturalFiltration T := rfl
#print axioms unclipped_after_horizon_not_centered
end
end IndependentSameMeasureAndHorizon
