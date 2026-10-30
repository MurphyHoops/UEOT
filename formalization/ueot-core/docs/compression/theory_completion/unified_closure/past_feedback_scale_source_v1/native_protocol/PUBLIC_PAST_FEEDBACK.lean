import UEOT
namespace IdentityReusedAuthorCheck0
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianPastStepGaussianResidualSource
open scoped NNReal Topology ProbabilityTheory MeasureTheory
#check residual_coefficient_indep_increment
#print axioms residual_increment_covariance
#print axioms residual_coefficient_indep_increment
example (I : Finset ℝ≥0) :
    IndepFun (fun ω => (residualVector 1 2 I ω,Real.sin (process 1 ω))) (increment 1 2) sourceLaw :=
  residual_coefficient_indep_increment (fun ω => Real.sin (process 1 ω)) 1 2 (by norm_num)
    (Real.continuous_sin.comp_stronglyMeasurable (process_stronglyAdapted 1)) I
example : IndepFun (fun ω => (residualVector 1 2 ({0,1,3/2,2,3} : Finset ℝ≥0) ω,Real.sin (process 1 ω)))
    (increment 1 2) sourceLaw :=
  residual_coefficient_indep_increment (fun ω => Real.sin (process 1 ω)) 1 2 (by norm_num)
    (Real.continuous_sin.comp_stronglyMeasurable (process_stronglyAdapted 1)) {0,1,3/2,2,3}
example : overlap 1 2 (1/2)=0 := by norm_num [overlap]
example : overlap 1 2 3=1 := by norm_num [overlap]
example : cov[residual 1 2 3,increment 1 2;sourceLaw]=0 := residual_increment_covariance 1 2 3 (by norm_num)
example : cov[residual 1 2 (3/2),increment 1 2;sourceLaw]=0 := residual_increment_covariance 1 2 (3/2) (by norm_num)
example : cov[residual 1 2 0,increment 1 2;sourceLaw]=0 := residual_increment_covariance 1 2 0 (by norm_num)
end IdentityReusedAuthorCheck0
namespace IdentityReusedAuthorCheck1
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open BrownianPastStepExponentialSource BrownianPastStepGaussianResidualSource BrownianPastStepShiftedSource
open scoped NNReal Topology ProbabilityTheory MeasureTheory
#check shiftedProcess_isBrownian
#check shiftedNatural_eq_original
#print axioms shifted_finite_map
#print axioms shiftedProcess_isBrownian
#print axioms shiftedNatural_eq_original
#print axioms shifted_indep_original_past
#print axioms shiftedProcess_martingale
private noncomputable def feedback (ω : ℝ≥0 → ℝ) : ℝ := Real.sin (process 1 ω)
private theorem feedback_past : StronglyMeasurable[naturalFiltration 1] feedback :=
  Real.continuous_sin.comp_stronglyMeasurable (process_stronglyAdapted 1)
example : IsBrownianReal (shiftedProcess feedback 1 2) (stepLaw feedback 1 2) :=
  shiftedProcess_isBrownian feedback 1 2 (by norm_num) feedback_past
example : HasLaw (fun ω => ({0,1/2,1,3/2,2,3} : Finset ℝ≥0).restrict (shiftedProcess feedback 1 2 · ω))
    (BrownianReal.projectiveFamily {0,1/2,1,3/2,2,3}) (stepLaw feedback 1 2) :=
  (shiftedProcess_isPreBrownian feedback 1 2 (by norm_num) feedback_past).hasLaw _
example : shiftedNatural feedback 1 2 feedback_past=naturalFiltration :=
  shiftedNatural_eq_original feedback 1 2 (by norm_num) feedback_past
example : Martingale (shiftedProcess feedback 1 2) naturalFiltration (stepLaw feedback 1 2) :=
  shiftedProcess_martingale feedback 1 2 (by norm_num) feedback_past
example (ω : ℝ≥0 → ℝ) : shiftedProcess feedback 1 2 (1/2) ω=process (1/2) ω :=
  shiftedProcess_before feedback 1 2 (1/2) (by norm_num) (by norm_num) ω
example (ω : ℝ≥0 → ℝ) : shiftedProcess feedback 1 2 3 ω=process 3 ω-feedback ω := by
  convert shiftedProcess_after feedback 1 2 3 (by norm_num) (by norm_num) ω using 1; norm_num
example : HasLaw (shiftedProcess feedback 1 2 3) (gaussianReal 0 3) (stepLaw feedback 1 2) :=
  (shiftedProcess_isPreBrownian feedback 1 2 (by norm_num) feedback_past).hasLaw_eval 3
example : IndepFun (shiftedIncrement feedback 1 2 2 3)
    (fun ω (r : Iic (2 : ℝ≥0)) => process r ω) (stepLaw feedback 1 2) :=
  shiftedIncrement_indep_original_past feedback 1 2 (by norm_num) feedback_past 2 3 (by norm_num)
example : IsBrownianReal (shiftedProcess feedback 1 1) (stepLaw feedback 1 1) :=
  shiftedProcess_isBrownian feedback 1 1 le_rfl feedback_past
end IdentityReusedAuthorCheck1
namespace IdentityReusedAuthorCheck2
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open BrownianPastStepExponentialSource BrownianPastStepShiftedSource BrownianPastStepGirsanovSource BrownianPredictableDensity
open scoped NNReal Topology ProbabilityTheory MeasureTheory ENNReal
noncomputable section
#check actualTerminalData
#check actual_p_kl_05
#print axioms baseline_returns_actual_integral
#print axioms stepControl_progressive
#print axioms terminalIntegral_martingale
#print axioms actualTerminalData
#print axioms actual_p_kl_05
private def feedback (ω : ℝ≥0 → ℝ) : ℝ := 1+(1/2)*Real.sin (process 1 ω)
private theorem feedback_past : StronglyMeasurable[naturalFiltration 1] feedback := by
  have hc : Continuous (fun x : ℝ => 1+(1/2)*Real.sin x) := by fun_prop
  exact hc.comp_stronglyMeasurable (process_stronglyAdapted 1)
private theorem feedback_interval (ω : ℝ≥0 → ℝ) : (1/2 : ℝ) ≤ feedback ω ∧ feedback ω ≤ 3/2 := by
  have hl := Real.neg_one_le_sin (process 1 ω)
  have hh := Real.sin_le_one (process 1 ω)
  unfold feedback
  constructor <;> linarith
private theorem feedback_bound (ω : ℝ≥0 → ℝ) : ‖feedback ω‖ ≤ 3/2 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [(feedback_interval ω).1])]
  exact (feedback_interval ω).2
private theorem feedback_top : MemLp feedback ∞ sourceLaw :=
  MemLp.of_bound (feedback_past.mono (naturalFiltration.le 1)).aestronglyMeasurable (3/2) (Eventually.of_forall feedback_bound)
example : UEOT.V3.GirsanovPathKL.TerminalGirsanovData sourceLaw (stepLaw feedback 1 2) 2 (stepControl feedback 1 2) :=
  actualTerminalData feedback 1 2 (by norm_num) feedback_past feedback_top
example : klDiv (stepLaw feedback 1 2) sourceLaw =
    ENNReal.ofReal ((1/2 : ℝ)*(∫ ω, feedback ω^2 ∂sourceLaw)*((2 : ℝ≥0)-(1 : ℝ≥0) : ℝ≥0)) ∧
    klDiv ((stepLaw feedback 1 2).map (process 2)) (sourceLaw.map (process 2)) ≤
      ENNReal.ofReal ((1/2 : ℝ)*(∫ ω, feedback ω^2 ∂sourceLaw)*((2 : ℝ≥0)-(1 : ℝ≥0) : ℝ≥0)) := by
  convert actual_p_kl_05 feedback 1 2 (by norm_num) feedback_past feedback_top (process 2) (measurable_process 2) using 1 <;> norm_num
/-- Actual positive finite risk interval, proved from the SAME supplied
bounded START feedback and ORIGINAL P-KL consumer, without sampling. -/
example : ENNReal.ofReal (1/8 : ℝ) ≤ klDiv (stepLaw feedback 1 2) sourceLaw ∧
    klDiv (stepLaw feedback 1 2) sourceLaw ≤ ENNReal.ofReal (9/8 : ℝ) := by
  have hi := (feedback_top.mono_exponent (show (2 : ℝ≥0∞) ≤ ∞ from le_top)).integrable_sq
  have hlo : (1/4 : ℝ) ≤ ∫ ω, feedback ω^2 ∂sourceLaw := by
    have h := integral_mono (integrable_const (μ := sourceLaw) (1/4 : ℝ)) hi (fun ω => by
      have hp := (feedback_interval ω).1
      nlinarith)
    simpa using h
  have hhi : (∫ ω, feedback ω^2 ∂sourceLaw) ≤ (9/4 : ℝ) := by
    have h := integral_mono hi (integrable_const (μ := sourceLaw) (9/4 : ℝ)) (fun ω => by
      have hp := feedback_interval ω
      nlinarith)
    simpa using h
  have hk := (actual_p_kl_05 feedback 1 2 (by norm_num) feedback_past feedback_top (process 2) (measurable_process 2)).1
  constructor
  · rw [hk]
    apply ENNReal.ofReal_le_ofReal
    norm_num
    linarith
  · rw [hk]
    apply ENNReal.ofReal_le_ofReal
    norm_num
    linarith
example : klDiv (stepLaw feedback 1 1) sourceLaw=0 := by
  simpa using (actual_p_kl_05 feedback 1 1 le_rfl feedback_past feedback_top (process 1) (measurable_process 1)).1
example : (predictableIntegral 2 (baselineInput feedback 1 2 (by norm_num) feedback_past feedback_top) : (ℝ≥0 → ℝ) → ℝ)
    =ᵐ[sourceLaw] baselineIntegral feedback 1 2 := baseline_returns_actual_integral feedback 1 2 (by norm_num) feedback_past feedback_top
example (ω : ℝ≥0 → ℝ) : stepControl feedback 1 2 (1/2) ω=0 := by norm_num [stepControl]
example : (actualTerminalData feedback 1 2 (by norm_num) feedback_past feedback_top).controlledIntegralProcess 0=0 :=
  (actualTerminalData feedback 1 2 (by norm_num) feedback_past feedback_top).controlledIntegral_initial
end
end IdentityReusedAuthorCheck2

namespace IndependentOriginalPastAndSameEnergy
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open BrownianPastStepExponentialSource BrownianPastStepTiltKernelSource
open BrownianPastStepGaussianResidualSource BrownianPastStepShiftedSource BrownianPastStepGirsanovSource
open scoped NNReal Topology ProbabilityTheory MeasureTheory ENNReal
noncomputable section

-- Full-law result requires START measurability, not an artificial boundedness premise.
example : IsBrownianReal (shiftedProcess (process 1) 1 2) (stepLaw (process 1) 1 2) :=
  shiftedProcess_isBrownian (process 1) 1 2 (by norm_num) (process_stronglyAdapted 1)
example : shiftedNatural (process 1) 1 2 (process_stronglyAdapted 1)=naturalFiltration :=
  shiftedNatural_eq_original (process 1) 1 2 (by norm_num) (process_stronglyAdapted 1)
example : IndepFun (shiftedIncrement (process 1) 1 2 (1/2) 3)
    (fun ω (r : Iic (1/2 : ℝ≥0)) => process r ω) (stepLaw (process 1) 1 2) :=
  shiftedIncrement_indep_original_past (process 1) 1 2 (by norm_num) (process_stronglyAdapted 1) (1/2) 3 (by exact_mod_cast (by norm_num : (1/2 : ℝ) ≤ 3))

-- Exact SAME original coefficient law is preserved, even without uniform bound.
example : (stepLaw (process 1) 1 2).map (process 1)=sourceLaw.map (process 1) :=
  stepLaw_map_coefficient (process 1) 1 2 (by norm_num) (process_stronglyAdapted 1)

-- Merely P-essentially-bounded generic H, not a pointwise bound or an independent Q bound.
example (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (htop : MemLp H ∞ sourceLaw) :
    (stepLaw H a b).rnDeriv sourceLaw =ᵐ[stepLaw H a b]
      fun ω => ENNReal.ofReal (stepExponential H a b ω) :=
  (actualTerminalData H a b hab hH htop).rnDeriv_eq_density
example (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (htop : MemLp H ∞ sourceLaw) :
    (actualTerminalData H a b hab hH htop).density =
      fun ω => ENNReal.ofReal (stepExponential H a b ω) := rfl
example (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (htop : MemLp H ∞ sourceLaw) :
    (actualTerminalData H a b hab hH htop).controlledFiltration 1=naturalFiltration b := rfl
example (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    (∫ ω, UEOT.V3.GirsanovPathKL.controlEnergy b (stepControl H a b) ω ∂stepLaw H a b)=
      (∫ ω, H ω^2 ∂sourceLaw)*((b : ℝ)-(a : ℝ)) := actual_energy_mean H a b hab hH

-- Original Fa rights are not exposed before START, even at negative real times.
example (H : (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) : stepControl H 1 2 (-2) ω=0 := by
  norm_num [stepControl]
example (H : (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) : shiftedProcess H 1 2 (3/2) ω=process (3/2) ω-H ω/2 := by
  unfold shiftedProcess overlap
  norm_num
  ring
example (H : (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) : controlledPath H 1 2 (1/2) ω=0 := by
  simp [controlledPath,BrownianCommonRefinement.clamp]
example (H : (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) : shiftedProcess H 1 2 3 ω=process 3 ω-H ω := by
  have h := shiftedProcess_after H 1 2 3 (by norm_num) (by norm_num) ω
  norm_num at h
  exact h
example (H : (ℝ≥0 → ℝ) → ℝ) (hH : StronglyMeasurable[naturalFiltration 0] H)
    (htop : MemLp H ∞ sourceLaw) : klDiv (stepLaw H 0 0) sourceLaw=0 := by
  simpa using (actual_p_kl_05 H 0 0 le_rfl hH htop (process 0) (measurable_process 0)).1
end
end IndependentOriginalPastAndSameEnergy
