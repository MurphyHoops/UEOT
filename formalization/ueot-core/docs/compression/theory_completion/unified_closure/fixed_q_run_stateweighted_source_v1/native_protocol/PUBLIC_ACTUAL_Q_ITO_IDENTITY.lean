import UEOT
namespace ControlledItoIdentityIndependent
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralLiteralIntervals
open BrownianBoundedC2DynkinSource BrownianScalarItoSource BrownianIntegralTimeEnergy BrownianIntegralCrossVariation
open BrownianBoundedPredictableApproximation BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianOwnQTimeInput BrownianOwnQTargetIntegral BrownianOwnQTargetShift
open BrownianControlledTestInput BrownianControlledC2Source BrownianControlledItoIdentitySource
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
-- Fixed deployment is genuinely path-dependent/nonsmooth in its ORIGINALFs1.
-- Target g below does not replace this b, its Q or shifted noise.
def H (w : ℝ≥0→ℝ) : ℝ := if process (1/2) w≤process 1 w then 3/2 else -1/2
theorem H_past : StronglyMeasurable[naturalFiltration 1] H := by
  let : MeasurableSpace (ℝ≥0→ℝ) := naturalFiltration 1
  have h0 := (process_stronglyAdapted (1/2)).mono (naturalFiltration.mono (by norm_num : (1/2 : ℝ≥0)≤1))
  have hs : MeasurableSet {w : ℝ≥0→ℝ | process (1/2) w≤process 1 w} :=
    measurableSet_le h0.measurable (process_stronglyAdapted 1).measurable
  exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable
theorem H_bound (w : ℝ≥0→ℝ) : ‖H w‖≤3/2 := by unfold H; split_ifs <;> norm_num
theorem H_top : MemLp H ∞ sourceLaw :=
  MemLp.of_bound (H_past.mono (naturalFiltration.le 1)).aestronglyMeasurable (3/2) (ae_of_all _ H_bound)
def b : fullPredictableL2 2 := intervalInput 2 1 2 (by norm_num) le_rfl H H_past H_top
theorem b_bound : ∀ᵐ p ∂inputLaw 2, |(b : Lp ℝ 2 (inputLaw 2)) p|≤(3/2 : ℝ) := by
  filter_upwards [intervalInput_coe 2 1 2 (by norm_num) le_rfl H H_past H_top] with p hp
  change (b : Lp ℝ 2 (inputLaw 2)) p=intervalIntegrand H 1 2 p at hp
  rw [hp]
  unfold intervalIntegrand
  change |(Ioc (1 : ℝ) 2).indicator (fun _=>1) p.1*H p.2|≤3/2
  by_cases ht : p.1∈Ioc (1 : ℝ) 2
  · rw [Set.indicator_of_mem ht,one_mul]
    simpa only [Real.norm_eq_abs] using H_bound p.2
  · norm_num [Set.indicator_of_notMem ht]
private theorem cos_C2 : ContDiff ℝ 2 Real.cos := by fun_prop
private theorem cos_bound (x : ℝ) : ‖deriv Real.cos x‖≤(1 : ℝ) := by
  simpa only [Real.deriv_cos,Real.norm_eq_abs,abs_neg] using Real.abs_sin_le_one x
private theorem cos_bound2 (x : ℝ) : ‖iteratedDeriv 2 Real.cos x‖≤(1 : ℝ) := by
  simpa only [Real.norm_eq_abs] using Real.abs_iteratedDeriv_cos_le_one 2 x
private theorem cos_second : iteratedDeriv 2 Real.cos= -Real.cos := by
  simp

-- SAME previously constructed Q integrator, not remainder-as-definition.
def Qtest (U : ℝ≥0) : Lp ℝ 2 (fullLaw 2 b) :=
  testNoise 2 b (3/2) (by norm_num) b_bound U (-1) (-2) Real.cos cos_C2 1 (by norm_num) cos_bound
example (U : ℝ≥0) : Qtest U=
    BrownianOwnQHorizonTargetIntegral.targetIntegralQ 2 b (3/2) (by norm_num) b_bound U
      (testInput U (-1) (-2) Real.cos cos_C2 1 (by norm_num) cos_bound)
      (1*|(-2 : ℝ)|) (by positivity)
      (testInput_bound U (-1) (-2) Real.cos cos_C2 1 (by norm_num) cos_bound) := rfl
example (U : ℝ≥0) : (∫ w,Qtest U w ∂fullLaw 2 b)=0 :=
  testNoise_mean_zero 2 b (3/2) (by norm_num) b_bound U (-1) (-2) Real.cos cos_C2 1 (by norm_num) cos_bound

theorem generator_cos (x a : ℝ) : controlledGenerator (-2) Real.cos x a=2*a*Real.sin x-2*Real.cos x := by
  rw [controlledGenerator,Real.deriv_cos,cos_second]
  simp only [Pi.neg_apply]
  ring
-- Independent integration/read U includes both U<deployment2 and U>2,
-- preserving Q2b and the actual global masked action throughout.
theorem actual_cos_QI (U : ℝ≥0) : (fun w=>Real.cos (state (-1) (-2) U w))=ᵐ[fullLaw 2 b]
    fun w=>Real.cos (-1)+Qtest U w+
      ∫ t,2*control 2 b (3/2) t w*Real.sin (state (-1) (-2) t w)-
        2*Real.cos (state (-1) (-2) t w) ∂timeLaw U := by
  simpa [Qtest,generator_cos] using actual_ownQ_ito_at 2 b (3/2) (by norm_num) b_bound U (-1) (-2) Real.cos cos_C2
    1 1 (by norm_num) (by norm_num) cos_bound cos_bound2
example (U : ℝ≥0) :
    (fun w=>Real.cos (state (-1) (-2) U w)-Real.cos (-1)-
      ∫ t,2*control 2 b (3/2) t w*Real.sin (state (-1) (-2) t w)-
        2*Real.cos (state (-1) (-2) t w) ∂timeLaw U)=ᵐ[fullLaw 2 b] Qtest U := by
  simpa [Qtest,generator_cos] using actual_ito_remainder 2 b (3/2) (by norm_num) b_bound U (-1) (-2) Real.cos cos_C2
    1 1 (by norm_num) (by norm_num) cos_bound cos_bound2
example : Qtest 0=ᵐ[fullLaw 2 b] fun _=>0 := by
  filter_upwards [actual_cos_QI 0,state_initial 2 b (-1) (-2)] with w h hi
  norm_num only [NNReal.coe_zero] at h
  rw [hi] at h
  norm_num [timeLaw] at h
  exact h
example (U : ℝ≥0) : testNoise 2 b (3/2) (by norm_num) b_bound U (-1) 0 Real.cos cos_C2
    1 (by norm_num) cos_bound=ᵐ[fullLaw 2 b] fun _=>0 := by
  filter_upwards [actual_ownQ_ito_at 2 b (3/2) (by norm_num) b_bound U (-1) 0 Real.cos cos_C2
    1 1 (by norm_num) (by norm_num) cos_bound cos_bound2] with w h
  norm_num [state,controlledGenerator] at h
  exact h
#print axioms testNoise
#print axioms testNoise_mean_zero
#print axioms test_cross_eq_firstDrift
#print axioms secondEnergy_eq_raw
#print axioms actual_ownQ_ito_at
#print axioms actual_ito_remainder
#print axioms actual_cos_QI
end
end ControlledItoIdentityIndependent
