import UEOT
namespace FixedQControlIndependent
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralLiteralIntervals
open BrownianBoundedC2DynkinSource BrownianScalarItoSource BrownianIntegralTimeEnergy BrownianIntegralCrossVariation
open BrownianBoundedPredictableApproximation BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianOwnQTimeInput BrownianBoundedControlReadout
open BrownianOwnQHorizonTargetIntegral BrownianOwnQHorizonTargetShift
open BrownianControlledTestInput BrownianControlledC2Source
open BrownianControlledHorizonTestInput BrownianControlledReadTimeSource BrownianControlledDynkinSource
open BrownianControlledDiscountSource BrownianControlledOccupationSource BrownianControlledInfiniteRewardSource
open BrownianControlledItoRunSource BrownianControlledHJBSource
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

-- The fixed density law Q2,b NEVER changes when integration/read U changes.
def test (U : ℝ≥0) : fullPredictableL2 U := testInput U (-1) (-2) Real.cos cos_C2 1 (by norm_num) cos_bound
theorem test_bound (U : ℝ≥0) : ∀ᵐ p ∂inputLaw U, |(test U : Lp ℝ 2 (inputLaw U)) p|≤(2 : ℝ) := by
  have h:=testInput_bound U (-1) (-2) Real.cos cos_C2 1 (by norm_num) cos_bound
  norm_num at h
  exact h
example (U : ℝ≥0) : targetIntegralQ 2 b (3/2) (by norm_num) b_bound U (test U) 2 (by norm_num) (test_bound U)
    =ᵐ[fullLaw 2 b] fun w=>(predictableIntegral U (test U) : (ℝ≥0→ℝ)→ℝ) w-
      crossTimeEnergy U (test U) (actualControlInput 2 b (3/2) (by norm_num) U) U w :=
  targetIntegralQ_eq_actual 2 b (3/2) (by norm_num) b_bound U (test U) 2 (by norm_num) (test_bound U)
example (U : ℝ≥0) : Integrable (predictableIntegral U (test U) : (ℝ≥0→ℝ)→ℝ) (fullLaw 2 b) :=
  target_baseline_integrable 2 b (3/2) (by norm_num) b_bound U (test U) 2 (by norm_num) (test_bound U)
theorem generator_cos (x a : ℝ) : controlledGenerator (-2) Real.cos x a=2*a*Real.sin x-2*Real.cos x := by
  rw [controlledGenerator,Real.deriv_cos,cos_second]
  simp only [Pi.neg_apply]
  ring
-- Includes U=3/2<A and U=3>A on the SAME law in a single theorem.
theorem actual_cos_all_read (U : ℝ≥0) :
    (∫ w, Real.cos (state (-1) (-2) U w) ∂fullLaw 2 b)=Real.cos (-1)+
      ∫ t,∫ w, 2*control 2 b (3/2) t w*Real.sin (state (-1) (-2) t w)-
        2*Real.cos (state (-1) (-2) t w) ∂fullLaw 2 b ∂timeLaw U := by
  simpa [generator_cos] using actual_controlled_expectation_at 2 b (3/2) (by norm_num) b_bound U (-1) (-2)
    Real.cos cos_C2 1 1 (by norm_num) (by norm_num) cos_bound cos_bound2
example : (∫ w,Real.cos (state (-1) (-2) 0 w) ∂fullLaw 2 b)=Real.cos (-1) := by
  simpa [timeLaw] using actual_cos_all_read 0
example (U : ℝ≥0) : (∫ w,Real.cos (state (-1) 0 U w) ∂fullLaw 2 b)=Real.cos (-1) := by
  simpa [controlledGenerator] using actual_controlled_expectation_at 2 b (3/2) (by norm_num) b_bound U (-1) 0
    Real.cos cos_C2 1 1 (by norm_num) (by norm_num) cos_bound cos_bound2
example : UEOT.V3.RecoveryDynkin.DynkinExpectationCertificate (expectedTest 2 b (-1) (-2) Real.cos)
    (expectedGenerator 2 b (3/2) (-1) (-2) Real.cos) 3 :=
  actual_controlled_dynkin 2 b (3/2) (by norm_num) b_bound (-1) (-2) Real.cos cos_C2 1 1
    (by norm_num) (by norm_num) cos_bound cos_bound2 3 (by norm_num)
example : UEOT.V3.RecoveryDynkin.DynkinExpectationCertificate (expectedTest 2 b (-1) (-2) Real.cos)
    (expectedGenerator 2 b (3/2) (-1) (-2) Real.cos) 0 :=
  actual_controlled_dynkin 2 b (3/2) (by norm_num) b_bound (-1) (-2) Real.cos cos_C2 1 1
    (by norm_num) (by norm_num) cos_bound cos_bound2 0 le_rfl
example (U : ℝ≥0) : discount 2 U*(∫ w,Real.cos (state (-1) (-2) U w) ∂fullLaw 2 b)=Real.cos (-1)+
    ∫ t,discount 2 t*(∫ w,controlledGenerator (-2) Real.cos (state (-1) (-2) t w) (control 2 b (3/2) t w)-
      2*Real.cos (state (-1) (-2) t w) ∂fullLaw 2 b) ∂timeLaw U :=
  actual_discounted_expectation 2 b (3/2) (by norm_num) b_bound (-1) (-2) Real.cos cos_C2 1 1
    (by norm_num) (by norm_num) cos_bound cos_bound2 2 U
example (U : ℝ≥0) : IsProbabilityMeasure (terminalLaw 2 b (-1) (-2) U) :=
  terminalLaw_probability 2 b (3/2) (by norm_num) b_bound (-1) (-2) U
example (U : ℝ≥0) : IsFiniteMeasure (occupation 2 b (3/2) (-1) (-2) 2 U) := by
  let _:=discountedInputLaw_finite 2 b (3/2) (by norm_num) b_bound 2 (by norm_num) U
  unfold occupation
  infer_instance
example : occupation 2 b (3/2) (-1) (-2) 2 0=0 := by
  simp [occupation,discountedInputLaw,BrownianOwnQTimeInput.inputLawQ,timeLaw]
theorem cos_read_bound (p : ℝ×(ℝ≥0→ℝ)) : ‖Real.cos (jointReadout 2 b (3/2) (-1) (-2) p).1‖≤(1 : ℝ) := Real.abs_cos_le_one _
example : Tendsto (fun n : ℕ=>∫ z,Real.cos z.1 ∂occupation 2 b (3/2) (-1) (-2) 2 (n : ℝ≥0)) atTop
    (𝓝 (infiniteReward 2 b (3/2) (-1) (-2) 2 (fun z=>Real.cos z.1))) :=
  actual_reward_tendsto 2 b (3/2) (by norm_num) b_bound (-1) (-2) 2 (by norm_num) (fun z=>Real.cos z.1)
    (by fun_prop) 1 cos_read_bound
example : Integrable (fun p=>discount 2 p.1*Real.cos (jointReadout 2 b (3/2) (-1) (-2) p).1) (infiniteInputLaw 2 b) :=
  reward_integrable_infinite 2 b (3/2) (by norm_num) b_bound (-1) (-2) 2 (by norm_num) (fun z=>Real.cos z.1)
    (by fun_prop) 1 cos_read_bound
-- Exact nonzero infinite reward from actual fixed-Q normalization and true tail.
example : infiniteReward 2 b (3/2) (-1) (-2) 2 (fun _=>1)=1/2 := by
  let _:=fullLaw_probability 2 b (3/2) (by norm_num) b_bound
  rw [infiniteReward_eq_time 2 b (3/2) (by norm_num) b_bound (-1) (-2) 2 (by norm_num) (fun _=>1) measurable_const 1 (fun _=>by norm_num)]
  simp only [integral_const,probReal_univ,one_smul,mul_one,discount]
  rw [integral_Ici_eq_integral_Ioi]
  have h:=integral_exp_mul_Ioi (a:=(-2 : ℝ)) (by norm_num) 0
  norm_num at h
  simpa only [neg_mul] using h

-- Original p_ctl_03 common consumer uses its declared sigma2/rho1/model,
-- with this different genuine nonsmooth b, SAME run returned by actualItoRun.
def actualPolicy : Policy (3/2) := ⟨2,b,b_bound⟩
example : (run (3/2) (by norm_num) actualPolicy (-1)).occupation 3=
    occupation 2 b (3/2) (-1) 2 1 3 := rfl
example : (run (3/2) (by norm_num) actualPolicy (-1)).terminalLaw (3/2)=
    terminalLaw 2 b (-1) 2 (3/2) := rfl
example : (run (3/2) (by norm_num) actualPolicy (-1)).infiniteReward=
    infiniteReward 2 b (3/2) (-1) 2 1 (fun z=>model.reward z.1 z.2) := rfl
example : (run (3/2) (by norm_num) actualPolicy (-1)).infiniteReward≤2+Real.sin (-1) :=
  (actual_p_ctl_03 (3/2) (by norm_num) (-1)).1 actualPolicy
example : (run (3/2) (by norm_num) (selectorPolicy (3/2) (by norm_num)) (Real.pi/2)).infiniteReward=3 := by
  have h:=actual_selector_reward (3/2) (by norm_num) (Real.pi/2)
  norm_num at h
  exact h
example : (run 0 le_rfl (selectorPolicy 0 le_rfl) (Real.pi/2)).infiniteReward=3 := by
  have h:=actual_selector_reward 0 le_rfl (Real.pi/2)
  norm_num at h
  exact h
example : ∀ᵐ z ∂(selectorRun (3/2) (by norm_num) (-1)).toItoRun.occupation 10,z.2=0 :=
  (selectorRun (3/2) (by norm_num) (-1)).selector_ae 10
-- Zero deployment kills drift but not the U3 second-order term.
theorem zero_bound : ∀ᵐ p ∂inputLaw 0, |((0 : fullPredictableL2 0) : Lp ℝ 2 (inputLaw 0)) p|≤(0 : ℝ) := by
  simp [inputLaw_zero]
example : (∫ w,Real.cos (state (-1) (-2) 3 w) ∂fullLaw 0 0)=Real.cos (-1)+
    ∫ t,∫ w,(-2 : ℝ)*Real.cos (state (-1) (-2) t w) ∂fullLaw 0 0 ∂timeLaw 3 := by
  simpa [generator_cos,BrownianBoundedControlSource.control] using actual_controlled_expectation_at 0 0 0 le_rfl zero_bound 3 (-1) (-2)
    Real.cos cos_C2 1 1 (by norm_num) (by norm_num) cos_bound cos_bound2
#print axioms targetIntegralQ_eq_actual
#print axioms target_baseline_mean_eq_cross
#print axioms test_integral_mean_at
#print axioms actual_controlled_expectation_at
#print axioms actual_controlled_dynkin
#print axioms actual_discounted_expectation
#print axioms terminalLaw_probability
#print axioms occupation_integral
#print axioms actual_discounted_occupation
#print axioms reward_integrable_infinite
#print axioms actual_reward_tendsto
#print axioms actualItoRun
#print axioms actual_reward_le_value
#print axioms actualControlFamily
#print axioms actual_p_ctl_03
#print axioms actual_selector_reward
#print axioms actual_cos_all_read
end
end FixedQControlIndependent
