import UEOT
namespace ControlledC2Independent
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralLiteralIntervals
open BrownianBoundedC2DynkinSource BrownianScalarItoSource BrownianIntegralTimeEnergy BrownianIntegralCrossVariation
open BrownianBoundedPredictableApproximation BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianOwnQTimeInput BrownianOwnQTargetIntegral BrownianOwnQTargetShift
open BrownianControlledTestInput BrownianControlledC2Source
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

def g : fullPredictableL2 2 := testInput 2 (-1) (-2) Real.cos cos_C2 1 (by norm_num) cos_bound
theorem g_bound : ∀ᵐ p ∂inputLaw 2, |(g : Lp ℝ 2 (inputLaw 2)) p|≤(2 : ℝ) := by
  have h:=testInput_bound 2 (-1) (-2) Real.cos cos_C2 1 (by norm_num) cos_bound
  norm_num at h
  exact h
theorem actual_g_coe : (g : Lp ℝ 2 (inputLaw 2))=ᵐ[inputLaw 2]
    fun p=>2*Real.sin (state (-1) (-2) p.1 p.2) := by
  filter_upwards [testInput_coe 2 (-1) (-2) Real.cos cos_C2 1 (by norm_num) cos_bound] with p hp
  change (g : Lp ℝ 2 (inputLaw 2)) p=_ at hp
  rw [hp,Real.deriv_cos]
  ring
example : targetInputValueQ 2 b (3/2) (by norm_num) b_bound g 2 (by norm_num)∈
    BrownianOwnQIntegralClosure.integralDomain 2 b (3/2) (by norm_num) b_bound 2 :=
  targetInput_mem_domain 2 b (3/2) (by norm_num) b_bound g 2 (by norm_num) g_bound
example : (∫ w,targetIntegralQ 2 b (3/2) (by norm_num) b_bound g 2 (by norm_num) g_bound w ∂fullLaw 2 b)=0 :=
  targetIntegralQ_mean_zero 2 b (3/2) (by norm_num) b_bound g 2 (by norm_num) g_bound
example : targetIntegralQ 2 b (3/2) (by norm_num) b_bound g 2 (by norm_num) g_bound=ᵐ[fullLaw 2 b]
    fun w=>(predictableIntegral 2 g : (ℝ≥0→ℝ)→ℝ) w-crossTimeEnergy 2 g b 2 w :=
  targetIntegralQ_eq_actual 2 b (3/2) (by norm_num) b_bound g 2 (by norm_num) g_bound
example : Integrable (crossTimeEnergy 2 g b 2) (fullLaw 2 b) :=
  actual_cross_integrable 2 b (3/2) (by norm_num) b_bound g 2 (by norm_num) g_bound
example : Integrable (predictableIntegral 2 g : (ℝ≥0→ℝ)→ℝ) (fullLaw 2 b) :=
  target_baseline_integrable 2 b (3/2) (by norm_num) b_bound g 2 (by norm_num) g_bound
example : (∫ w,(predictableIntegral 2 g : (ℝ≥0→ℝ)→ℝ) w ∂fullLaw 2 b)=
    ∫ w,crossTimeEnergy 2 g b 2 w ∂fullLaw 2 b :=
  target_baseline_mean_eq_cross 2 b (3/2) (by norm_num) b_bound g 2 (by norm_num) g_bound

theorem generator_cos (x a : ℝ) : controlledGenerator (-2) Real.cos x a=
    2*a*Real.sin x-2*Real.cos x := by
  rw [controlledGenerator,Real.deriv_cos,cos_second]
  simp only [Pi.neg_apply]
  ring
-- Physical state is ORIGINALB under fixed b's Q: it has real drift, and is
-- not being declared Gaussian with variance4t. W_b, rather than this X, is Brownian.
theorem actual_cos_expectation : (∫ w, Real.cos (state (-1) (-2) 2 w) ∂fullLaw 2 b)=Real.cos (-1)+
    ∫ t,∫ w, (2 : ℝ)*control 2 b (3/2) t w*Real.sin (state (-1) (-2) t w)-
      2*Real.cos (state (-1) (-2) t w) ∂fullLaw 2 b ∂timeLaw 2 := by
  simpa [generator_cos] using actual_controlled_expectation 2 b (3/2) (by norm_num) b_bound (-1) (-2)
    Real.cos cos_C2 1 1 (by norm_num) (by norm_num) cos_bound cos_bound2
example : Integrable (fun w=>Real.cos (state (-1) (-2) 2 w)) (fullLaw 2 b) :=
  state_test_integrable 2 b (3/2) (by norm_num) b_bound (-1) (-2) Real.cos cos_C2
    1 1 (by norm_num) (by norm_num) cos_bound cos_bound2
example : state (-1) (-2) 0=ᵐ[fullLaw 2 b] fun _=>(-1 : ℝ) := state_initial 2 b (-1) (-2)
example (t : ℝ≥0) (w : ℝ≥0→ℝ) : state (-1) (-2) t w= -1-2*shiftedProcess 2 b (3/2) t w-
    2*(∫ u in (0 : ℝ)..(min t 2 : ℝ≥0), boundedRepresentative 2 b (3/2) (u,w)) := by
  have h:=state_controlled_primitive 2 b (3/2) (-1) (-2) t w
  convert h using 1; ring
-- Degenerate diffusion and zero horizon are separate actual boundaries;
-- no selected-success condition or changed deployment law is inserted.
example : (∫ w, Real.cos (state (-1) 0 2 w) ∂fullLaw 2 b)=Real.cos (-1) := by
  simpa [controlledGenerator] using actual_controlled_expectation 2 b (3/2) (by norm_num) b_bound (-1) 0
    Real.cos cos_C2 1 1 (by norm_num) (by norm_num) cos_bound cos_bound2
def zeroB : fullPredictableL2 0 := 0
theorem zero_bound : ∀ᵐ p ∂inputLaw 0, |(zeroB : Lp ℝ 2 (inputLaw 0)) p|≤(0 : ℝ) := by simp [inputLaw_zero]
example : (∫ w, Real.cos (state (-1) (-2) 0 w) ∂fullLaw 0 zeroB)=Real.cos (-1) := by
  simpa [timeLaw] using actual_controlled_expectation 0 zeroB 0 (by norm_num) zero_bound (-1) (-2)
    Real.cos cos_C2 1 1 (by norm_num) (by norm_num) cos_bound cos_bound2
#print axioms targetInput_mem_domain
#print axioms target_outputs_tendsto
#print axioms targetIntegralQ_returns_literal
#print axioms targetIntegralQ_mean_zero
#print axioms targetIntegralQ_eq_actual
#print axioms actual_cross_integrable
#print axioms target_baseline_mean_eq_cross
#print axioms testInput_coe
#print axioms testInput_bound
#print axioms test_integral_mean_eq_control_drift
#print axioms state_controlled_primitive
#print axioms actual_ito_identity
#print axioms actual_controlled_expectation
#print axioms state_test_integrable
#print axioms actual_cos_expectation
end
end ControlledC2Independent
