import UEOT
namespace OwnQClosureIndependent
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralLiteralIntervals
open BrownianBoundedPredictableApproximation BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianOwnQTimeInput BrownianOwnQIntegralClosure BrownianOwnQBoundedInput
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
-- Fresh nonsmooth positive coefficient depends on TWO original history times;
-- distinct from author's sine and the previous review's sum-of-signs input.
def H (w : ℝ≥0→ℝ) : ℝ := if 0≤process 1 w*process (1/2) w then 1 else 1/2
theorem H_past : StronglyMeasurable[naturalFiltration 1] H := by
  have hm := (process_stronglyAdapted 1).mul
    ((process_stronglyAdapted (1/2)).mono (naturalFiltration.mono (by norm_num)))
  let : MeasurableSpace (ℝ≥0→ℝ) := naturalFiltration 1
  have hs : MeasurableSet {w : ℝ≥0→ℝ | 0≤process 1 w*process (1/2) w} :=
    measurableSet_le measurable_const hm.measurable
  exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable
theorem H_bound (w : ℝ≥0→ℝ) : ‖H w‖≤1 := by unfold H; split_ifs <;> norm_num
theorem H_top : MemLp H ∞ sourceLaw :=
  MemLp.of_bound (H_past.mono (naturalFiltration.le 1)).aestronglyMeasurable 1 (ae_of_all _ H_bound)
def f : fullPredictableL2 2 := intervalInput 2 1 2 (by norm_num) le_rfl H H_past H_top
theorem f_bound : ∀ᵐ p ∂inputLaw 2, |(f : Lp ℝ 2 (inputLaw 2)) p|≤(1 : ℝ) := by
  filter_upwards [intervalInput_coe 2 1 2 (by norm_num) le_rfl H H_past H_top] with p hp
  change (f : Lp ℝ 2 (inputLaw 2)) p=intervalIntegrand H 1 2 p at hp
  rw [hp]
  unfold intervalIntegrand
  change |(Ioc (1 : ℝ) 2).indicator (fun _=>1) p.1*H p.2|≤1
  by_cases ht : p.1∈Ioc (1 : ℝ) 2
  · rw [Set.indicator_of_mem ht,one_mul]
    simpa only [Real.norm_eq_abs] using H_bound p.2
  · simp [Set.indicator_of_notMem ht]
example (U : ℝ≥0) : inputLawQ 2 f U≪inputLaw U := inputLawQ_absolutelyContinuous 2 f U
example : boundedInputValueQ 2 f 1 (by norm_num) f_bound∈
    BrownianOwnQIntegralClosure.integralDomain 2 f 1 (by norm_num) f_bound 2 :=
  boundedInput_mem_domain 2 f 1 (by norm_num) f_bound
example : boundedInputValueQ 2 f 1 (by norm_num) f_bound=ᵐ[inputLawQ 2 f 2]
    fun p=>control 2 f 1 p.1 p.2 := boundedInputValueQ_returns_control 2 f 1 (by norm_num) f_bound
example : Tendsto (fun n=>inputValueQ 2 f 1 (by norm_num) f_bound
    (approximation 2 f 1 (by norm_num) f_bound n)) atTop
      (𝓝 (boundedInputValueQ 2 f 1 (by norm_num) f_bound)) :=
  actual_inputs_tendsto 2 f 1 (by norm_num) f_bound
example : Tendsto (fun n=>outputValueQ 2 f 1 (by norm_num) f_bound
    (approximation 2 f 1 (by norm_num) f_bound n)) atTop
      (𝓝 (boundedIntegralQ 2 f 1 (by norm_num) f_bound)) :=
  actual_outputs_tendsto 2 f 1 (by norm_num) f_bound
example : Integrable (boundedIntegralQ 2 f 1 (by norm_num) f_bound : (ℝ≥0→ℝ)→ℝ) (fullLaw 2 f) :=
  boundedIntegralQ_integrable 2 f 1 (by norm_num) f_bound
example : (∫ w, boundedIntegralQ 2 f 1 (by norm_num) f_bound w ∂fullLaw 2 f)=0 :=
  boundedIntegralQ_mean_zero 2 f 1 (by norm_num) f_bound
-- This SAME f is literally finite. Bind its newly constructed Q domain point
-- to that actual record, then test the extended SAME integral's literal return.
def r : ElementaryInput 2 := intervalRecord 2 1 2 (by norm_num) le_rfl H H_past H_top
private theorem same_native_input : boundedInputValueQ 2 f 1 (by norm_num) f_bound=
    inputValueQ 2 f 1 (by norm_num) f_bound r := by
  have hP : (f : Lp ℝ 2 (inputLaw 2)) =ᵐ[inputLaw 2] integrand r.clock r.coefficient :=
    (BrownianTimeIntegrand.integrand_memLp_two 2 r.clock r.coefficient r.coefficient_bounded).coeFn_toLp
  apply Lp.ext
  apply (boundedInputValueQ_coe 2 f 1 (by norm_num) f_bound).trans
  have hQ : boundedRepresentative 2 f 1 =ᵐ[inputLawQ 2 f 2] integrand r.clock r.coefficient :=
    (inputLawQ_absolutelyContinuous 2 f 2).ae_le ((boundedRepresentative_ae 2 f 1 f_bound).symm.trans hP)
  filter_upwards [hQ,(BrownianOwnQTimeInput.integrand_memLp_two 2 f 1 (by norm_num) f_bound r).coeFn_toLp]
    with p hg hr
  exact hg.trans hr.symm

theorem SAME_actual_bounded_integral_literal : boundedIntegralQ 2 f 1 (by norm_num) f_bound=
    outputValueQ 2 f 1 (by norm_num) f_bound r := by
  have he : boundedInputQ 2 f 1 (by norm_num) f_bound=
      representedInput 2 f 1 (by norm_num) f_bound r := Subtype.ext same_native_input
  unfold boundedIntegralQ
  rw [he,BrownianOwnQIntegralClosure.integral_returns_literal]
example : (boundedIntegralQ 2 f 1 (by norm_num) f_bound : (ℝ≥0→ℝ)→ℝ)=ᵐ[fullLaw 2 f]
    BrownianOwnQSimpleIntegral.simpleIntegral 2 f 1 r := by
  rw [SAME_actual_bounded_integral_literal]
  exact (BrownianOwnQSimpleIntegral.simpleIntegral_memLp_two 2 f 1 (by norm_num) f_bound r).coeFn_toLp

-- DensityA0 and integrator horizon3 are distinct; closure preserves real
-- execution noise even though the SAME density-control itself has zero dt mass.
def zeroF : fullPredictableL2 0 := 0
theorem zero_bound : ∀ᵐ p ∂inputLaw 0, |(zeroF : Lp ℝ 2 (inputLaw 0)) p|≤(0 : ℝ) := by
  simp [inputLaw_zero]
example : boundedInputValueQ 0 zeroF 0 (by norm_num) zero_bound=ᵐ[inputLawQ 0 zeroF 0]
    fun p=>control 0 zeroF 0 p.1 p.2 := boundedInputValueQ_returns_control 0 zeroF 0 (by norm_num) zero_bound
example : boundedInputValueQ 0 zeroF 0 (by norm_num) zero_bound=0 := by
  apply Lp.ext
  have hm : inputLawQ 0 zeroF 0=0 := by simp [inputLawQ,timeLaw]
  exact ae_iff.mpr (by simp [hm])
example : boundedIntegralQ 0 zeroF 0 (by norm_num) zero_bound=0 := by
  apply norm_eq_zero.mp
  rw [boundedIntegralQ_norm]
  have hm : inputLawQ 0 zeroF 0=0 := by simp [inputLawQ,timeLaw]
  have hz : boundedInputValueQ 0 zeroF 0 (by norm_num) zero_bound=0 := by
    apply Lp.ext
    exact ae_iff.mpr (by simp [hm])
  rw [hz,norm_zero]
theorem zero_density_nonzero_integrator :
    ‖BrownianOwnQIntegralClosure.integral 0 zeroF 0 (by norm_num) zero_bound 3
      (representedInput 0 zeroF 0 (by norm_num) zero_bound (BrownianIntegralClosure.unitInput 3))‖^2=3 := by
  rw [BrownianOwnQIntegralClosure.integral_returns_literal]
  unfold outputValueQ
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  rw [integral_congr_ae ((BrownianOwnQSimpleIntegral.simpleIntegral_memLp_two 0 zeroF 0 (by norm_num) zero_bound
    (BrownianIntegralClosure.unitInput 3)).coeFn_toLp.mono (fun _ h=>congrArg (fun x : ℝ=>x^2) h))]
  let _ := fullLaw_probability 0 zeroF 0 (by norm_num) zero_bound
  rw [BrownianOwnQSimpleIntegral.simpleIntegral_isometry 0 zeroF 0 (by norm_num) zero_bound]
  change (∑ i : Fin 1,
    (((BrownianIntegralClosure.unitInput 3).clock i.succ : ℝ)-((BrownianIntegralClosure.unitInput 3).clock i.castSucc : ℝ))*
      (∫ w, (BrownianIntegralClosure.unitInput 3).coefficient i w^2 ∂fullLaw 0 zeroF))=3
  rw [Fin.sum_univ_one]
  change ((3 : ℝ)-0)*(∫ _ : ℝ≥0→ℝ, (1 : ℝ)^2 ∂fullLaw 0 zeroF)=3
  simp
example (x : BrownianOwnQIntegralClosure.integralDomain 2 f 1 (by norm_num) f_bound 4) :
    ‖BrownianOwnQIntegralClosure.integral 2 f 1 (by norm_num) f_bound 4 x‖=‖x‖ :=
  integral_norm 2 f 1 (by norm_num) f_bound 4 x
#print axioms BrownianOwnQIntegralClosure.combination_norm
#print axioms BrownianOwnQIntegralClosure.integral_returns_literal
#print axioms BrownianOwnQIntegralClosure.integral_norm
#print axioms BrownianOwnQIntegralClosure.literal_outputs_tendsto
#print axioms inputLawQ_density
#print axioms inputLawQ_absolutelyContinuous
#print axioms actual_inputs_tendsto
#print axioms boundedInputValueQ_returns_control
#print axioms boundedInput_mem_domain
#print axioms actual_outputs_tendsto
#print axioms boundedIntegralQ_integrable
#print axioms boundedIntegralQ_mean_zero
#print axioms SAME_actual_bounded_integral_literal
#print axioms zero_density_nonzero_integrator
end
end OwnQClosureIndependent
