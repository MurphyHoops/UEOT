import UEOT
namespace FiniteTableIndependent
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianIntegralClosure
open BrownianPredictableDensity BrownianFiniteStepExponentialSource BrownianFiniteStepConditionalSource
open BrownianFiniteStepTerminalKLSource BrownianFiniteStepShiftedSource
open UEOT.V3.GirsanovPathKL
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def feedback (w : ℝ≥0 → ℝ) : ℝ := 1+(1/2)*Real.sin (process 1 w)
theorem feedback_past : StronglyMeasurable[naturalFiltration 1] feedback := by
  exact (show Continuous (fun x : ℝ=>1+(1/2)*Real.sin x) by fun_prop).comp_stronglyMeasurable (process_stronglyAdapted 1)
theorem feedback_range (w : ℝ≥0 → ℝ) : (1/2 : ℝ)≤feedback w ∧ feedback w≤3/2 := by
  have hl := Real.neg_one_le_sin (process 1 w)
  have hu := Real.sin_le_one (process 1 w)
  constructor <;> dsimp only [feedback] <;> linarith
theorem feedback_top : MemLp feedback ∞ sourceLaw := by
  apply MemLp.of_bound (feedback_past.mono (naturalFiltration.le 1)).aestronglyMeasurable (3/2)
  apply ae_of_all
  intro w
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [(feedback_range w).1])]
  exact (feedback_range w).2

def table : ElementaryInput 2 where
  n := 2
  clock := ![0,1,2]
  coefficient := ![fun _=>1,feedback]
  clock_mono := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  clock_zero := rfl
  clock_end := rfl
  coefficient_past := by intro i; fin_cases i
                         · exact stronglyMeasurable_const
                         · exact feedback_past
  coefficient_bounded := by intro i; fin_cases i
                            · exact memLp_top_const 1
                            · exact feedback_top

-- All prefix normalization and ORIGINAL-clock martingale remain bound to table.
example := prefix_martingale table
example : (∫ w, prefixExponential table 1 w ∂sourceLaw)=1 := (prefix_integrable_mean table 1).2
example : sourceLaw[prefixExponential table (Fin.last table.n) | naturalFiltration 1] =ᵐ[sourceLaw]
    prefixExponential table 1 := prefix_conditional table _ 1 (by decide)
example := prefix_source table 1
example := final_centered_indep_original_past table (⟨1,by decide⟩ : Fin table.n)
example : HasLaw (centeredRow table ⟨1,by decide⟩) (gaussianReal 0 1) (tableLaw table) := by
  have h := (final_centered_law_indep table ⟨1,by decide⟩).1
  change HasLaw (centeredRow table ⟨1,by decide⟩) (gaussianReal 0 ((2 : ℝ≥0)-1)) (tableLaw table) at h
  have he : (2 : ℝ≥0)-1=1 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub (by norm_num : (1 : ℝ≥0)≤2)]
    norm_num
  simpa only [he] using h

-- Full W law on both cell interiors and BEYOND the registered horizon2.
example : HasLaw (fun w=>({0,(1/2 : ℝ≥0),1,(3/2 : ℝ≥0),2,3} : Finset ℝ≥0).restrict (tableProcess table · w))
    (BrownianReal.projectiveFamily {0,(1/2 : ℝ≥0),1,(3/2 : ℝ≥0),2,3}) (tableLaw table) :=
  (tableProcess_isBrownian table).toIsPreBrownianReal.hasLaw _
example (s : ℝ≥0) := tableProcess_indep_original_past table s
example := tableProcess_natural_eq table
example (w : ℝ≥0 → ℝ) := actual_terminal_integral_binding table w
example : (actualTerminalData table).baselineIntegral=
    (predictableIntegral 2 (literalPredictableInput table) : (ℝ≥0 → ℝ) → ℝ) := rfl

-- Crucial quantifier test: original B1 has changed law under FINALQ, despite
-- W being Brownian and W's natural past equalling originalFs exactly.
theorem W_one (w : ℝ≥0 → ℝ) : tableProcess table 1 w=process 1 w-1 := by
  rw [tableProcess_formula]
  change process 1 w-(∑ i : Fin 2, table.coefficient i w*BrownianPastStepGaussianResidualSource.overlap (table.clock i.castSucc) (table.clock i.succ) 1)=_
  rw [Fin.sum_univ_two]
  change process 1 w-((1 : ℝ)*BrownianPastStepGaussianResidualSource.overlap 0 1 1+
    feedback w*BrownianPastStepGaussianResidualSource.overlap 1 2 1)=process 1 w-1
  norm_num [BrownianPastStepGaussianResidualSource.overlap]

theorem final_original_B1_law : HasLaw (process 1) (gaussianReal 1 1) (tableLaw table) := by
  have h := gaussianReal_add_const ((tableProcess_isBrownian table).toIsPreBrownianReal.hasLaw_eval 1) 1
  convert h using 1
  · funext w
    rw [W_one]
    ring
  · norm_num

theorem final_past_is_NOT_original_P : (tableLaw table).map (process 1)≠sourceLaw.map (process 1) := by
  intro h
  have hq := final_original_B1_law.map_eq
  rw [h,(process_isPreBrownian.hasLaw_eval 1).map_eq] at hq
  have hi := congrArg (fun mu : Measure ℝ=>∫ x, x ∂mu) hq
  norm_num only [integral_id_gaussianReal] at hi

theorem original_feedback_in_returned_noise (w : ℝ≥0 → ℝ) :
    feedback w=1+(1/2)*Real.sin (tableProcess table 1 w+1) := by
  rw [W_one]
  simp [feedback]

-- Exact cost is FINALQ expectation; real source bounds do not replace it by EP.
theorem actual_energy (w : ℝ≥0 → ℝ) : tableEnergy table w=1+feedback w^2 := by
  unfold tableEnergy
  change (∑ i : Fin 2, ((table.clock i.succ : ℝ)-(table.clock i.castSucc : ℝ))*table.coefficient i w^2)=_
  rw [Fin.sum_univ_two]
  change ((1 : ℝ)-0)*1^2+(2-1)*feedback w^2=_
  ring
example : klDiv (tableLaw table) sourceLaw=ENNReal.ofReal ((1/2 : ℝ)*(∫ w, tableEnergy table w ∂tableLaw table)) ∧
    klDiv ((tableLaw table).map (fun w=>(process 1 w,process 3 w)))
      (sourceLaw.map (fun w=>(process 1 w,process 3 w))) ≤
      ENNReal.ofReal ((1/2 : ℝ)*(∫ w, tableEnergy table w ∂tableLaw table)) :=
  actual_p_kl_05 table _ ((measurable_process 1).prodMk (measurable_process 3))
example : ENNReal.ofReal (5/8 : ℝ)≤klDiv (tableLaw table) sourceLaw ∧
    klDiv (tableLaw table) sourceLaw≤ENNReal.ofReal (13/8 : ℝ) := by
  have hb (w) : (5/4 : ℝ)≤tableEnergy table w ∧ tableEnergy table w≤13/4 := by
    rw [actual_energy]
    have hh := feedback_range w
    constructor <;> nlinarith
  have hlo := integral_mono (integrable_const (5/4 : ℝ)) (tableEnergy_integrable table) (fun w=>(hb w).1)
  have hhi := integral_mono (tableEnergy_integrable table) (integrable_const (13/4 : ℝ)) (fun w=>(hb w).2)
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hlo hhi
  rw [(actual_p_kl_05 table id measurable_id).1]
  constructor <;> apply ENNReal.ofReal_le_ofReal <;> linarith

-- Repeat original feedback on an actual collapsed middle cell; full W still Brownian.
def repeated : ElementaryInput 2 where
  n := 3
  clock := ![0,1,1,2]
  coefficient := ![fun _=>1,feedback,feedback]
  clock_mono := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  clock_zero := rfl
  clock_end := rfl
  coefficient_past := by intro i; fin_cases i
                         · exact stronglyMeasurable_const
                         · exact feedback_past
                         · exact feedback_past
  coefficient_bounded := by intro i; fin_cases i
                            · exact memLp_top_const 1
                            · exact feedback_top
                            · exact feedback_top
example := tableProcess_isBrownian repeated
example (w : ℝ≥0 → ℝ) : centeredRow repeated (⟨1,by decide⟩ : Fin repeated.n) w=0 := by
  simp [centeredRow,BrownianPastStepTiltKernelSource.centeredIncrement,increment,repeated]

def empty : ElementaryInput 0 where
  n := 0
  clock := fun _=>0
  coefficient := fun j=>Fin.elim0 j
  clock_mono := fun _ _ _=>le_rfl
  clock_zero := rfl
  clock_end := rfl
  coefficient_past := fun j=>Fin.elim0 j
  coefficient_bounded := fun j=>Fin.elim0 j
example : tableProcess empty=process := prefixProcess_zero empty
example : tableLaw empty=sourceLaw := prefixLaw_zero empty
example := actualTerminalData empty

#print axioms past_weight_step_condExp
#print axioms prefix_martingale
#print axioms final_centered_law_indep
#print axioms actualTerminalData
#print axioms actual_p_kl_05
#print axioms BrownianMeasuredStepTransport.shifted_finite_map
#print axioms BrownianMeasuredStepTransport.shifted_isPreBrownian
#print axioms BrownianMeasuredStepTransport.shifted_natural_eq
#print axioms prefix_source
#print axioms tableProcess_isBrownian
#print axioms tableProcess_indep_original_past
#print axioms actual_terminal_integral_binding
#print axioms final_original_B1_law
#print axioms final_past_is_NOT_original_P
end
end FiniteTableIndependent
