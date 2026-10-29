import UEOT
namespace IndependentIdentityReusedConsumer
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open DualDriveNoisyOperationalCalibration DualDriveFiniteNoisyCalibration
namespace ActualFiniteCalibrationConsumer
noncomputable section
set_option linter.defProp false
local notation "DATA" => sourceData regularParameters registeredRaw
private def hspec := select_spec DATA true registered_regular_output.1
/-- Same observed samples, SAME actual checked inverse consumed by calibration. -/
def actualChecked := dataChecked DATA hspec.2.1 hspec.2.2.1
example (z : Coordinate 2) : actualChecked.symm (columns (measuredSamples DATA) z)=z :=
  computed_inverse_left DATA hspec.2.1 hspec.2.2.1 z
example (z : Coordinate 2) : columns (measuredSamples DATA) (actualChecked.symm z)=z :=
  computed_inverse_right DATA hspec.2.1 hspec.2.2.1 z
/-- The actual SAME returned coefficient has a small NONZERO finite-data error. -/
theorem actual_returned_vector :
    coefficients (computedInverse DATA) (measuredQueries DATA true)=(320/321 : ℝ) • unit (1 : Fin 2) := by
  have h0 := registered_regular_output.2.1
  have h1 := registered_regular_output.2.2.1
  have h3 : mean DATA 3=(2 : ℚ) := by
    norm_num [registered_means,trueMean,regularParameters,Fin.ext_iff]
  ext i
  fin_cases i <;>
    norm_num [coefficients,computedInverse,measuredQueries,diagonal_apply,unit,h0,h1,h3]

theorem actual_nonzero_error :
    ‖coefficients (computedInverse DATA) (measuredQueries DATA true)-unit (1 : Fin 2)‖=(1/321 : ℝ) := by
  have h : coefficients (computedInverse DATA) (measuredQueries DATA true)-unit (1 : Fin 2)=
      ((320/321 : ℝ)-1) • unit (1 : Fin 2) := by rw [actual_returned_vector,sub_smul,one_smul]
  rw [h,norm_smul,norm_unit,mul_one,Real.norm_eq_abs]
  norm_num

/-- Unknown order genuinely varies between legal sources; changed observed
query data from SAME frozen primitive word return different correct actions. -/
example : regularParameters.latent false < regularParameters.latent true := registered_regular_action_correct
example : reverseParameters.latent true < reverseParameters.latent false := registered_reverse_action_correct
example : select DATA=some true := registered_regular_output.1
example : select (sourceData reverseParameters registeredRaw)=some false := registered_reverse_output

/-- Complete-law joint bound, not conditioned on successful witness/acceptance. -/
example : (rawLaw registeredBudget).real {omega | AcceptWrong regularParameters (sourceData regularParameters omega)} < 1 :=
  lt_of_le_of_lt (registered_joint_risk_le regularParameters regular_valid) registered_bound_nonvacuous
example : (rawLaw registeredBudget).real {omega | AcceptWrong reverseParameters (sourceData reverseParameters omega)} < 1 :=
  lt_of_le_of_lt (registered_joint_risk_le reverseParameters reverse_valid) registered_bound_nonvacuous
example : 0 < (rawLaw registeredBudget).real {registeredRaw} := registered_word_positive_mass
example (data : Data 0) : select data=none := zero_budget_reject data
example {N : ℕ} (data : Data N) (h : mean data 0=0 ∨ mean data 1=0) : select data=none := singular_data_reject data h
#print axioms actual_nonzero_error
#print axioms actualChecked
end
end ActualFiniteCalibrationConsumer
end IndependentIdentityReusedConsumer
open MeasureTheory ProbabilityTheory Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open DualDriveFiniteNoisyCalibration VariableRegisteredSamples
namespace IndependentFiniteExactData
def jsonSigns : Raw 32 := fun j =>
  match (j.1 : ℕ) with
  | 0 => (#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]).getD j.2 false
  | 1 => (#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]).getD j.2 false
  | 2 => (#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]).getD j.2 false
  | _ => (#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]).getD j.2 false
def jsonRegular : Data 32 := fun j =>
  match (j.1 : ℕ) with
  | 0 => (#[(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ)]).getD j.2 0
  | 1 => (#[(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ)]).getD j.2 0
  | 2 => (#[(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ)]).getD j.2 0
  | _ => (#[(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ)]).getD j.2 0
def jsonReverse : Data 32 := fun j =>
  match (j.1 : ℕ) with
  | 0 => (#[(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ)]).getD j.2 0
  | 1 => (#[(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ)]).getD j.2 0
  | 2 => (#[(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(21/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ),(19/10 : ℚ)]).getD j.2 0
  | _ => (#[(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ)]).getD j.2 0
theorem jsonSigns_match : ∀ j : Index 32, jsonSigns j=registeredRaw j := by
  rintro ⟨j,k⟩
  fin_cases j <;> fin_cases k <;> decide
theorem jsonRegular_matches_actual : ∀ j : Index 32, jsonRegular j=sourceData regularParameters registeredRaw j := by
  rintro ⟨j,k⟩
  fin_cases j <;> fin_cases k <;> norm_num [jsonRegular,sourceData,sensor,trueMean,regularParameters,registeredRaw,registeredBudget,bit,Fin.ext_iff]
theorem jsonReverse_matches_actual : ∀ j : Index 32, jsonReverse j=sourceData reverseParameters registeredRaw j := by
  rintro ⟨j,k⟩
  fin_cases j <;> fin_cases k <;> norm_num [jsonReverse,sourceData,sensor,trueMean,reverseParameters,registeredRaw,registeredBudget,bit,Fin.ext_iff]
#eval do
  for row in List.finRange 4 do
    for col in List.finRange 32 do
      let j : Index 32 := ⟨row,col⟩
      unless jsonSigns j == registeredRaw j && jsonRegular j == sourceData regularParameters registeredRaw j && jsonReverse j == sourceData reverseParameters registeredRaw j do
        throw (IO.userError "Independent COMPLETE128 coordinate/source mismatch")
  unless select jsonRegular == some true && select jsonReverse == some false do
    throw (IO.userError "Independent complete JSON actual selector mismatch")
  unless mean jsonRegular 0 == 2 && mean jsonRegular 1 == 321/160 && mean jsonRegular 2 == 0 && mean jsonRegular 3 == 2 do
    throw (IO.userError "Independent complete JSON rational means mismatch")
  unless conditioning jsonRegular == 1/2 && (mean jsonRegular 0)⁻¹ == 1/2 && (mean jsonRegular 1)⁻¹ == 160/321 && estimate jsonRegular true == 320/321 do
    throw (IO.userError "Independent complete JSON inverse/score mismatch")
  IO.println "ALL128 explicit registered signs and BOTH full128 observed data arrays: actual source equality + exact selector/inverse VM checks passed"
def limitRaw : Raw 32 := fun j =>
  match (j.1 : ℕ) with
  | 0 => (#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]).getD j.2 false
  | 1 => (#[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]).getD j.2 false
  | 2 => (#[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]).getD j.2 false
  | _ => (#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]).getD j.2 false
def limitParameters : Parameters := ⟨![1,9/100],fun a => if a then 1 else -1⟩
theorem limit_valid : Valid limitParameters := by
  refine ⟨?_,?_,?_⟩
  · intro i; fin_cases i <;> norm_num [limitParameters]
  · intro a; cases a <;> norm_num [limitParameters]
  · norm_num [limitParameters]
theorem limit_means : (mean (sourceData limitParameters limitRaw) 0=1) ∧
    mean (sourceData limitParameters limitRaw) 1= -1/100 ∧
    mean (sourceData limitParameters limitRaw) 2= -19/100 ∧
    mean (sourceData limitParameters limitRaw) 3=19/100 := by
  norm_num [mean,sourceData,sensor,trueMean,limitParameters,limitRaw,Fin.sum_univ_succ,bit,Fin.ext_iff]
theorem limit_actual_output : select (sourceData limitParameters limitRaw)=some false := by
  have hm := limit_means
  norm_num [select,conditioning,estimate,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2]
theorem limit_accepted_wrong : AcceptWrong limitParameters (sourceData limitParameters limitRaw) := by
  refine ⟨false,limit_actual_output,?_⟩
  intro h
  have hh := h true (by decide)
  norm_num [limitParameters] at hh
theorem limit_outside_good : limitRaw ∉ Good 32 := by
  intro hg
  obtain ⟨chosen,hs,hbad⟩ := limit_accepted_wrong
  exact hbad (good_selected_action_correct limitParameters limit_valid limitRaw (by decide) hg chosen hs)
theorem limit_word_mass : (rawLaw 32).real {limitRaw}=(1/2 : ℝ)^128 := by
  rw [Measure.real,rawLaw,productRowLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [PMF.uniformOfFintype_apply,Fintype.prod_sigma,Finset.prod_const]
theorem limit_word_positive : 0 < (rawLaw 32).real {limitRaw} := by rw [limit_word_mass]; positivity
theorem limit_positive_joint_error : 0 < (rawLaw 32).real {omega | AcceptWrong limitParameters (sourceData limitParameters omega)} := by
  apply lt_of_lt_of_le limit_word_positive
  apply measureReal_mono
  · intro omega h
    have he : omega=limitRaw := h
    subst omega
    exact limit_accepted_wrong
  · exact measure_ne_top _ _
example : (rawLaw 32).real {omega | AcceptWrong limitParameters (sourceData limitParameters omega)} ≤ 8*Real.exp (-4) :=
  registered_joint_risk_le limitParameters limit_valid
#print axioms jsonSigns_match
#print axioms jsonRegular_matches_actual
#print axioms jsonReverse_matches_actual
#print axioms limit_outside_good
#print axioms limit_positive_joint_error
end IndependentFiniteExactData
