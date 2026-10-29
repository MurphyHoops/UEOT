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
