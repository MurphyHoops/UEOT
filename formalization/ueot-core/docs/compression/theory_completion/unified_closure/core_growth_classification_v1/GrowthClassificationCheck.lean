import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreTheoryClosure

/-! Boundary consumers for the finite growth-classification extension.
These use kernel-checked real arithmetic and the actual population endpoints.
They are not new feedback, finite-deadline optimality, or empirical claims. -/
namespace UEOTGrowthClassificationCheck
noncomputable section
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open CoreRegenerativeSource CoreRegenerativeControlPopulation
open CoreRegenerativeGrowthClassification CoreRegenerativeGrowthPopulation
open CoreRegenerativeGrowthAttainment

def careSubcritical : Parameters := ⟨3/5, 1/10, 3/10, 1/2, 1/5⟩
def subcritical : Parameters := ⟨1/2, 1/8, 1/4, 1/4, 1/3⟩
def critical : Parameters := ⟨2/3, 1/8, 1/4, 1/4, 1/3⟩
def careAdvantage : Parameters := ⟨3/4, 1/4, 3/8, 1/8, 1/3⟩
def tie : Parameters := ⟨3/4, 1/8, 1/4, 1/8, 1/3⟩

theorem careSubcritical_valid : ProbabilityValid careSubcritical := by
  constructor <;> norm_num [careSubcritical]
theorem subcritical_valid : ProbabilityValid subcritical := by
  constructor <;> norm_num [subcritical]
theorem critical_valid : ProbabilityValid critical := by
  constructor <;> norm_num [critical]
theorem careAdvantage_valid : ProbabilityValid careAdvantage := by
  constructor <;> norm_num [careAdvantage]
theorem tie_valid : ProbabilityValid tie := by
  constructor <;> norm_num [tie]

theorem careSubcritical_not_old_Valid : ¬ Valid careSubcritical := by
  intro h
  have hs := h.supercritical
  norm_num [careSubcritical] at hs

theorem careSubcritical_rates :
    kc careSubcritical = 9/10 ∧ growthRate careSubcritical true = 61/50 ∧
    optimalRate careSubcritical = 61/50 := by
  norm_num [kc, kb, kStar, mu, optimalRate, growthRate, programAction,
    countRate, survivalRate, birthRate, careSubcritical]

theorem subcritical_rates :
    growthRate subcritical false = 3/4 ∧ growthRate subcritical true = 5/6 ∧
    optimalRate subcritical = 1 := by
  norm_num [kc, kb, kStar, mu, optimalRate, growthRate, programAction,
    countRate, survivalRate, birthRate, subcritical]

theorem critical_rates :
    kc critical = 11/12 ∧ growthRate critical true = 1 ∧ optimalRate critical = 1 := by
  norm_num [kc, kb, kStar, mu, optimalRate, growthRate, programAction,
    countRate, survivalRate, birthRate, critical]

theorem careAdvantage_rates :
    growthRate careAdvantage false = 9/8 ∧ growthRate careAdvantage true = 25/24 ∧
    optimalRate careAdvantage = 9/8 := by
  norm_num [kc, kb, kStar, mu, optimalRate, growthRate, programAction,
    countRate, survivalRate, birthRate, careAdvantage]

theorem enlarged_domain_actual_internal (index : ℕ) (tag : Bool) :
    HasExpectedGrowth careSubcritical (programPolicy true)
      (founderState index true true tag) (optimalRate careSubcritical) := by
  apply (damaged_program_attains_iff careSubcritical careSubcritical_valid index true tag).mpr
  norm_num [programRegion, careSubcritical, growthRate, programAction,
    countRate, survivalRate, birthRate]

theorem reversed_actual_internal (index : ℕ) (tag : Bool) :
    HasExpectedGrowth careAdvantage (programPolicy false)
      (founderState index false true tag) (optimalRate careAdvantage) := by
  apply (damaged_program_attains_iff careAdvantage careAdvantage_valid index false tag).mpr
  norm_num [programRegion, careAdvantage, kc, countRate, survivalRate, birthRate]

theorem critical_actual_internal (index : ℕ) (tag : Bool) :
    HasExpectedGrowth critical (programPolicy true)
      (founderState index true true tag) (optimalRate critical) := by
  apply (damaged_program_attains_iff critical critical_valid index true tag).mpr
  norm_num [programRegion, critical, growthRate, programAction,
    countRate, survivalRate, birthRate]

theorem tie_both_actual_internal (index : ℕ) (theta tag : Bool) :
    HasExpectedGrowth tie (programPolicy theta)
      (founderState index theta true tag) (optimalRate tie) := by
  apply (damaged_program_attains_iff tie tie_valid index theta tag).mpr
  cases theta <;> norm_num [programRegion, tie, kc, growthRate, programAction,
    countRate, survivalRate, birthRate]

theorem subcritical_actual_internal_failure (index : ℕ) (theta tag : Bool) :
    ¬ HasExpectedGrowth subcritical (programPolicy theta)
      (founderState index theta true tag) (optimalRate subcritical) := by
  rw [damaged_program_attains_iff subcritical subcritical_valid]
  cases theta <;> norm_num [programRegion, subcritical, kc, growthRate, programAction,
    countRate, survivalRate, birthRate]

#print axioms valid_iff_probability_advantage_supercritical
#print axioms CoreRegenerativeGrowthClassification.noiseWeight_pos
#print axioms actual_one_step_value_le
#print axioms actual_selected_one_step_value_eq
#print axioms optimal_population_upper
#print axioms optimal_hasExpectedGrowth
#print axioms programPolicy_positive_branch_is_internal
#print axioms optimalRate_isLeast_uniform_upper
#print axioms false_program_attains_iff
#print axioms true_program_attains_iff
#print axioms same_damaged_program_repairs_and_attains_iff
#print axioms subcritical_existing_programs_do_not_attain
#print axioms old_valid_damaged_program_attains
#print axioms enlarged_domain_actual_internal
#print axioms subcritical_actual_internal_failure
end
end UEOTGrowthClassificationCheck
