import UEOT
namespace IndependentConflictParametricInfinite
open MeasureTheory ProbabilityTheory
open UEOT.V3.PathError
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open ConflictParametricSource ConflictParametricPath ConflictParametricInfinite
noncomputable section
abbrev theta : ℝ:=2/7
theorem h0 : 0≤theta:=by norm_num
theorem h1 : theta≤1:=by norm_num
theorem hp : 0<theta:=by norm_num

theorem actual_event_hidden_false :
 (eventRow theta h0 h1 (false,(false,true))).toReal=(1/7:ℝ) :=by
 rw [actual_event_mass];norm_num [theta,actionWeight]
theorem actual_event_hidden_true :
 (eventRow theta h0 h1 (true,(true,false))).toReal=(5/14:ℝ) :=by
 rw [actual_event_mass];norm_num [theta,actionWeight]
theorem inconsistent_action_visible_has_zero_mass (u : Bool) :
 (eventRow theta h0 h1 (false,(true,u))).toReal=0 :=by
 rw [actual_event_mass];simp
theorem SAME_full_record_cylinders (n : ℕ) :
 (source theta h0 h1).map (recordPrefix n)=(law theta h0 h1 n).toMeasure :=finite_record_cylinder _ _ _ n
theorem SAME_production_full_record_cylinders (n : ℕ) :
 (source theta h0 h1).map (recordPrefix n)=
 (causalLaw (PMF.pure (true,false)) (riskMicroControlKernel Prod.fst (fun _=>M.transitionPMF)
 (observedPolicy theta h0 h1)) n).toMeasure :=by
 rw [finite_record_cylinder,actual_record_law]
theorem actual_past_independent (n : ℕ) :
 IndepFun (recordPrefix n) (fun w:Stream=>w n) (source theta h0 h1) :=current_independent_prefix _ _ _ _
theorem actual_T3_survival_cylinder :
 source theta h0 h1 {w|survives 3 (recordPrefix 3 w)}=ENNReal.ofReal (125/343:ℝ) :=by
 rw [actual_survival_cylinder];norm_num [theta]
theorem actual_persistent_survival_null :
 source theta hp.le h1 {w|∀n,survives n (recordPrefix n w)}=0 :=persistent_survival_null theta hp h1
theorem actual_EVENTUAL_failure_ae :
 ∀ᵐw ∂source theta hp.le h1,∃n,¬survives n (recordPrefix n w) :=actual_eventual_failure_ae theta hp h1
def allSafeStream : Stream:=fun _=>(true,(true,true))
theorem null_event_nonempty_not_pointwise_failure :
 ∀n,survives n (recordPrefix n allSafeStream) :=by
 intro n;induction n with
 | zero=>rfl
 | succ n ih=>exact ⟨ih,rfl⟩
theorem chronological_current_prefix (n : ℕ) (w : Stream) :
 (recordPrefix (n+1) w).1=recordPrefix n w :=record_prefix_consistent n w
theorem actual_T3_reference_budget :
 (law theta h0 h1 3).toMeasure.real {h|¬survives 3 h}≤
 (referenceLaw theta h0 h1 3).toMeasure.real {h|¬survives 3 h}+(6/7:ℝ) :=by
 convert actual_zero_reference_budget theta h0 h1 3 using 1;norm_num [theta]
theorem budget_has_positive_actual_risk :
 (law theta h0 h1 3).toMeasure.real {h|¬survives 3 h}=(218/343:ℝ) :=by
 rw [actual_first_exit_probability];norm_num [theta]
theorem endpoint_one_same_infinite_source_fails_first_tick :
 source 1 (by norm_num) (by norm_num) {w|survives 1 (recordPrefix 1 w)}=0 :=by
 rw [actual_survival_cylinder];norm_num
theorem endpoint_zero_same_source_survives :
 ∀ᵐ w ∂source 0 (by norm_num) (by norm_num), ∀n,survives n (recordPrefix n w) :=zero_theta_survives_ae
end
#print axioms h0
#print axioms h1
#print axioms hp
#print axioms actual_event_hidden_false
#print axioms actual_event_hidden_true
#print axioms inconsistent_action_visible_has_zero_mass
#print axioms SAME_full_record_cylinders
#print axioms SAME_production_full_record_cylinders
#print axioms actual_past_independent
#print axioms actual_T3_survival_cylinder
#print axioms actual_persistent_survival_null
#print axioms actual_EVENTUAL_failure_ae
#print axioms null_event_nonempty_not_pointwise_failure
#print axioms chronological_current_prefix
#print axioms actual_T3_reference_budget
#print axioms budget_has_positive_actual_risk
#print axioms endpoint_one_same_infinite_source_fails_first_tick
#print axioms endpoint_zero_same_source_survives
end IndependentConflictParametricInfinite
