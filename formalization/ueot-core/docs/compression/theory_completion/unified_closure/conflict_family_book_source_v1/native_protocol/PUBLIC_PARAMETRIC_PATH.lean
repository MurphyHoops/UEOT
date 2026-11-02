import UEOT
namespace IndependentConflictParametricPath
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.PathError
open ConflictParametricSource ConflictParametricPath
noncomputable section
abbrev theta : ℝ:=1/8
theorem h0 : 0≤theta:=by norm_num
theorem h1 : theta≤1:=by norm_num
theorem hs : theta<1:=by norm_num

theorem THIS_observed_production_path (T : ℕ) :
 law theta h0 h1 T=causalLaw (PMF.pure (true,false))
 (riskMicroControlKernel Prod.fst (fun _=>M.transitionPMF) (observedPolicy theta h0 h1)) T :=actual_record_law _ _ _ _
theorem original_T2_first_exit :
 (law theta h0 h1 2).toMeasure.real {h|¬survives 2 h}=(15/64:ℝ) :=by
 rw [actual_first_exit_probability];norm_num [theta]
theorem original_T2_survival :
 survivalMass theta h0 h1 2=(49/64:ℝ) :=by
 rw [exact_survival_mass];norm_num [theta]
theorem whole_conditioned_PATH (T : ℕ) :
 (law theta h0 hs.le T).filter {h|survives T h} (survival_supported theta h0 hs T)=
 law 0 (by norm_num) (by norm_num) T :=full_conditioned_path_eq_zero_policy theta h0 hs T
theorem conditioned_timeZERO :
 (law theta h0 hs.le 0).filter {h|survives 0 h} (survival_supported theta h0 hs 0)=
 PMF.pure (true,false) :=full_conditioned_path_eq_zero_policy theta h0 hs 0
theorem all_time_uncertified_row_mass (n : ℕ) :
 (coverageDeploymentRowLaw (PMF.pure (true,false)) Prod.fst (fun _=>M.transitionPMF)
 (observedPolicy theta h0 h1) n).toMeasure.real {xa|¬xa.2=true}=theta :=actual_uncertified_occupancy _ _ _ _
theorem declaring_ALLcert_does_not_remove_source_risk :
 (coverageDeploymentRowLaw (PMF.pure (true,false)) Prod.fst (fun _=>M.transitionPMF)
 (observedPolicy theta h0 h1) 1).toMeasure.real {_xa|¬True}=0 ∧
 (law theta h0 h1 2).toMeasure.real {h|¬survives 2 h}>0 :=by
 refine ⟨all_rows_certified_zero_occupancy _ _ _ _,?_⟩
 rw [original_T2_first_exit];norm_num
theorem different_safe_reference_zero_exit (T : ℕ) :
 (referenceLaw theta h0 h1 T).toMeasure.real {h|¬survives T h}=0 :=reference_zero_exit_probability _ _ _ _
theorem safe_reference_SOURCE_differs_from_actual_false (x : State) :
 M.transitionPMF x false≠M.transitionPMF x true :=by
 intro he
 have hh:=congrArg (fun p:PMF State=>(p (false,true)).toReal) he
 rw [transition_real,transition_real] at hh
 norm_num at hh
def returnedHistory : History 2 := (((true,false),(false,(false,true))),(true,(true,false)))
theorem interrupted_then_returned_actual_atom :
 (law theta h0 h1 2 returnedHistory).toReal=(7/256:ℝ) :=by
 have hm : (law theta h0 h1 1 (((true,false),(false,(false,true))) : History 1)).toReal=(1/16:ℝ) :=by
  calc
   _ = (law theta h0 h1 0 (true,false)).toReal * actionWeight theta false *
       (if (false,true).1=false then (1/2:ℝ) else 0) :=mass_succ theta h0 h1 0 (true,false) false (false,true)
   _ = _ :=by
    change ((PMF.pure (true,false) : PMF State) (true,false)).toReal * (1/8) * (1/2) = (1/16:ℝ)
    norm_num

 have ht := mass_succ theta h0 h1 1 (((true,false),(false,(false,true))) : History 1) true (true,false)
 rw [hm] at ht
 norm_num [actionWeight,theta] at ht
 exact ht

theorem returned_atom_is_not_full_survival : ¬survives 2 returnedHistory :=by
 simp [returnedHistory,survives]
theorem endpoint_one_no_positive_survival (n : ℕ) :
 (law 1 (by norm_num) (by norm_num) (n+1)).toMeasure {h|survives (n+1) h}=0 :=theta_one_positive_survival_zero n
theorem timeZERO_no_first_exit :
 (law 1 (by norm_num) (by norm_num) 0).toMeasure.real {h|¬survives 0 h}=0 :=by
 rw [actual_first_exit_probability];norm_num
end
#print axioms h0
#print axioms h1
#print axioms hs
#print axioms THIS_observed_production_path
#print axioms original_T2_first_exit
#print axioms original_T2_survival
#print axioms whole_conditioned_PATH
#print axioms conditioned_timeZERO
#print axioms all_time_uncertified_row_mass
#print axioms declaring_ALLcert_does_not_remove_source_risk
#print axioms different_safe_reference_zero_exit
#print axioms safe_reference_SOURCE_differs_from_actual_false
#print axioms interrupted_then_returned_actual_atom
#print axioms returned_atom_is_not_full_survival
#print axioms endpoint_one_no_positive_survival
#print axioms timeZERO_no_first_exit
end IndependentConflictParametricPath
