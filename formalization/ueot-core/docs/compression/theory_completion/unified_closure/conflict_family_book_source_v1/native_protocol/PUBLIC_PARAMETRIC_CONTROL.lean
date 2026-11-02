import UEOT
namespace IndependentConflictParametricControl
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly UEOT.V3.PathError
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.ViabilityKernel
open ConflictParametricSource ConflictParametricControl
noncomputable section
abbrev theta : ℝ := 7/11
theorem h0 : 0≤theta := by norm_num
theorem h1 : theta≤1 := by norm_num
def memory3 : (causalPolicy theta h0 h1).Memory 3 :=
 ((((false,true),(true,(true,true))),(false,(false,false))),(false,(false,true)))
theorem returned_history_value :
 CausalPolicy.infiniteValue (causalPolicy theta h0 h1) M memory3=(14/11:ℝ) := by
 rw [full_history_infinite_value];norm_num [theta]
theorem source_stationary_value (x : State) :
 M.policyValue (policy theta h0 h1) x=(14/11:ℝ) := by
 rw [stationary_policy_value];norm_num [theta]
theorem original_action_strict_gap (x : State) :
 M.qValue M.optimalValue x false=2 ∧ M.qValue M.optimalValue x true=1 := by
 rw [unrestricted_optimal_value];simp [unrestricted_q]
theorem every_original_causal (pi : CausalPolicy State (fun _=>Bool)) {t : ℕ} (h : pi.Memory t) :
 CausalPolicy.infiniteValue pi M h≤2 :=unrestricted_all_causal pi h
theorem original_attainment :
 CausalPolicy.infiniteValue (greedyPolicy M) M (t:=3) (false,true)=2 :=unrestricted_actual_attainment _
def outsideTrue : viableSourceAction M conflictSurvivalRegion (false,false) :=
 ⟨true, by simp [conflictSurvivalRegion]⟩
def outsideFalse : viableSourceAction M conflictSurvivalRegion (false,false) :=
 ⟨false, by simp [conflictSurvivalRegion]⟩
theorem outside_both_allowed_but_only_false_optimal :
 R.qValue R.optimalValue (false,false) outsideTrue=0 ∧
 R.qValue R.optimalValue (false,false) outsideFalse=2 := by
 rw [restricted_optimal_value,restricted_q,restricted_q];simp [outsideTrue,outsideFalse]
theorem current_values_greedy :
 R.optimalValue (false,false)=2 ∧ R.optimalValue (true,true)=0 ∧
 (R.greedyAction (false,false)).val=false ∧ (R.greedyAction (true,true)).val=true := by
 rw [restricted_optimal_value,restricted_greedy,restricted_greedy];norm_num [restrictedValue]
theorem safe_false_illegal :
 ¬∃a : viableSourceAction M conflictSurvivalRegion (true,true), a.val=false := by
 rintro ⟨a,ha⟩
 have hh:=(restricted_action_iff _ _).mp a.property rfl
 rw [ha] at hh;cases hh
theorem every_restricted_causal (pi : CausalPolicy State (viableSourceAction M conflictSurvivalRegion))
 {t : ℕ} (h : pi.Memory t) :
 CausalPolicy.infiniteValue pi R h≤2*(if (pi.current h).1 then 0 else 1) :=restricted_all_causal pi h
theorem restricted_attainment_safe :
 CausalPolicy.infiniteValue (greedyPolicy R) R (t:=3) (true,true)=0 := by
 rw [restricted_actual_attainment];norm_num [restrictedValue]
theorem restricted_attainment_outside :
 CausalPolicy.infiniteValue (greedyPolicy R) R (t:=3) (false,true)=2 := by
 rw [restricted_actual_attainment];norm_num [restrictedValue]
theorem actual_D_comes_from_same_original_P (x : State) :
 restrictedRow x=M.transitionPMF x x.1 :=restrictedRow_original x
theorem invariant_7_11 :
 (mu theta h0 h1).bind restrictedRow=mu theta h0 h1 :=all_mixtures_invariant _ _ _
theorem ALL_invariants (nu : PMF State) :
 nu.bind restrictedRow=nu ↔ ∃t : ℝ,∃h0 : 0≤t,∃h1 : t≤1,nu=mu t h0 h1 :=invariant_iff_mixture nu
theorem mixture_coordinates (y : State) :
 (mu theta h0 h1 y).toReal=(4/11:ℝ)*(mu 0 (by norm_num) (by norm_num) y).toReal+
 (7/11:ℝ)*(mu 1 (by norm_num) (by norm_num) y).toReal :=by
 convert actual_mixture_coordinates theta h0 h1 y using 1; norm_num [theta]
theorem noncontracting : UEOT.V3.FiniteDobrushin.dobrushinAlpha D D_stochastic=1 :=full_closed_loop_dobrushin
theorem ALL_safe_action_paths (T : ℕ) :
 actionPath (PMF.pure (true,true)) restrictedHistoryPolicy T=
 actionPath (PMF.pure (true,true)) (historyPolicy 0 (by norm_num) (by norm_num)) T :=by
 apply safe_initial_full_action_path
 intro x hx
 have he : x=(true,true):=by simpa only [PMF.mem_support_pure_iff] using hx
 rw [he];rfl
theorem no_unsafe_extension :
 actionPath (PMF.pure (false,false)) restrictedHistoryPolicy 1≠
 actionPath (PMF.pure (false,false)) (historyPolicy 0 (by norm_num) (by norm_num)) 1 :=unsafe_initial_full_action_path_ne
end
#print axioms h0
#print axioms h1
#print axioms returned_history_value
#print axioms source_stationary_value
#print axioms original_action_strict_gap
#print axioms every_original_causal
#print axioms original_attainment
#print axioms outside_both_allowed_but_only_false_optimal
#print axioms current_values_greedy
#print axioms safe_false_illegal
#print axioms every_restricted_causal
#print axioms restricted_attainment_safe
#print axioms restricted_attainment_outside
#print axioms actual_D_comes_from_same_original_P
#print axioms invariant_7_11
#print axioms ALL_invariants
#print axioms mixture_coordinates
#print axioms noncontracting
#print axioms ALL_safe_action_paths
#print axioms no_unsafe_extension
end IndependentConflictParametricControl
