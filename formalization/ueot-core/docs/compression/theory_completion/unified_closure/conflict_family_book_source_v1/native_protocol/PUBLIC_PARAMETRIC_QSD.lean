import UEOT
namespace IndependentConflictStationaryQSD
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open ConflictParametricSource
open scoped BigOperators
noncomputable section

def theta : ℝ:=5/13
theorem theta_nonnegative : 0≤theta :=by norm_num [theta]
theorem theta_at_most_one : theta≤1 :=by norm_num [theta]
theorem theta_less_one : theta<1 :=by norm_num [theta]

def eta : stdSimplex ℝ Bool:=⟨(fun b=>if b then 5/7 else 2/7),
  (by intro b;cases b <;> norm_num),(by norm_num)⟩
def etaPMF : PMF Bool:=FiniteProbabilityRow.ofRealRow eta.val (stdSimplex.zero_le eta) (stdSimplex.sum_eq_one eta)
theorem etaPMF_real (b : Bool) : (etaPMF b).toReal=if b then (5/7:ℝ) else 2/7 :=
  FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ _
theorem eta_not_fair : eta.val≠(fun _=> (1/2:ℝ)) :=by
  intro he
  have hx:=congrFun he false
  norm_num [eta] at hx

def sourceInitial : PMF State:=etaPMF.map (fun b=>(true,b))

end
end IndependentConflictStationaryQSD

namespace IndependentConflictQSD
open MeasureTheory ProbabilityTheory
open UEOT.V3.CoreOperationalAssembly UEOT.V3.FiniteDiscountedControl UEOT.V3.PathError UEOT.V3.QSDPerron
open UEOT.V3.Compression.TheoryCompletion UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open ConflictParametricSource ConflictParametricQSD SameSourceConditionedTerminalCheck SameSourceKilledPathCheck
open IndependentConflictStationaryQSD
open scoped BigOperators
noncomputable section
local instance : MeasurableSpace State:=⊤
local instance : DecidableEq K:=Classical.decEq K

def etaSafe : PMF K:=etaPMF.map safeEquiv

theorem etaSafe_real (u : Bool) : (etaSafe (safeEquiv u)).toReal=if u then (5/7:ℝ) else 2/7 :=by
 cases u <;> simp [etaSafe,PMF.map_apply,tsum_fintype,etaPMF_real]

theorem etaSafe_not_fair : etaSafe≠fairPMF :=by
 intro he
 have hx:=congrArg (fun p : PMF K=>(p (safeEquiv false)).toReal) he
 rw [etaSafe_real,fairPMF_real] at hx
 norm_num [fair] at hx

theorem same_registered_K : K=conflictSurvivalRegion :=rfl

theorem actual_raw_killed : Q theta theta_nonnegative theta_at_most_one=
 killedMatrix M (policy theta theta_nonnegative theta_at_most_one) K :=rfl

theorem actual_Bool_to_K (u v : Bool) :
 Q theta theta_nonnegative theta_at_most_one (safeEquiv u) (safeEquiv v)=
   (closedRow theta theta_nonnegative theta_at_most_one (true,u) (true,v)).toReal :=by
 rw [killed_embed,killed_actual]

theorem exact_source_entry : Q theta theta_nonnegative theta_at_most_one (safeEquiv false) (safeEquiv true)=(4/13:ℝ) :=by
 rw [Q_entry]
 norm_num [theta,rho]

theorem etaSafe_source_initial : etaSafe.map Subtype.val=sourceInitial :=by
 rw [etaSafe,PMF.map_comp]
 rfl

theorem full_source_identity (T : ℕ) :
 actualLaw theta theta_nonnegative theta_at_most_one etaSafe T=
 causalLaw sourceInitial (riskMicroControlKernel id (fun _=>M.transitionPMF)
   (historyPolicy theta theta_nonnegative theta_at_most_one)) T :=by
 unfold actualLaw
 rw [etaSafe_source_initial,actual_policy_history]

theorem actual_any_initial_source (nu : PMF K) (n : ℕ) :
 (actualLaw theta theta_nonnegative theta_at_most_one nu (n+1)).toMeasure.real {h |
   ¬riskEverFailure (fun x=>x∉K) (n+1) h}=(8/13:ℝ)^(n+1) :=by
 rw [actual_survival_mass]
 norm_num [rho,theta]

theorem actual_T3_nonqsd_killed (u : Bool) :
 rowApply (fun x=>(etaSafe x).toReal) ((Q theta theta_nonnegative theta_at_most_one)^3) (safeEquiv u)=(256/2197:ℝ) :=by
 rw [show 3=2+1 from rfl,arbitrary_positive_power _ _ _ _ (coverage_sum_toReal etaSafe)]
 norm_num [rho,theta,fair]

theorem actual_T3_survival :
 (actualLaw theta theta_nonnegative theta_at_most_one etaSafe 3).toMeasure.real {h |
   ¬riskEverFailure (fun x=>x∉K) 3 h}=(512/2197:ℝ) :=by
 have hh:=actual_any_initial_source etaSafe 2
 norm_num at hh
 exact hh

theorem actual_T3_joint_endpoint :
 (actualLaw theta theta_nonnegative theta_at_most_one etaSafe 3).toMeasure.real {h |
   ¬riskEverFailure (fun x=>x∉K) 3 h ∧ riskLastState 3 h=(safeEquiv true).val}=(256/2197:ℝ) :=by
 rw [show 3=2+1 from rfl,actual_terminal_mass]
 norm_num [rho,theta,fair]

theorem actual_any_initial_filtered (nu : PMF K) (n : ℕ) :
 actualConditionedTerminal M id (fun _ : State=>actionLaw theta theta_nonnegative theta_less_one.le)
   (nu.map Subtype.val) K (n+1) (actual_survival_pos theta theta_nonnegative theta_less_one nu n)=
   fairPMF.map Subtype.val :=actual_conditioned_terminal theta theta_nonnegative theta_less_one nu n

theorem true_original_GOa : KilledQSDGOA (Q theta theta_nonnegative theta_less_one.le) fair (rho theta) :=
 actual_qsd_goa theta theta_nonnegative theta_less_one

theorem true_BiEigen_and_Doob (u v : K) :
 UEOT.V3.Compression.PositiveEigenstructure.hTransform (biData theta theta_nonnegative theta_less_one).right u v=(1/2:ℝ) :=
 actual_doob_fair theta theta_nonnegative theta_less_one u v

theorem original_Eigen_stationary_consumer (v : K) :
 UEOT.V3.Compression.PositiveEigenstructure.rowApply
   (UEOT.V3.Compression.PositiveEigenstructure.invariantWeight (biData theta theta_nonnegative theta_less_one))
   (UEOT.V3.Compression.PositiveEigenstructure.hTransform (biData theta theta_nonnegative theta_less_one).right) v=
   UEOT.V3.Compression.PositiveEigenstructure.invariantWeight (biData theta theta_nonnegative theta_less_one) v :=
 actual_doob_invariant theta theta_nonnegative theta_less_one v

theorem original_GOa_all_T_including_zero (T : ℕ) (v : K) :
 rowApply fair ((Q theta theta_nonnegative theta_less_one.le)^T) v/rho theta^T=fair v :=
 original_goa_all_steps theta theta_nonnegative theta_less_one T v

theorem Doob_is_actual_theta_zero :
 UEOT.V3.Compression.PositiveEigenstructure.hTransform (biData theta theta_nonnegative theta_less_one).right=
   Q 0 le_rfl (by norm_num) :=doob_eq_actual_safe theta theta_nonnegative theta_less_one

theorem zero_time_nonqsd :
 rowApply (fun x=>(etaSafe x).toReal) ((Q theta theta_nonnegative theta_at_most_one)^0) (safeEquiv false)=(2/7:ℝ) :=by
 rw [time_zero_row,etaSafe_real]
 rfl

theorem zero_time_conditional_keeps_input :
 actualConditionedTerminal M id (fun _ : State=>actionLaw theta theta_nonnegative theta_at_most_one)
   (etaSafe.map Subtype.val) K 0 (by
      change 0<(actualLaw theta theta_nonnegative theta_at_most_one etaSafe 0).toMeasure.real _
      rw [actual_time_zero_mass];norm_num)=etaSafe.map Subtype.val :=
 actual_conditioned_time_zero _ _ _ _

theorem input_after_embedding_not_fair : etaSafe.map Subtype.val≠fairPMF.map Subtype.val :=by
 intro hh
 have retract (p : PMF K) : (p.map Subtype.val).map (fun x : State=>safeEquiv x.2)=p :=by
  rw [PMF.map_comp]
  have hfun : ((fun x : State=>safeEquiv x.2) ∘ Subtype.val)=id :=by
   funext x
   exact safeEquiv.apply_symm_apply x
  rw [hfun,PMF.map_id]
 have he:=congrArg (fun p : PMF State=>p.map (fun x : State=>safeEquiv x.2)) hh
 rw [retract,retract] at he
 exact etaSafe_not_fair he

theorem theta_one_raw_zero (x y : K) : Q 1 (by norm_num) le_rfl x y=0 :=by rw [Q_entry];norm_num [rho]

theorem theta_one_no_positivity (n : ℕ) :
 ¬0<(actualLaw 1 (by norm_num) le_rfl etaSafe (n+1)).toMeasure.real {h |
   ¬riskEverFailure (fun x=>x∉K) (n+1) h} :=theta_one_no_positive_conditioning _ _

theorem theta_one_no_positive_QSD (q : K→ℝ) (r : ℝ) : ¬KilledQSDGOA (Q 1 (by norm_num) le_rfl) q r :=theta_one_no_qsd _ _

theorem theta_zero_survives (n : ℕ) :
 (actualLaw 0 le_rfl (by norm_num) etaSafe (n+1)).toMeasure.real {h |
   ¬riskEverFailure (fun x=>x∉K) (n+1) h}=1 :=theta_zero_survival_one _ _

theorem book_delta_same_source : (PMF.pure (safeEquiv false)).map Subtype.val=ConflictParametricStationary.initial :=by
 rw [PMF.pure_map]
 rfl

end
#print axioms etaSafe_real
#print axioms etaSafe_not_fair
#print axioms same_registered_K
#print axioms actual_raw_killed
#print axioms actual_Bool_to_K
#print axioms exact_source_entry
#print axioms etaSafe_source_initial
#print axioms full_source_identity
#print axioms actual_any_initial_source
#print axioms actual_T3_nonqsd_killed
#print axioms actual_T3_survival
#print axioms actual_T3_joint_endpoint
#print axioms actual_any_initial_filtered
#print axioms true_original_GOa
#print axioms true_BiEigen_and_Doob
#print axioms original_Eigen_stationary_consumer
#print axioms original_GOa_all_T_including_zero
#print axioms Doob_is_actual_theta_zero
#print axioms zero_time_nonqsd
#print axioms zero_time_conditional_keeps_input
#print axioms input_after_embedding_not_fair
#print axioms theta_one_raw_zero
#print axioms theta_one_no_positivity
#print axioms theta_one_no_positive_QSD
#print axioms theta_zero_survives
#print axioms book_delta_same_source
end IndependentConflictQSD
