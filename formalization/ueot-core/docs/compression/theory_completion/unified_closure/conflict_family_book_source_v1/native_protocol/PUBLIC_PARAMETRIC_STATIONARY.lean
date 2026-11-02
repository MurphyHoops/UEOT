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

namespace IndependentConflictStationary
open UEOT.V3.CoreOperationalAssembly UEOT.V3.FiniteDiscountedControl UEOT.V3.PathError
open UEOT.V3.Compression.TheoryCompletion UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open ConflictParametricSource ConflictParametricStationary
open IndependentConflictStationaryQSD
open UEOT.V3.FiniteCesaroInvariant
open Filter Topology
noncomputable section
local instance : DecidableEq State:=Classical.decEq State
local instance : MeasurableSpace State:=⊤
local instance : MeasurableSingletonClass State:=⟨fun _=>trivial⟩

theorem arbitrary_initial_one_step (p : PMF State) :
 p.bind (closedRow theta theta_nonnegative theta_at_most_one)=mu theta theta_nonnegative theta_at_most_one :=actual_one_step _ _ _ _

theorem original_full_action_source (p : PMF State) (t : ℕ) :
 (causalLaw p (riskMicroControlKernel id (fun _=>M.transitionPMF)
   (historyPolicy theta theta_nonnegative theta_at_most_one)) (t+1)).map (riskLastState (t+1))=
   mu theta theta_nonnegative theta_at_most_one :=original_action_marginal_after_one _ _ _ _ _

theorem off_carrier_start_actual_source : actualMarginal theta theta_nonnegative theta_at_most_one (PMF.pure (false,true)) 1=
 mu theta theta_nonnegative theta_at_most_one :=actual_marginal_after_one _ _ _ _ 0

theorem initial_time_preserved : actualMarginal theta theta_nonnegative theta_at_most_one initial 0=initial :=by
 change initial.map id=initial
 exact PMF.map_id _

theorem initial_is_not_stationary : initial≠mu theta theta_nonnegative theta_at_most_one :=by
 intro hh
 have he:=congrArg (fun p : PMF State=>(p (true,false)).toReal) hh
 rw [mu_real] at he
 norm_num [initial,PMF.pure_apply,theta] at he

theorem cesaro_N1_initial : actualCesaro theta theta_nonnegative theta_at_most_one 0=initial :=by
 apply PMF.ext
 intro y
 apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
 rw [cesaro_exact]
 norm_num

theorem cesaro_N5_atom : (actualCesaro theta theta_nonnegative theta_at_most_one 4 (true,false)).toReal=(29/65:ℝ) :=by
 rw [cesaro_exact,mu_real]
 norm_num [theta,initial,PMF.pure_apply]

theorem cesaro_N5_exact_tv : UEOT.V3.TotalVariation.tvDist
 (actualCesaro theta theta_nonnegative theta_at_most_one 4).toMeasure
 (mu theta theta_nonnegative theta_at_most_one).toMeasure=(9/65:ℝ) :=by
 rw [cesaro_tv_exact]
 norm_num [theta]

theorem cesaro_N1_exact_tv : UEOT.V3.TotalVariation.tvDist
 (actualCesaro theta theta_nonnegative theta_at_most_one 0).toMeasure
 (mu theta theta_nonnegative theta_at_most_one).toMeasure=(9/13:ℝ) :=by
 rw [cesaro_tv_exact]
 norm_num [theta]

theorem cesaro_N5_residual :
 (Matrix.vecMul (fun y=>(actualCesaro theta theta_nonnegative theta_at_most_one 4 y).toReal) (P theta)-
   (fun y=>(actualCesaro theta theta_nonnegative theta_at_most_one 4 y).toReal)) (true,false)=(-9/65:ℝ) :=by
 rw [cesaro_residual]
 simp only [mu_real]
 norm_num [theta,initial,PMF.pure_apply]

theorem actual_endpoint_zero_TV : UEOT.V3.TotalVariation.tvDist
 (actualCesaro 0 (by norm_num) (by norm_num) 0).toMeasure
 (mu 0 (by norm_num) (by norm_num)).toMeasure=(1/2:ℝ) :=by rw [cesaro_tv_exact];norm_num

theorem actual_endpoint_one_TV : UEOT.V3.TotalVariation.tvDist
 (actualCesaro 1 (by norm_num) (by norm_num) 0).toMeasure
 (mu 1 (by norm_num) (by norm_num)).toMeasure=1 :=by rw [cesaro_tv_exact];norm_num

theorem original_GOa_actual_mu :
 CesaroLimitGOA (P theta) (matrix_stochastic theta theta_nonnegative theta_at_most_one)
   (ofPMF initial) (ofPMF (mu theta theta_nonnegative theta_at_most_one)) :=by
 obtain ⟨nu,phi,hmono,hlim⟩ :=(p_goa_01 (P theta) (matrix_stochastic theta theta_nonnegative theta_at_most_one) (ofPMF initial)).1
 have hi :=(p_goa_01 (P theta) (matrix_stochastic theta theta_nonnegative theta_at_most_one) (ofPMF initial)).2 nu phi hmono hlim
 have he : nu=ofPMF (mu theta theta_nonnegative theta_at_most_one) :=by
  apply Subtype.ext
  exact hi.symm.trans (normalized_row_step theta theta_nonnegative theta_at_most_one nu.val (stdSimplex.sum_eq_one nu))
 rw [he] at hlim
 exact ⟨phi,hmono,hlim⟩

theorem original_GOa_invariant_consumer :
 InvariantLawGOA (P theta) (matrix_stochastic theta theta_nonnegative theta_at_most_one)
   (ofPMF (mu theta theta_nonnegative theta_at_most_one)) :=
 cesaroLimitGOA_is_invariant _ _ _ _ original_GOa_actual_mu

end
#print axioms arbitrary_initial_one_step
#print axioms original_full_action_source
#print axioms off_carrier_start_actual_source
#print axioms initial_time_preserved
#print axioms initial_is_not_stationary
#print axioms cesaro_N1_initial
#print axioms cesaro_N5_atom
#print axioms cesaro_N5_exact_tv
#print axioms cesaro_N1_exact_tv
#print axioms cesaro_N5_residual
#print axioms actual_endpoint_zero_TV
#print axioms actual_endpoint_one_TV
#print axioms original_GOa_actual_mu
#print axioms original_GOa_invariant_consumer
end IndependentConflictStationary
