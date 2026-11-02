import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSupportViability
import UEOT.V3.FiniteDiscountedGreedy

/-!
Original promise: the parameterized four-state source has actual unrestricted and safety-restricted numerical optima.
Existing source: the original nonzero-reward model M, its actual PMF mixture, and the derived viable action subtype.
Reduced premise: compute the value and unique greedy actions of M and of its actual viableRestrictedModel.
Family: every theta in [0,1]; the restricted action class keeps both original actions outside K.
Consumers: arbitrary causal-policy domination, full restricted closed-loop invariant laws, and safe-initial path transport.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricControl

open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly UEOT.V3.PathError
open UEOT.V3.ViabilityKernel
open ConflictParametricSource FiniteActionRealizabilityCheck
open Filter Topology
open scoped BigOperators
noncomputable section
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSingletonClass State := ⟨fun _ => trivial⟩

theorem stationary_policy_value (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    M.policyValue (policy theta h0 h1) = fun _ => 2*theta := by
  apply Eq.symm
  apply M.policyValue_unique
  funext x
  simp only [Model.policyBellman, Model.policyReward, Model.policyExpect]
  have he : (∑ y, M.policyTransition (policy theta h0 h1) x y * (2*theta))=2*theta := by
    rw [←Finset.sum_mul, M.policyTransition_sum_one, one_mul]
  rw [he, discount_eq]
  simp [policy, SourcePolicyPathBridgeCheck.liftedStationaryPolicy, actionLaw_real,
    reward_eq, actionWeight]
  ring

theorem full_history_truncated_eq (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    ∀ k {t : ℕ} (h : (causalPolicy theta h0 h1).Memory t),
      CausalPolicy.truncatedValue (causalPolicy theta h0 h1) M k h =
        CausalPolicy.truncatedValue (policy theta h0 h1).toCausalPolicy M k
          (t:=t) (riskLastState t h) := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro t h
    simp only [CausalPolicy.truncatedValue_succ]
    apply Finset.sum_congr rfl
    intro a _
    congr 2
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    rw [ih]
    rfl

theorem full_history_infinite_value (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {t : ℕ} (h : (causalPolicy theta h0 h1).Memory t) :
    CausalPolicy.infiniteValue (causalPolicy theta h0 h1) M h = 2*theta := by
  have he : CausalPolicy.infiniteValue (causalPolicy theta h0 h1) M h =
      CausalPolicy.infiniteValue (policy theta h0 h1).toCausalPolicy M
        (t:=t) (riskLastState t h) := by
    apply tendsto_nhds_unique
      (CausalPolicy.truncatedValue_tendsto_infiniteValue (causalPolicy theta h0 h1) M h)
    exact (CausalPolicy.truncatedValue_tendsto_infiniteValue
      (policy theta h0 h1).toCausalPolicy M (t:=t) (riskLastState t h)).congr'
        (Eventually.of_forall fun k => (full_history_truncated_eq theta h0 h1 k h).symm)
  rw [he, M.stationary_infiniteValue_eq_policyValue, stationary_policy_value]

theorem unrestricted_q (x : State) (a : Bool) :
    M.qValue (fun _ => 2) x a = if a then (1 : ℝ) else 2 := by
  have he : M.expect x a (fun _ => 2)=2 := by
    simp only [Model.expect]
    rw [←Finset.sum_mul, M.transition_sum_one, one_mul]
  rw [Model.qValue, he, reward_eq, discount_eq]
  cases a <;> norm_num

theorem unrestricted_optimal_value : M.optimalValue = fun _ => 2 := by
  apply Eq.symm
  apply M.fixedPoint_unique
  funext x
  unfold Model.bellman
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    rw [unrestricted_q]
    cases a <;> norm_num
  · have hh:=Finset.le_sup' (fun a : Bool=>M.qValue (fun _=>2) x a) (Finset.mem_univ false)
    simpa only [unrestricted_q, Bool.false_eq_true, if_false] using hh

theorem unrestricted_greedy (x : State) : M.greedyAction x=false := by
  have hh:=M.greedyAction_spec x
  rw [unrestricted_optimal_value, unrestricted_q] at hh
  cases ha : M.greedyAction x <;> simp_all

theorem unrestricted_optimal_action_iff (x : State) (a : Bool) :
    M.qValue M.optimalValue x a=M.optimalValue x ↔ a=false := by
  rw [unrestricted_optimal_value,unrestricted_q]
  cases a <;> norm_num

theorem unrestricted_all_causal (pi : CausalPolicy State (fun _ => Bool))
    {t : ℕ} (h : pi.Memory t) : CausalPolicy.infiniteValue pi M h ≤ 2 := by
  simpa only [unrestricted_optimal_value] using CausalPolicy.infiniteValue_le_optimal pi M h

theorem source_stays_iff (x : State) (a : Bool) :
    StaysIn (M.transitionPMF x a) conflictSurvivalRegion ↔ a=true := by
  change StaysIn (M.transitionPMF x a) {y | y.1=true} ↔ a=true
  rw [frozen_pmf_staysIn_iff_real_zero_outside]
  constructor
  · intro hh
    cases a with
    | false =>
      have hz:=hh (false,false) (by simp)
      rw [transition_eq] at hz
      norm_num at hz
    | true => rfl
  · intro ha y hy
    subst a
    rcases y with ⟨b,u⟩
    cases b with
    | false => simp [transition_eq]
    | true => exact False.elim (hy rfl)

instance restrictedNonempty (x : State) : Nonempty (viableSourceAction M conflictSurvivalRegion x) :=
  exists_viable_source_action M conflictSurvivalRegion conflict_region_is_actual_pmf_viability_fixed x

def R := viableRestrictedModel M conflictSurvivalRegion conflict_region_is_actual_pmf_viability_fixed

theorem restricted_action_iff (x : State) (a : Bool) :
    (x∈conflictSurvivalRegion → StaysIn (M.transitionPMF x a) conflictSurvivalRegion) ↔
      (x.1=true → a=true) := by
  change (x.1=true → StaysIn (M.transitionPMF x a) conflictSurvivalRegion) ↔ _
  rw [source_stays_iff]

def restrictedSelector (x : State) : viableSourceAction M conflictSurvivalRegion x :=
  ⟨x.1, fun hx => (source_stays_iff x x.1).2 hx⟩

def restrictedValue (x : State) : ℝ := 2*(if x.1 then 0 else 1)

theorem restricted_transition (x : State) (a : viableSourceAction M conflictSurvivalRegion x) (y : State) :
    R.transition x a y = M.transition x a.val y := rfl
theorem restricted_reward (x : State) (a : viableSourceAction M conflictSurvivalRegion x) :
    R.reward x a = M.reward x a.val := rfl

theorem restricted_q (x : State) (a : viableSourceAction M conflictSurvivalRegion x) :
    R.qValue restrictedValue x a = if a.val then (0 : ℝ) else 2 := by
  simp only [Model.qValue, Model.expect, restricted_transition, restricted_reward, reward_eq]
  change (if a.val then 0 else 1)+(1/2 : ℝ)*
    (∑ y : State, M.transition x a.val y * restrictedValue y)=_
  cases ha : a.val <;> norm_num [transition_eq,restrictedValue,Fintype.sum_prod_type]

theorem restricted_optimal_value : R.optimalValue=restrictedValue := by
  apply Eq.symm
  apply R.fixedPoint_unique
  funext x
  unfold Model.bellman
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    rw [restricted_q]
    have hs:=a.property
    rw [restricted_action_iff] at hs
    cases hb : x.1 with
    | false => cases ha : a.val <;> norm_num [restrictedValue,hb]
    | true => rw [hs hb]; norm_num [restrictedValue,hb]
  · have hh:=Finset.le_sup' (fun a : viableSourceAction M conflictSurvivalRegion x => R.qValue restrictedValue x a)
      (Finset.mem_univ (restrictedSelector x))
    rw [restricted_q] at hh
    have he : (if (restrictedSelector x).val then (0 : ℝ) else 2)=restrictedValue x := by
      cases hb : x.1 <;> norm_num [restrictedSelector,restrictedValue,hb]
    rw [he] at hh
    exact hh

theorem restricted_greedy (x : State) : (R.greedyAction x).val=x.1 := by
  have hh:=R.greedyAction_spec x
  rw [restricted_optimal_value,restricted_q] at hh
  have hs:=(R.greedyAction x).property
  rw [restricted_action_iff] at hs
  cases hb : x.1 with
  | false =>
    cases ha : (R.greedyAction x).val with
    | false => rfl
    | true => norm_num [restrictedValue,hb,ha] at hh
  | true => exact hs hb

theorem restricted_optimal_action_iff (x : State) (a : viableSourceAction M conflictSurvivalRegion x) :
    R.qValue R.optimalValue x a=R.optimalValue x ↔ a.val=x.1 := by
  rw [restricted_optimal_value,restricted_q]
  cases hb : x.1 <;> cases ha : a.val <;> norm_num [restrictedValue,hb]

theorem restricted_all_causal (pi : CausalPolicy State (viableSourceAction M conflictSurvivalRegion))
    {t : ℕ} (h : pi.Memory t) :
    CausalPolicy.infiniteValue pi R h ≤ 2*(if (pi.current h).1 then 0 else 1) := by
  simpa only [restricted_optimal_value,restrictedValue] using CausalPolicy.infiniteValue_le_optimal pi R h

theorem unrestricted_actual_attainment {t : ℕ} (x : State) :
    CausalPolicy.infiniteValue (greedyPolicy M) M (t:=t) x=2 := by
  rw [greedy_infiniteValue_eq_optimal,unrestricted_optimal_value]

theorem restricted_actual_attainment {t : ℕ} (x : State) :
    CausalPolicy.infiniteValue (greedyPolicy R) R (t:=t) x=restrictedValue x := by
  rw [greedy_infiniteValue_eq_optimal,restricted_optimal_value]

/-- The full-domain closed loop is the ACTUAL restricted Bellman greedy policy. -/
def restrictedPolicy : StationaryPolicy (viableSourceAction M conflictSurvivalRegion) :=
  StationaryPolicy.ofSelector R.greedyAction

def restrictedRow (x : State) : PMF State := policyTransitionPMF R restrictedPolicy x
def D : Matrix State State ℝ := policyMatrix R restrictedPolicy

theorem restrictedRow_original (x : State) : restrictedRow x=M.transitionPMF x x.1 := by
  classical
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [restrictedRow,policyTransitionPMF_apply_toReal, Model.transitionPMF_apply_toReal,
    Model.policyTransition,restrictedPolicy,StationaryPolicy.ofSelector,restricted_transition,
    ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,restricted_greedy]

theorem restrictedRow_real (x y : State) :
    (restrictedRow x y).toReal=if y.1=x.1 then (1/2 : ℝ) else 0 := by
  rw [restrictedRow_original,transition_real]

theorem D_eq (x y : State) : D x y=if y.1=x.1 then (1/2 : ℝ) else 0 := by
  have hh:=restrictedRow_real x y
  simpa only [restrictedRow,policyTransitionPMF_apply_toReal,D,policyMatrix] using hh

theorem restricted_bind_real (nu : PMF State) (b u : Bool) :
    ((nu.bind restrictedRow) (b,u)).toReal=
      ((nu (b,false)).toReal+(nu (b,true)).toReal)/2 := by
  change realRow (actionMixture restrictedRow nu) (b,u)=_
  rw [realRow_actionMixture]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realRow, restrictedRow_real]
  cases b <;> simp [Fintype.sum_prod_type] <;> ring

theorem all_mixtures_invariant (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) :
    (mu theta h0 h1).bind restrictedRow=mu theta h0 h1 := by
  apply PMF.ext
  rintro ⟨b,u⟩
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [restricted_bind_real,mu_real,mu_real,mu_real]
  cases b <;> norm_num

theorem actual_mixture_coordinates (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) (y : State) :
    (mu theta h0 h1 y).toReal=
      (1-theta)*(mu 0 (by norm_num) (by norm_num) y).toReal+
        theta*(mu 1 (by norm_num) (by norm_num) y).toReal := by
  rw [mu_real,mu_real,mu_real]
  cases y.1 <;> norm_num <;> ring

/-- Every invariant probability is one of the complete two-fiber mixtures;
neither unique full-domain GOA nor collapse to the safe fiber is asserted. -/
theorem invariant_iff_mixture (nu : PMF State) :
    nu.bind restrictedRow=nu ↔ ∃theta : ℝ,∃h0 : 0≤theta,∃h1 : theta≤1,nu=mu theta h0 h1 := by
  constructor
  · intro hn
    have heq (b : Bool) : (nu (b,false)).toReal=(nu (b,true)).toReal := by
      have hf:=congrArg (fun p : PMF State=>(p (b,false)).toReal) hn
      have ht:=congrArg (fun p : PMF State=>(p (b,true)).toReal) hn
      rw [restricted_bind_real] at hf ht
      linarith
    have hsum:=coverage_sum_toReal nu
    simp only [Fintype.sum_prod_type] at hsum
    simp at hsum
    let theta : ℝ:=(nu (false,false)).toReal+(nu (false,true)).toReal
    have h0 : 0≤theta:=add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have h1 : theta≤1 := by
      dsimp only [theta]
      linarith [show 0≤(nu (true,false)).toReal from ENNReal.toReal_nonneg,
        show 0≤(nu (true,true)).toReal from ENNReal.toReal_nonneg]
    refine ⟨theta,h0,h1,?_⟩
    apply PMF.ext
    rintro ⟨b,u⟩
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    rw [mu_real]
    have hf:=heq false
    have ht:=heq true
    cases b <;> cases u <;> simp only [Bool.false_eq_true,if_false,if_true] <;> dsimp only [theta] <;> linarith
  · rintro ⟨theta,h0,h1,rfl⟩
    exact all_mixtures_invariant theta h0 h1

theorem invariant_not_unique :
    mu 0 (by norm_num) (by norm_num)≠mu 1 (by norm_num) (by norm_num) := by
  intro hn
  have he:=congrArg (fun p : PMF State=>(p (false,false)).toReal) hn
  rw [mu_real,mu_real] at he
  norm_num at he

theorem D_stochastic : D∈Matrix.rowStochastic ℝ State :=
  policyMatrix_rowStochastic R restrictedPolicy

theorem full_closed_loop_dobrushin : UEOT.V3.FiniteDobrushin.dobrushinAlpha D D_stochastic=1 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro z _
    unfold UEOT.V3.FiniteDobrushin.rowTV FiniteProbabilityRow.tvDist
    exact UEOT.V3.TotalVariation.tvDist_le_one _ _
  · have hh:=UEOT.V3.FiniteDobrushin.rowTV_le_dobrushinAlpha D D_stochastic (false,false) (true,false)
    have hr : UEOT.V3.FiniteDobrushin.rowTV D D_stochastic (false,false) (true,false)=1 := by
      unfold UEOT.V3.FiniteDobrushin.rowTV FiniteProbabilityRow.tvDist
      rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
      have hrow (x y : State) : ((UEOT.V3.FiniteDobrushin.rowPMF D D_stochastic x) y).toReal=
          if y.1=x.1 then (1/2 : ℝ) else 0 :=
        (UEOT.V3.FiniteDobrushin.rowPMF_toReal D D_stochastic x y).trans (D_eq x y)
      simp_rw [hrow]
      norm_num [Fintype.sum_prod_type]
    rwa [hr] at hh

theorem actionLaw_zero : actionLaw 0 (by norm_num) (by norm_num)=PMF.pure true := by
  apply PMF.ext
  intro a
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [actionLaw_real]
  cases a <;> simp [actionWeight,PMF.pure_apply]

/-- Project the ACTUAL restricted greedy action into the original action type. -/
def restrictedHistoryPolicy : ∀ t, CausalHistory State (Bool × State) t → PMF Bool :=
  SourcePolicyPathBridgeCheck.observationMarkovPolicy
    (fun x => PMF.pure (R.greedyAction x).val)

def actionPath (p : PMF State)
    (pi : ∀ t, CausalHistory State (Bool × State) t → PMF Bool) (T : ℕ) :=
  causalLaw p (riskMicroControlKernel id (fun _ => M.transitionPMF) pi) T

theorem zero_path_current_safe (p : PMF State) (hp : StaysIn p conflictSurvivalRegion)
    (t : ℕ) (h : CausalHistory State (Bool × State) t)
    (hh : h∈(actionPath p (historyPolicy 0 (by norm_num) (by norm_num)) t).support) :
    (riskLastState t h).1=true := by
  cases t with
  | zero => exact hp hh
  | succ t =>
    rcases h with ⟨h,a,y⟩
    have hf:=(SupportViabilityClosure.mem_microLaw_succ_support_iff p id (fun _ => M.transitionPMF)
      (historyPolicy 0 (by norm_num) (by norm_num)) t h a y).mp hh
    have ha : a=true := by simpa only [historyPolicy,actionLaw_zero,PMF.mem_support_pure_iff] using hf.2.1
    subst a
    exact ((source_stays_iff (riskLastState t h) true).2 rfl) hf.2.2

private theorem supported_zero_kernel_eq (p : PMF State) (hp : StaysIn p conflictSurvivalRegion)
    (t : ℕ) (h : CausalHistory State (Bool × State) t)
    (hh : h∈(actionPath p (historyPolicy 0 (by norm_num) (by norm_num)) t).support) :
    riskMicroControlKernel id (fun _ => M.transitionPMF) restrictedHistoryPolicy t h=
      riskMicroControlKernel id (fun _ => M.transitionPMF) (historyPolicy 0 (by norm_num) (by norm_num)) t h := by
  have hb:=zero_path_current_safe p hp t h hh
  unfold riskMicroControlKernel
  congr 1
  change PMF.pure ((R.greedyAction (riskLastState t
    (riskHistoryMap id (fun ax : Bool × State => (ax.1,id ax.2)) t h))).val)=actionLaw 0 _ _
  have hlast : riskLastState t (riskHistoryMap id (fun ax : Bool × State => (ax.1,id ax.2)) t h)=riskLastState t h := by
    cases t <;> rfl
  rw [restricted_greedy,hlast,hb,actionLaw_zero]

/-- Equality of complete finite STATE-ACTION paths, not just stationary laws,
on safe initial source laws. Outside K the two actual policies are different. -/
theorem safe_initial_full_action_path (p : PMF State) (hp : StaysIn p conflictSurvivalRegion) (T : ℕ) :
    actionPath p restrictedHistoryPolicy T=
      actionPath p (historyPolicy 0 (by norm_num) (by norm_num)) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    apply PMF.ext
    rintro ⟨h,ax⟩
    change pmfExtend (actionPath p restrictedHistoryPolicy T)
      (riskMicroControlKernel id (fun _ => M.transitionPMF) restrictedHistoryPolicy T) (h,ax)=
      pmfExtend (actionPath p (historyPolicy 0 (by norm_num) (by norm_num)) T)
        (riskMicroControlKernel id (fun _ => M.transitionPMF) (historyPolicy 0 (by norm_num) (by norm_num)) T) (h,ax)
    rw [pmfExtend_apply,pmfExtend_apply,ih]
    by_cases hh : actionPath p (historyPolicy 0 (by norm_num) (by norm_num)) T h=0
    · simp only [hh,zero_mul]
    · rw [supported_zero_kernel_eq p hp T h (by simpa only [PMF.mem_support_iff] using hh)]

theorem unsafe_initial_full_action_path_ne :
    actionPath (PMF.pure (false,false)) restrictedHistoryPolicy 1≠
      actionPath (PMF.pure (false,false)) (historyPolicy 0 (by norm_num) (by norm_num)) 1 := by
  intro he
  have hh:=congrArg (fun p : PMF (CausalHistory State (Bool × State) 1)=>
    (p ((false,false),(false,(false,false)))).toReal) he
  change (pmfExtend (PMF.pure (false,false))
    (riskMicroControlKernel id (fun _ => M.transitionPMF) restrictedHistoryPolicy 0)
    ((false,false),(false,(false,false)))).toReal=
      (pmfExtend (PMF.pure (false,false))
        (riskMicroControlKernel id (fun _ => M.transitionPMF) (historyPolicy 0 (by norm_num) (by norm_num)) 0)
        ((false,false),(false,(false,false)))).toReal at hh
  simp [pmfExtend,riskMicroControlKernel,restrictedHistoryPolicy,
    SourcePolicyPathBridgeCheck.observationMarkovPolicy,riskHistoryMap,riskLastState,
    restricted_greedy,historyPolicy,actionLaw_zero] at hh
  norm_num [transition_eq] at hh


end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricControl
