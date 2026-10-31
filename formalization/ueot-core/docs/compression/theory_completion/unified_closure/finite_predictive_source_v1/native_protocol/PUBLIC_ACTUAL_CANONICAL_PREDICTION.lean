import UEOT
set_option maxRecDepth 16384
namespace IndependentRegisterPredictive
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
open RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite
open RegisterFaultDynamicProbe RegisterFaultDynamicProbeInfinite RegisterFaultDynamicPrice
open RegisterInstructionPurposeScale RegisterActuatorScaleSource RegisterSemanticInstructionScale
open UEOT.V3.BoundedLossSampling
open scoped BigOperators ENNReal
noncomputable section
local instance {n : ℕ} : MeasurableSpace (RegisterFaultJointRecord.ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (RegisterFaultJointRecord.ModeRecord n):=⟨fun _=>trivial⟩

-- SAME immutable 48/16-per-row raw word, with the ORIGINAL existing width1/4 protocol.
-- This is a separate identity-matching formal reuse check, not a change to the width1/100 registration.
-- In this original coarser read the old low-cost verdict is UNKNOWN; no old idle fact is transported across bins.
def rawWord : Coordinate 64→Bool×Bool:=fun j=>if j.2.val<48 then (true,false) else (false,false)
def visible (k : ℕ) : Batch 64:=fun j=>(decide (j.2.val<48) && j.1,if j.2.val<48 then k else 0)
def low : Mechanism:=⟨true,11/5⟩
def high : Mechanism:=⟨true,6⟩
def initial : Organism 2:=⟨[false,true],(fun j=>if j=0 then false else true),true⟩
theorem half_price : priceValue (1/2) (by norm_num)=(1/2 : NNReal) :=by
  unfold priceValue
  apply Subtype.ext
  change ((1/2 : ℚ) : ℝ)=(1/2 : ℝ)
  norm_num
theorem eps_ok : (1/4 : NNReal)≤1:=by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)
theorem low_bin : feeBin (1/4) low.writeCost=8:=by norm_num [feeBin,low]
theorem high_bin : feeBin (1/4) high.writeCost=24:=by norm_num [feeBin,high]

theorem low_actual_data : sourceData low (1/4) rawWord=visible 8 :=by
  funext j
  rcases j with ⟨b,k⟩
  have hgoal : low.goal=true:=rfl
  cases b <;> by_cases hk : k.val<48 <;>
    simp only [sourceData,feature,rawWord,hk,if_true,if_false,low_bin] <;>
    simp [visible,hgoal,hk]
theorem high_actual_data : sourceData high (1/4) rawWord=visible 24 :=by
  funext j
  rcases j with ⟨b,k⟩
  have hgoal : high.goal=true:=rfl
  cases b <;> by_cases hk : k.val<48 <;>
    simp only [sourceData,feature,rawWord,hk,if_true,if_false,high_bin] <;>
    simp [visible,hgoal,hk]

theorem mean_true (k : ℕ) : birthMean (visible k) true=3/4 :=by
  change birthMean (visible 0) true=3/4
  decide +kernel
theorem mean_false (k : ℕ) : birthMean (visible k) false=0 :=by simp [birthMean,visible]

theorem low_new : classify (1/2) (1/4) (1/2) (1/4) (visible 8)=.repair true :=by decide +kernel
theorem low_old : select (1/2) (1/4) (visible 8)=.unknown :=by decide +kernel
theorem high_new : classify (1/2) (1/4) (1/2) (1/4) (visible 24)=.idle true :=by decide +kernel

example : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) rawWord)=.repair true :=by rw [low_actual_data];exact low_new
example : select (1/2) (1/4) (sourceData low (1/4) rawWord)=.unknown :=by rw [low_actual_data];exact low_old
example : classify (1/2) (1/4) (1/2) (1/4) (sourceData high (1/4) rawWord)=.idle true :=by rw [high_actual_data];exact high_new

-- Actual original trace/terminal parent, with all 128 transactions retained.
example : (probeTrace (0 : Fin 2) low rawWord initial (registration 64)).map (recordObservation (1/4))=
    (registration 64).map (sourceData low (1/4) rawWord) :=actual_probe_trace_observations 0 low (1/4) rawWord initial rfl _
example : postProbeParent (0 : Fin 2) low rawWord initial=
    (probeTrace 0 low rawWord initial (registration 64)).foldl (fun _ r=>r.transaction.parentAfter) initial :=postProbeParent_trace _ _ _ _
example : (postProbeParent (0 : Fin 2) low rawWord initial).physical 0=false :=rfl
example : (postProbeParent (0 : Fin 2) low rawWord initial).physical 1=true :=rfl
example : (postProbeParent (0 : Fin 2) low rawWord initial).program=true :=postProbeParent_program _ _ _ _

theorem low_good (noise : PMF Bool) : rawWord∈Good noise low (1/4) eps_ok 64 (1/4) ((1/4 : ℚ) : ℝ) :=by
  intro b
  change |empiricalRisk birthScore (sourceSample low (1/4) b) rawWord-
    trueRisk (row noise low (1/4) eps_ok (1/4) b).toMeasure birthScore|≤((1/4 : ℚ) : ℝ)
  rw [←birthMean_source,birth_mean,low_actual_data]
  cases b <;> norm_num [mean_false,mean_true,low,repairChance]
theorem high_good (noise : PMF Bool) : rawWord∈Good noise high (1/4) eps_ok 64 (1/4) ((1/4 : ℚ) : ℝ) :=by
  intro b
  change |empiricalRisk birthScore (sourceSample high (1/4) b) rawWord-
    trueRisk (row noise high (1/4) eps_ok (1/4) b).toMeasure birthScore|≤((1/4 : ℚ) : ℝ)
  rw [←birthMean_source,birth_mean,high_actual_data]
  cases b <;> norm_num [mean_false,mean_true,high,repairChance]

theorem low_separated : DynamicallySeparated low (1/4) (1/2) (1/4) (1/2) (1/4) :=by
  unfold DynamicallySeparated
  rw [low_bin]
  left
  norm_num [repairChance]
theorem high_separated : DynamicallySeparated high (1/4) (1/2) (1/4) (1/2) (1/4) :=by
  unfold DynamicallySeparated
  rw [high_bin]
  right
  norm_num [repairChance]

open UEOT.V3.EvolutionPrice
open RegisterFaultJointRecord
open RegisterPopulationHistorySource (Store Request)

theorem actual_repair : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) rawWord)=.repair true :=by
  rw [low_actual_data];exact low_new

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState
set_option linter.defProp false
abbrev port : Fin 2:=0
def labels : PMF Bool:=PMF.pure false
theorem discount_ok : (0:ℝ)<1/2 ∧ (1/2:ℝ)<1:=by norm_num
local instance : Fintype (ReachableState (stochasticFuture
    (RegisterPredictiveSource.kernel port labels low (1/2) (1/4) eps_ok (1/2) discount_ok)
    (RegisterPredictiveSource.read port))):=Fintype.ofFinite _
local instance : Fintype (ReachableState (stochasticFuture
    (RegisterPredictiveSource.kernel port labels high (1/2) (1/4) eps_ok (1/2) discount_ok)
    (RegisterPredictiveSource.read port))):=Fintype.ofFinite _
def actualParent:=postProbeParent port low rawWord initial
def actualP:=returnedAST port (classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) rawWord))
def actualQ:=RegisterSemanticInstructionScale.returnedProgram port actualP

theorem this_pair : synthesize port actualP=some actualQ:=returned_synthesis port _
theorem whole_micro_actual :
    (RegisterPredictiveSource.control port labels low (1/2) (1/4) eps_ok (1/2) discount_ok).micro=
    model port labels low (1/2) (1/4) eps_ok (1/2) discount_ok :=
  RegisterPredictiveSource.control_micro_eq_actual port labels low (1/2) (1/4) eps_ok (1/2) discount_ok

def actualPrimitiveRow :=RegisterPredictiveSource.kernel_actual_mode_source port labels low (1/2) (1/4) eps_ok (1/2) discount_ok actualParent.physical

def actualDerivedResolve :=RegisterPredictiveSource.actual_tests_resolve port labels low (1/2) (1/4) eps_ok (1/2) discount_ok

def actualUniqueQuotient :=RegisterPredictiveSource.actual_unique_normalized_quotient port labels low (1/2) (1/4) eps_ok (1/2) discount_ok

theorem this_macro_lifts_this_P (x : State 2) :
    RegisterPredictiveSource.returnedMacro port labels low (1/2) (1/4) eps_ok (1/2) discount_ok actualQ
      ((RegisterPredictiveSource.control port labels low (1/2) (1/4) eps_ok (1/2) discount_ok).f x)=interpret actualP x :=
  RegisterPredictiveSource.returnedMacro_lift_is_actual_p port labels low (1/2) (1/4) eps_ok (1/2) discount_ok actualP actualQ this_pair x

def canonicalValueAtRealParent :=RegisterPredictiveSource.canonical_value_is_actual_active_value port labels low (1/2) (1/4) eps_ok (1/2) discount_ok actualParent.physical

def canonicalFineCompetitorOptimality :=RegisterPredictiveSource.canonical_greedy_actual_optimal port labels low (1/2) (1/4) eps_ok (1/2) discount_ok

def allPriceHighValue :=RegisterPredictiveSource.canonical_value_is_actual_active_value port labels high (1/2) (1/4) eps_ok (1/2) discount_ok actualParent.physical

example : (1/2:ℝ)*high.writeCost>1:=by norm_num [high]

def owner : RegisterTimestampedBirthSource.ClockedOrganism 2:=⟨initial,[(2,false),(5,true)],11⟩
theorem actual_six : RegisterFaultDynamicProbeP9Terminal.Six (0:Fin 1) labels low
    (priceValue (1/2) (by norm_num)) (1/4) eps_ok (1/2) discount_ok owner.identity (owner.clock+128)
    ((RegisterFaultDynamicProbeP9Terminal.clockedScale port).objectMap
      (RegisterFaultDynamicProbeP9Terminal.dataObject port low (1/2) (1/4) (1/2) (1/4) rawWord owner)) :=by
  convert RegisterFaultDynamicProbeP9Terminal.data_actual_p9_six port labels low (1/4)
    (by exact_mod_cast (by norm_num : (1/4:ℝ)<1)) (1/2) (1/4) (1/2) (1/4)
    (by norm_num) (by norm_num) (by norm_num) rawWord owner rfl (low_good labels) true actual_repair using 1; norm_num

theorem actual_selected_canonical_GOD :
    IsBellmanGODSelector (RegisterPredictiveSource.control port labels low (1/2) (1/4) eps_ok (1/2) discount_ok).micro (interpret actualP) :=by
  apply (RegisterPredictiveSource.actual_returned_god port labels low (1/2) (1/4) eps_ok (1/2) discount_ok actualP actualQ this_pair).mpr
  have hg:=actual_six.2.2.1
  rw [half_price] at hg
  exact hg

def originalP9ExactSource :=RegisterPredictiveSource.actual_p9_god_bridge port labels low (1/2) (1/4) eps_ok (1/2) discount_ok

-- Different dimension/retained port from author: n3/port1/hidden2.
def x : State 3:=fun _=>true
def hidden : State 3:=Function.update x 2 false
def activeDifferent : State 3:=Function.update x 1 false
def K (epsilon : NNReal) (he : epsilon≤1):=RegisterPredictiveSource.kernel (1:Fin 3) labels low (1/2) epsilon he (1/2) discount_ok
def obs : State 3→Bool:=RegisterPredictiveSource.read (1:Fin 3)
theorem hidden_distinct_predictive_equal : x≠hidden ∧ stochasticFuture (K (1/4) eps_ok) obs x=stochasticFuture (K (1/4) eps_ok) obs hidden :=by
  constructor
  · intro h; have hh:=congrFun h 2; norm_num [x,hidden] at hh
  · exact (RegisterPredictiveSource.future_eq_iff_active (1:Fin 3) labels low (1/2) (1/4) eps_ok (1/2) discount_ok x hidden).mpr rfl

theorem true_active_is_different : stochasticFuture (K (1/4) eps_ok) obs x≠stochasticFuture (K (1/4) eps_ok) obs activeDifferent :=by
  intro h
  have hh:=(RegisterPredictiveSource.future_eq_iff_active (1:Fin 3) labels low (1/2) (1/4) eps_ok (1/2) discount_ok x activeDifferent).mp h
  norm_num [x,activeDifferent] at hh

def hiddenReader : Instruction 3:=.test 2 true (.emit (some true)) (.emit none)
theorem hidden_reader_not_canonical_decoder :
    ¬∃D : (List (Action×Bool)→ℝ)→Action,
      D (stochasticFuture (K (1/4) eps_ok) obs x)=interpret hiddenReader x ∧
      D (stochasticFuture (K (1/4) eps_ok) obs hidden)=interpret hiddenReader hidden :=by
  rintro ⟨D,hx,hh⟩
  rw [←hidden_distinct_predictive_equal.2,hx] at hh
  norm_num [hiddenReader,interpret,x,hidden] at hh
  cases hh
example : synthesize (1:Fin 3) hiddenReader=none:=by decide +kernel

theorem total_fault_same_next_rows (a : Action) (z : State 3) :
    (K 1 (by norm_num)).mass x a z=(K 1 (by norm_num)).mass activeDifferent a z :=by
  have hu : Function.update x (1:Fin 3) (!low.goal)=Function.update activeDifferent (1:Fin 3) (!low.goal) :=by
    funext j;fin_cases j <;> rfl
  simp only [K,RegisterPredictiveSource.kernel,RegisterFaultControlModel.model,repairChance]
  norm_num
  rw [hu]

theorem total_fault_current_preword_separates :
    stochasticFuture (K 1 (by norm_num)) obs x [(none,true)]=1 ∧
    stochasticFuture (K 1 (by norm_num)) obs activeDifferent [(none,true)]=0 :=by
  constructor <;> simp only [stochasticFuture,one_word_trace_is_pre_transition_observation] <;>
    norm_num [obs,RegisterPredictiveSource.read,x,activeDifferent]

def oppositeGoal : Mechanism:=⟨false,11/5⟩
theorem zero_noise_same_physics_not_purpose (s z : State 3) (a : Action) :
    (RegisterPredictiveSource.kernel (1:Fin 3) labels low 0 0 (by norm_num) (1/2) discount_ok).mass s a z=
    (RegisterPredictiveSource.kernel (1:Fin 3) labels oppositeGoal 0 0 (by norm_num) (1/2) discount_ok).mass s a z :=by
  simp [RegisterPredictiveSource.kernel,RegisterFaultControlModel.model,repairChance]

theorem same_physics_rewards_disagree :
    (model (1:Fin 3) labels low 0 0 (by norm_num) (1/2) discount_ok).reward x none=1 ∧
    (model (1:Fin 3) labels oppositeGoal 0 0 (by norm_num) (1/2) discount_ok).reward x none=0 :=by
  simp only [RegisterFaultControlModel.model,expectedModePayoff_eq]
  norm_num [repairChance,stage,expectedChildren_eq,update,x,low,oppositeGoal]

end
end IndependentRegisterPredictive

#print axioms IndependentRegisterPredictive.this_pair
#print axioms IndependentRegisterPredictive.whole_micro_actual
#print axioms IndependentRegisterPredictive.actualPrimitiveRow
#print axioms IndependentRegisterPredictive.actualDerivedResolve
#print axioms IndependentRegisterPredictive.actualUniqueQuotient
#print axioms IndependentRegisterPredictive.this_macro_lifts_this_P
#print axioms IndependentRegisterPredictive.canonicalValueAtRealParent
#print axioms IndependentRegisterPredictive.canonicalFineCompetitorOptimality
#print axioms IndependentRegisterPredictive.allPriceHighValue
#print axioms IndependentRegisterPredictive.actual_six
#print axioms IndependentRegisterPredictive.actual_selected_canonical_GOD
#print axioms IndependentRegisterPredictive.originalP9ExactSource
#print axioms IndependentRegisterPredictive.hidden_distinct_predictive_equal
#print axioms IndependentRegisterPredictive.true_active_is_different
#print axioms IndependentRegisterPredictive.hidden_reader_not_canonical_decoder
#print axioms IndependentRegisterPredictive.total_fault_same_next_rows
#print axioms IndependentRegisterPredictive.total_fault_current_preword_separates
#print axioms IndependentRegisterPredictive.zero_noise_same_physics_not_purpose
#print axioms IndependentRegisterPredictive.same_physics_rewards_disagree
