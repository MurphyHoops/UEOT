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

theorem this_pair : synthesize port actualP=some actualQ:=RegisterFaultDynamicProbeInfinite.returned_synthesis port _
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

namespace FinalRegisterCrossInterface
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
open RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite RegisterFaultDynamicProbe
open RegisterInstructionPurposeScale RegisterActuatorScaleSource RegisterSemanticInstructionScale
open RegisterInstructionRecoveryScale RegisterFaultDynamicProbeLifecycle
open IndependentRegisterPredictive
open RegisterTimestampedBirthSource (ClockedOrganism)
open RegisterPopulationHistorySource (Store Request)
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState
open scoped BigOperators
noncomputable section
set_option linter.defProp false
local instance : Fintype (ReachableState (stochasticFuture
    (RegisterPredictiveSource.kernel port labels low (1/2) (1/4) eps_ok (1/2) discount_ok)
    (RegisterPredictiveSource.read port))):=Fintype.ofFinite _
abbrev Tail:=RegisterPopulationCurrentParentContinuation.Base 64 64
abbrev Words:=RegisterPopulationCurrentParentContinuation.Words
abbrev TraceSample:=Tail×Words

def confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class:=PMF.pure 1
def fullLaw:=RegisterPopulationCurrentParentContinuation.jointLaw (N:=64) port low (1/2) (1/4) (1/2) (1/4) owner true labels (1/4) eps_ok confuser 64

def current (z : Tail):=RegisterPopulationCurrentParentContinuation.currentParent port low (1/2) (1/4) (1/2) (1/4) z.1.1 owner true z.1.2

def pOf (z : Tail):=returnedAST port (classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1.1))
def qOf (z : Tail):=returnedProgram port (pOf z)
def estimateAt0 (z : Tail):=RegisterFaultDynamicProbeParentDiscovery.estimate
  (RegisterFaultDynamicProbeParentDiscovery.targetSensed port low (1/2) (1/4) (1/2) (1/4) z.1.1 owner.organism true z.1.2 0 z.2)
def episode (z : Tail):=RegisterFaultDynamicProbeParentDiscovery.episode port low (1/2) (1/4) (1/2) (1/4) z.1.1 owner.organism true z.1.2
def event0 (z : Tail):=RegisterFaultDynamicProbeParentDiscovery.eventIndex port low (1/2) (1/4) (1/2) (1/4) z.1.1 owner.organism true z.1.2 0
def initial (z : Tail):=[some (RegisterFaultDynamicProbeClocked.postClocked port low z.1.1 owner)]
def parentAt0 (z : Tail):=RegisterPopulationOwnerClockTransport.actualParent port low.writeCost (owner.clock+128) (initial z) (episode z) (event0 z)
def Bad : Set Tail:={z | z.1.1∉Good labels low (1/4) eps_ok 64 (1/4) ((1/4:ℚ):ℝ) ∨ estimateAt0 z≠parentAt0 z}

theorem not_bad_exact_prerequisites (z : Tail) (hz : z∉Bad) :
    z.1.1∈Good labels low (1/4) eps_ok 64 (1/4) ((1/4:ℚ):ℝ) ∧ estimateAt0 z=parentAt0 z :=by
  constructor
  · by_contra hb;exact hz (Or.inl hb)
  · by_contra hb;exact hz (Or.inr hb)

-- This proof intentionally does not assume or conclude marked-read Good.
theorem correct_mark_binds_actual_birth_parent (z : Tail) (hm : estimateAt0 z=parentAt0 z)
    (child : ClockedOrganism 2)
    (hc : RegisterPopulationOwnerClockTransport.childAt port low.writeCost (owner.clock+128)
      (initial z) (episode z) (event0 z)=some child) :
    let s:=RegisterPopulationOwnerClockTransport.run port low.writeCost (owner.clock+128) (initial z)
      ((episode z).take (event0 z))
    let q:=RegisterPopulationHistorySource.requestAt (episode z) (event0 z)
    ∃parent,(estimateAt0 z).bind (RegisterPopulationHistorySource.lookup s)=some parent ∧
      (RegisterTimestampedBirthSource.lineage port (RegisterOwnProgramPopulation.mechanism low.writeCost s q)).OffspringOf
        {parent with clock:=owner.clock+128+s.length} child ∧ child.clock=0 :=by
  dsimp only
  obtain ⟨parent,hp,hbirth,hzero⟩:=RegisterPopulationOwnerClockTransport.actual_birth_source port low.writeCost
    (owner.clock+128) _ _ child hc
  refine ⟨parent,?_,hbirth,hzero⟩
  rw [hm]
  simp only [parentAt0,RegisterPopulationOwnerClockTransport.actualParent,hc,Option.map_some,Option.bind_some]
  exact hp

-- The actual tail's computed AST is unchanged by native source extension.
theorem all_input_same_pair (z : Tail) : synthesize port (pOf z)=some (qOf z) :=RegisterFaultDynamicProbeInfinite.returned_synthesis port _

def current_primitive_row (z : Tail):=RegisterPredictiveSource.kernel_actual_mode_source port labels low (1/2) (1/4) eps_ok (1/2) discount_ok (current z).organism.physical

theorem current_macro_is_this_p (z : Tail) :
    RegisterPredictiveSource.returnedMacro port labels low (1/2) (1/4) eps_ok (1/2) discount_ok (qOf z)
      ((RegisterPredictiveSource.control port labels low (1/2) (1/4) eps_ok (1/2) discount_ok).f (current z).organism.physical)=
      interpret (pOf z) (current z).organism.physical :=
  RegisterPredictiveSource.returnedMacro_lift_is_actual_p port labels low (1/2) (1/4) eps_ok (1/2) discount_ok (pOf z) (qOf z) (all_input_same_pair z) _

theorem current_exact_evaluation (z : Tail)
    (hg : z.1.1∈Good labels low (1/4) eps_ok 64 (1/4) ((1/4:ℚ):ℝ))
    (ha : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1.1)≠.unknown) :
    synthesize port (pOf z)=some (qOf z) ∧
    IsBellmanGODSelector (model port labels low (1/2) (1/4) eps_ok (1/2) discount_ok) (interpret (pOf z)) ∧
    actualValue port labels low (1/4) eps_ok (1/2) (1/2) (current z).organism (pOf z)=
      (model port labels low (1/2) (1/4) eps_ok (1/2) discount_ok).optimalValue (current z).organism.physical ∧
    actualValue (0:Fin 1) labels low (1/4) eps_ok (1/2) (1/2) (projectOrganism port (current z).organism) (qOf z)=
      (model port labels low (1/2) (1/4) eps_ok (1/2) discount_ok).optimalValue (current z).organism.physical :=by
  convert RegisterPopulationCurrentParentContinuation.current_returned_pair port low (1/2) (1/4) (1/2) (1/4) z.1.1 owner true z.1.2
      labels (1/4) eps_ok (by norm_num) (by norm_num) (by norm_num) rfl hg ha using 1 <;> norm_num [current,pOf,qOf,half_price]

theorem current_canonical_GOD (z : Tail) (hg : z.1.1∈Good labels low (1/4) eps_ok 64 (1/4) ((1/4:ℚ):ℝ))
    (ha : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1.1)≠.unknown) :
    IsBellmanGODSelector (RegisterPredictiveSource.control port labels low (1/2) (1/4) eps_ok (1/2) discount_ok).micro (interpret (pOf z)) :=by
  rw [RegisterPredictiveSource.control_micro_eq_actual]
  exact (current_exact_evaluation z hg ha).2.1

theorem current_canonical_value (z : Tail) (hg : z.1.1∈Good labels low (1/4) eps_ok 64 (1/4) ((1/4:ℚ):ℝ))
    (ha : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1.1)≠.unknown) :
    actualValue port labels low (1/4) eps_ok (1/2) (1/2) (current z).organism (pOf z)=
      (RegisterPredictiveSource.control port labels low (1/2) (1/4) eps_ok (1/2) discount_ok).macroModel.optimalValue
        ((RegisterPredictiveSource.control port labels low (1/2) (1/4) eps_ok (1/2) discount_ok).f (current z).organism.physical) :=
  (current_exact_evaluation z hg ha).2.2.1.trans (RegisterPredictiveSource.control_exact_value port labels low (1/2) (1/4) eps_ok (1/2) discount_ok _)

def sourceNativeQWords :=RegisterPopulationCurrentParentContinuation.conditional_returned_word_source (N:=64) port low (1/2) (1/4) (1/2) (1/4) owner true labels (1/4) eps_ok (B:=64)

def sourceBaseMarginal :=RegisterPopulationCurrentParentContinuation.finite_marginal (N:=64) port low (1/2) (1/4) (1/2) (1/4) owner true labels (1/4) eps_ok confuser 64

def sourceSameInitialBalance :=RegisterPopulationCurrentParentContinuation.actual_balance_at_switch (N:=64) port low (1/2) (1/4) (1/2) (1/4) owner true (B:=64) 300 (9/4) (1/20)

def sourceP6NativePrice :=RegisterPopulationCurrentParentContinuation.same_joint_p6_native_price (N:=64) port low (1/2) (1/4) (1/2) (1/4) owner labels (1/4) eps_ok confuser 64
  (1/20) (9/4) 300 (9/4) (by norm_num [low]) (by norm_num) (by norm_num) rfl

theorem exact_full_risk : fullLaw.real (Prod.fst ⁻¹' Bad)≤5*Real.exp (-8) :=by
  have h:=RegisterPopulationCurrentParentContinuation.full_source_two_event_bound (N:=64) port low (1/2) (1/4) (1/2) (1/4) owner true
    labels (1/4) eps_ok confuser 64 (by decide) (by norm_num) (0:Fin 3)
  have hh : fullLaw.real (Prod.fst ⁻¹' Bad)≤ min 1 (4*Real.exp (-8))+Real.exp (-8) :=by
    convert h using 1 <;> norm_num [fullLaw,Bad,estimateAt0,parentAt0,initial,episode,event0]
    all_goals rfl
  exact hh.trans (by nlinarith [min_le_right (1:ℝ) (4*Real.exp (-8))])

-- Full original six-property terminal is evaluated at the REAL end state.
def currentObject (z : Tail) : RegisterFaultDynamicProbeP9Terminal.Carrier port:=
  (current z,⟨(pOf z,qOf z),all_input_same_pair z⟩,RegisterFaultDynamicProbeP9Terminal.idleAccepted port)

theorem current_original_six (z : Tail)
    (hg : z.1.1∈Good labels low (1/4) eps_ok 64 (1/4) ((1/4:ℚ):ℝ))
    (b : Bool) (hs : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1.1)=.repair b) :
    RegisterFaultDynamicProbeP9Terminal.Six (0:Fin 1) labels low (1/2) (1/4) eps_ok (1/2) discount_ok
      (current z).identity (current z).clock
      ((RegisterFaultDynamicProbeP9Terminal.clockedScale port).objectMap (currentObject z)) :=by
  have ha : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1.1)≠.unknown:=by rw [hs];simp
  have hc : restorationCheck port low.goal (pOf z)=true:=accepted_repair_restores port low (1/2) (1/4) (1/2) (1/4) z.1.1 b hs
  have hp : (current z).organism.program=low.goal:=
    (RegisterPopulationCurrentParentContinuation.current_parent_source port low (1/2) (1/4) (1/2) (1/4) z.1.1 owner true z.1.2).1
  apply RegisterFaultDynamicProbeP9Terminal.actual_p9_terminal port labels low (1/2) (1/4) eps_ok (1/2) discount_ok
    (current z).identity (current z).clock (currentObject z) hc
  · exact ⟨rfl,rfl,hp⟩
  · change PurposeOrder port labels low (1/4) eps_ok (1/2) (1/2) ((current z).organism,pOf z,.emit none)
    refine ⟨discount_ok,?_⟩
    rw [(current_exact_evaluation z hg ha).2.2.1,
      actual_value_policy port labels low (1/4) eps_ok (1/2) (1/2) discount_ok _ hp]
    exact (astPolicy (.emit none)).infiniteValue_le_optimal _ _
  · exact (current_exact_evaluation z hg ha).2.1
  · exact ⟨by exact_mod_cast (by norm_num : (1/4:ℝ)<1),
      RegisterFaultDynamicProbeNativeHomeostasis.native_frequency port labels low (1/4) eps_ok (pOf z) hc (current z).organism hp⟩

-- SAME full law: conditional output roles use actual mark equality, not read Good.
theorem same_joint_source_outputs :
    ∀ᵐ z ∂fullLaw,
      ResourceViable 300 (RegisterPopulationCurrentParentContinuation.tailInflow 195 (9/4))
        (RegisterPopulationCurrentParentContinuation.wholeCost port low (1/2) (1/4) (1/2) (1/4) owner true (1/20) z) ∧
      RegisterPopulationCurrentParentContinuation.ActualCohortPrice port low (1/2) (1/4) (1/2) (1/4) z.1.1.1 owner z.1.1.2 ∧
      (z.1∉Bad→∀b : Bool,classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1.1.1)=.repair b→
        RegisterPopulationCurrentParentContinuation.NativeFacts port low (1/4) eps_ok (current z.1)
          (RegisterPopulationCurrentParentContinuation.nativeRecords port low (1/2) (1/4) (1/2) (1/4) owner true z) ∧
        IsBellmanGODSelector (RegisterPredictiveSource.control port labels low (1/2) (1/4) eps_ok (1/2) discount_ok).micro (interpret (pOf z.1)) ∧
        RegisterFaultDynamicProbeP9Terminal.Six (0:Fin 1) labels low (1/2) (1/4) eps_ok (1/2) discount_ok
          (current z.1).identity (current z.1).clock
          ((RegisterFaultDynamicProbeP9Terminal.clockedScale port).objectMap (currentObject z.1)) ∧
        estimateAt0 z.1=parentAt0 z.1) :=by
  filter_upwards [sourceP6NativePrice] with z hz
  refine ⟨hz.1,hz.2.2.2,?_⟩
  intro hnb b hs
  have hh:=not_bad_exact_prerequisites z.1 hnb
  have ha : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1.1.1)≠.unknown:=by rw [hs];simp
  exact ⟨(hz.2.2.1 b hs).1,current_canonical_GOD z.1 hh.1 ha,current_original_six z.1 hh.1 b hs,hh.2⟩


end
end FinalRegisterCrossInterface

#print axioms FinalRegisterCrossInterface.not_bad_exact_prerequisites
#print axioms FinalRegisterCrossInterface.correct_mark_binds_actual_birth_parent
#print axioms FinalRegisterCrossInterface.all_input_same_pair
#print axioms FinalRegisterCrossInterface.current_primitive_row
#print axioms FinalRegisterCrossInterface.current_macro_is_this_p
#print axioms FinalRegisterCrossInterface.current_exact_evaluation
#print axioms FinalRegisterCrossInterface.current_canonical_GOD
#print axioms FinalRegisterCrossInterface.current_canonical_value
#print axioms FinalRegisterCrossInterface.sourceNativeQWords
#print axioms FinalRegisterCrossInterface.sourceBaseMarginal
#print axioms FinalRegisterCrossInterface.sourceSameInitialBalance
#print axioms FinalRegisterCrossInterface.sourceP6NativePrice
#print axioms FinalRegisterCrossInterface.exact_full_risk

#print axioms FinalRegisterCrossInterface.current_original_six
#print axioms FinalRegisterCrossInterface.same_joint_source_outputs

namespace FinalMeanResourceRole
open Set MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.Objecthood UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.ResourceClosure
open UEOT.V3.ViabilityKernel
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultSource
open RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite RegisterFaultDynamicProbe
open RegisterInstructionPurposeScale RegisterInstructionRecoveryScale RegisterFaultDynamicProbeLifecycle
open IndependentRegisterPredictive
open FinalRegisterCrossInterface
open scoped ENNReal BigOperators
noncomputable section
set_option linter.defProp false
set_option backward.isDefEq.respectTransparency false
abbrev Org:=RepairOrganizationState (State 2) Action Bool
local instance : Fintype Org:=repairOrganizationStateFintype
local instance : MeasurableSpace Org:=⊤
local instance : MeasurableSingletonClass Org:=⟨fun _=>trivial⟩
local instance : MeasurableSpace (RegisterFaultJointRecord.ModeRecord 2):=⊤
local instance : MeasurableSingletonClass (RegisterFaultJointRecord.ModeRecord 2):=⟨fun _=>trivial⟩
local instance : MeasurableSpace (RegisterTimestampedBirthSource.ClockedRecord 2):=⊤
local instance : MeasurableSingletonClass (RegisterTimestampedBirthSource.ClockedRecord 2):=⟨fun _=>trivial⟩

def S:=RegisterFaultNativeOrganization.system port low (1/4) eps_ok
def mu0 (z : Tail):PMF Org:=PMF.pure (RegisterFaultNativeOrganization.organization port low (current z).organism.physical)

theorem initial_in_original_carrier (z : Tail) :
    StaysIn (mu0 z) (finiteJointRepairCarrier (physical port) (target port low.goal) (certificate port low.goal)
      (substrate port) codec low.goal) :=by
  intro s hs
  have he : s=RegisterFaultNativeOrganization.organization port low (current z).organism.physical:=by simpa [mu0] using hs
  rw [he]
  exact (carrier_iff_program port low.goal _).mpr rfl

def original_mean (z : Tail):=finiteJoint_meanHomeostasis (physical port) (target port low.goal) (target_fixed port low.goal)
  (certificate port low.goal) (substrate port) codec low.goal (compiled_dynamics_implements port low.goal)
  (fault port) (1/4) eps_ok (actual_fault_envelope port low.goal) (mu0 z) (initial_in_original_carrier z)
  (by exact_mod_cast (by norm_num : (1/4:ℝ)<1))

def actualMarginal (z : Tail) (t : ℕ):Measure Org:=
  (RegisterPopulationCurrentParentContinuation.continuationKernel (N:=64) port low (1/2) (1/4) (1/2) (1/4) owner true labels (1/4) eps_ok 64 z).map
    (fun words=>RegisterFaultNativeOrganization.readRecord port
      (RegisterTimestampedBirthSource.eraseRecord
        (RegisterPopulationCurrentParentContinuation.nativeRecords port low (1/2) (1/4) (1/2) (1/4) owner true (z,words) t)))

theorem same_actual_marginal (z : Tail) (b : Bool)
    (hs : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1.1)=.repair b) (t : ℕ) :
    actualMarginal z t=(homeostaticMarginal S.mixedKernel (mu0 z) t).toMeasure :=by
  have hc : restorationCheck port low.goal (pOf z)=true:=accepted_repair_restores port low (1/2) (1/4) (1/2) (1/4) z.1.1 b hs
  have hp : (current z).organism.program=low.goal:=
    (RegisterPopulationCurrentParentContinuation.current_parent_source port low (1/2) (1/4) (1/2) (1/4) z.1.1 owner true z.1.2).1
  have hnative : Measurable (fun words=>RegisterPopulationCurrentParentContinuation.nativeRecords port low (1/2) (1/4) (1/2) (1/4) owner true (z,words)):=
    (RegisterPopulationCurrentParentContinuation.measurable_nativeRecords (N:=64) (B:=64) port low (1/2) (1/4) (1/2) (1/4) owner true).comp (measurable_const.prodMk measurable_id)
  have herase : Measurable (fun words t=>RegisterTimestampedBirthSource.eraseRecord
      (RegisterPopulationCurrentParentContinuation.nativeRecords port low (1/2) (1/4) (1/2) (1/4) owner true (z,words) t)):=by
    apply measurable_pi_lambda
    intro k
    exact (show Measurable (RegisterTimestampedBirthSource.eraseRecord : RegisterTimestampedBirthSource.ClockedRecord 2→RegisterFaultJointRecord.ModeRecord 2) from fun _ _=>trivial).comp
      ((measurable_pi_apply k).comp hnative)
  have hread : Measurable (fun rs : ℕ→RegisterFaultJointRecord.ModeRecord 2=>RegisterFaultNativeOrganization.readRecord port (rs t)):=
    (RegisterFaultNativeOrganization.measurable_readRecord port).comp (measurable_pi_apply t)
  have he:=congrArg (fun nu : Measure (ℕ→RegisterFaultJointRecord.ModeRecord 2)=>nu.map (fun rs=>RegisterFaultNativeOrganization.readRecord port (rs t)))
    (RegisterPopulationCurrentParentContinuation.conditional_native_erasure port low (1/2) (1/4) (1/2) (1/4) owner true labels (1/4) eps_ok z)
  rw [Measure.map_map hread herase] at he
  exact he.trans (RegisterFaultNativeOrganization.actual_organization_marginal port labels low (1/4) eps_ok (pOf z) hc (current z).organism hp t)

theorem same_actual_mean (z : Tail) (b : Bool)
    (hs : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1.1)=.repair b) :
    MeanHomeostasis (fun t=>((actualMarginal z t) S.legitimateᶜ).toReal)
      (((1/4:ENNReal)*canonicalFaultBurden S).toReal /
        ((((1-(1/4:NNReal):NNReal):ENNReal)*S.repairDrift).toReal)) :=by
  simp_rw [same_actual_marginal z b hs]
  convert original_mean z using 1 <;> norm_num
  all_goals rfl

theorem same_actual_finite_horizon (z : Tail) (b : Bool)
    (hs : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1.1)=.repair b) (K : ℕ) :
    ((((1-(1/4:NNReal):NNReal):ENNReal)*S.repairDrift)*
      (∑t∈Finset.range K,(actualMarginal z t) S.legitimateᶜ))≤
        homeostaticENNExpectation (mu0 z) S.potential+(K:ENNReal)*((1/4:ENNReal)*canonicalFaultBurden S) :=by
  simp_rw [same_actual_marginal z b hs]
  convert finiteJoint_finiteHorizonDamagedOccupation (physical port) (target port low.goal) (target_fixed port low.goal)
    (certificate port low.goal) (substrate port) codec low.goal (compiled_dynamics_implements port low.goal)
    (fault port) (1/4) eps_ok (actual_fault_envelope port low.goal) (mu0 z) (initial_in_original_carrier z) K using 1 <;> norm_num
  all_goals rfl


local instance : IsProbabilityMeasure fullLaw:=by dsimp [fullLaw];infer_instance

def actualCost (z : TraceSample) (t : ℕ):ℝ:=RegisterPopulationCurrentParentContinuation.wholeCost port low (1/2) (1/4) (1/2) (1/4) owner true (1/20) z t

theorem list_actual_cost_bounds (rs : List (Option (RegisterTimestampedBirthSource.ClockedRecord 2)))
    (hb : ∀r∈rs,0≤RegisterPopulationFundedProtocol.fee r ∧ RegisterPopulationFundedProtocol.fee r≤(low.writeCost:ℝ)) (t : ℕ) :
    0≤RegisterPopulationFiniteEpisodeResource.costStream rs t ∧ RegisterPopulationFiniteEpisodeResource.costStream rs t≤(low.writeCost:ℝ) :=by
  cases hh : rs[t]? with
  | none=>simp [RegisterPopulationFiniteEpisodeResource.costStream,RegisterPopulationFundedProtocol.recordAt,hh,RegisterPopulationFundedProtocol.fee,low.writeCost.coe_nonneg]
  | some r=>
    have hr : r∈rs:=List.mem_iff_getElem?.mpr ⟨t,hh⟩
    simpa [RegisterPopulationFiniteEpisodeResource.costStream,RegisterPopulationFundedProtocol.recordAt,hh] using hb r hr

theorem actual_cost_bounds (z : TraceSample) (t : ℕ) :
    0≤actualCost z t ∧ actualCost z t≤2*(low.writeCost:ℝ)+(1/20:ℝ) :=by
  have hw:=list_actual_cost_bounds (RegisterPopulationCurrentParentContinuation.finiteRecords port low (1/2) (1/4) (1/2) (1/4) owner true z.1)
    (RegisterPopulationFiniteEpisodeResource.whole_fee_bounds port low (1/2) (1/4) (1/2) (1/4) z.1.1.1 owner
      (RegisterFaultDynamicProbeParentDiscovery.plan true z.1.1.2)) t
  have hr : 0≤RegisterFiniteGenerationCommonConsumer.readCost 131 64 (1/20) t ∧
      RegisterFiniteGenerationCommonConsumer.readCost 131 64 (1/20) t≤(1/20:ℝ) :=by
    unfold RegisterFiniteGenerationCommonConsumer.readCost
    split_ifs <;> norm_num
  have ht : 0≤RegisterPopulationCurrentParentContinuation.tailFee 195
      (RegisterPopulationCurrentParentContinuation.nativeRecords port low (1/2) (1/4) (1/2) (1/4) owner true z) t ∧
      RegisterPopulationCurrentParentContinuation.tailFee 195
      (RegisterPopulationCurrentParentContinuation.nativeRecords port low (1/2) (1/4) (1/2) (1/4) owner true z) t≤(low.writeCost:ℝ) :=by
    by_cases hk : 195≤t
    · simp only [RegisterPopulationCurrentParentContinuation.tailFee,hk,ite_true]
      exact RegisterPopulationCurrentParentContinuation.native_fee_bounds port low (1/2) (1/4) (1/2) (1/4) owner true z _
    · simp [RegisterPopulationCurrentParentContinuation.tailFee,hk,low.writeCost.coe_nonneg]
  have hlen:=RegisterPopulationCurrentParentContinuation.finite_records_length (N:=64) port low (1/2) (1/4) (1/2) (1/4) owner true z.1
  dsimp only [actualCost,RegisterPopulationCurrentParentContinuation.wholeCost,
    RegisterPopulationCurrentParentContinuation.finiteBill,RegisterFiniteGenerationCommonConsumer.fullCost,
    RegisterPopulationCurrentParentContinuation.switchTime]
  rw [show (RegisterPopulationCurrentParentContinuation.finiteRecords port low (1/2) (1/4) (1/2) (1/4) owner true z.1).length=131 from hlen]
  norm_num only [Nat.reduceMul,Nat.reduceAdd]

  constructor <;> linarith [hw.1,hw.2,hr.1,hr.2,ht.1,ht.2]

theorem actual_cost_measurable (t : ℕ) : Measurable (fun z : TraceSample=>actualCost z t) :=by
  have hf : Measurable (fun z : TraceSample=>RegisterPopulationCurrentParentContinuation.finiteBill port low (1/2) (1/4) (1/2) (1/4) owner true (1/20) z.1 t):=
    (measurable_of_finite (fun b : Tail=>RegisterPopulationCurrentParentContinuation.finiteBill port low (1/2) (1/4) (1/2) (1/4) owner true (1/20) b t)).comp measurable_fst
  have he : Measurable (fun z : TraceSample=>(RegisterPopulationCurrentParentContinuation.nativeRecords port low (1/2) (1/4) (1/2) (1/4) owner true z (t-195)).expenditure):=
    (show Measurable (fun r : RegisterTimestampedBirthSource.ClockedRecord 2=>r.expenditure) from fun _ _=>trivial).comp
      ((measurable_pi_apply (t-195)).comp
        (RegisterPopulationCurrentParentContinuation.measurable_nativeRecords (N:=64) (B:=64) port low (1/2) (1/4) (1/2) (1/4) owner true))
  by_cases hk : 195≤t
  · convert hf.add he using 1
    funext z
    simp only [actualCost,RegisterPopulationCurrentParentContinuation.wholeCost,RegisterPopulationCurrentParentContinuation.tailFee,
      RegisterPopulationCurrentParentContinuation.switchTime,Nat.reduceMul,Nat.reduceAdd,hk,ite_true]
    rfl
  · convert hf using 1
    funext z
    simp only [actualCost,RegisterPopulationCurrentParentContinuation.wholeCost,RegisterPopulationCurrentParentContinuation.tailFee,
      RegisterPopulationCurrentParentContinuation.switchTime,Nat.reduceMul,Nat.reduceAdd,hk,ite_false,add_zero]

theorem actual_cost_integrable (t : ℕ) : Integrable (fun z : TraceSample=>actualCost z t) fullLaw :=by
  apply Integrable.of_bound (actual_cost_measurable t).aestronglyMeasurable (2*(low.writeCost:ℝ)+(1/20:ℝ))
  exact ae_of_all _ (fun z=>by rw [Real.norm_eq_abs,abs_of_nonneg (actual_cost_bounds z t).1];exact (actual_cost_bounds z t).2)

-- Literal write+read+tail expectations, not an invented Cresource state cost.
theorem original_expected_accounting_role :
    ResourceViable 300 (RegisterPopulationCurrentParentContinuation.tailInflow 195 (9/4))
      (fun t=>∫z,actualCost z t ∂fullLaw) :=by
  rw [resourceViable_iff_cumulative_cost_le]
  intro K
  have hb (z : TraceSample) : (∑t∈Finset.range K,actualCost z t)≤300+
      ∑t∈Finset.range K,RegisterPopulationCurrentParentContinuation.tailInflow 195 (9/4) t :=by
    exact (resourceViable_iff_cumulative_cost_le _ _ _).mp
      (RegisterPopulationCurrentParentContinuation.whole_p6 (N:=64) port low (1/2) (1/4) (1/2) (1/4) owner true
        (1/20) (9/4) 300 (9/4) (by norm_num [low]) (by norm_num) (by norm_num) z) K
  have hi:=integral_mono_of_nonneg (ae_of_all fullLaw (fun z=>Finset.sum_nonneg (fun t _=>(actual_cost_bounds z t).1)))
    (integrable_const (300+∑t∈Finset.range K,RegisterPopulationCurrentParentContinuation.tailInflow 195 (9/4) t))
    (ae_of_all fullLaw hb)
  rw [integral_finsetSum _ (fun t _=>actual_cost_integrable t)] at hi
  simpa using hi


end
end FinalMeanResourceRole
#print axioms FinalMeanResourceRole.initial_in_original_carrier
#print axioms FinalMeanResourceRole.original_mean
#print axioms FinalMeanResourceRole.same_actual_marginal
#print axioms FinalMeanResourceRole.same_actual_mean

#print axioms FinalMeanResourceRole.list_actual_cost_bounds
#print axioms FinalMeanResourceRole.actual_cost_bounds
#print axioms FinalMeanResourceRole.actual_cost_measurable
#print axioms FinalMeanResourceRole.actual_cost_integrable
#print axioms FinalMeanResourceRole.original_expected_accounting_role

#print axioms FinalMeanResourceRole.same_actual_finite_horizon
