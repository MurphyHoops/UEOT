import UEOT
set_option maxRecDepth 32768
namespace IndependentHistoryPrice
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.Objecthood UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
open RegisterFaultJointRecord RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite
open RegisterFaultDynamicProbe RegisterFaultDynamicProbeInfinite RegisterFaultDynamicProbeResource RegisterFaultDynamicProbeLifecycle
open RegisterInstructionPurposeScale RegisterActuatorScaleSource RegisterSemanticInstructionScale
open RegisterInstructionRecoveryScale RegisterInstructionHomeostasis
open UEOT.V3.BoundedLossSampling
open scoped BigOperators ENNReal
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩

-- Independently frozen complete 144-coordinate FORMAL fixture, not sampling.
def raw : Coordinate 72→Bool×Bool:=fun j=>(decide (j.2.val%4≠3),decide (j.2.val%5=1))
def visible (k : ℕ) : Batch 72:=fun j=>(decide (j.2.val%4≠3) && !j.1,if j.2.val%4≠3 then k else 0)
def low : Mechanism:=⟨false,4⟩
def high : Mechanism:=⟨false,20⟩
def seed : Organism 5:=⟨[true,false,false,true,true],fun _=>true,false⟩
def other : Organism 5:={seed with history:=[false,true,false]}
abbrev port : Fin 5:=4
theorem eps_ok : (1/4 : NNReal)≤1 :=by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)
theorem low_bin : feeBin (1/8) low.writeCost=32 :=by norm_num [feeBin,low]
theorem high_bin : feeBin (1/8) high.writeCost=160 :=by norm_num [feeBin,high]

theorem low_data : sourceData low (1/8) raw=visible 32 :=by
  funext j
  rcases j with ⟨b,k⟩
  have hg : low.goal=false:=rfl
  cases b <;> by_cases hk : k.val%4≠3 <;>
    simp only [sourceData,feature,raw,hk,decide_false,low_bin] <;>
    simp [visible,hg,hk]
theorem high_data : sourceData high (1/8) raw=visible 160 :=by
  funext j
  rcases j with ⟨b,k⟩
  have hg : high.goal=false:=rfl
  cases b <;> by_cases hk : k.val%4≠3 <;>
    simp only [sourceData,feature,raw,hk,decide_false,high_bin] <;>
    simp [visible,hg,hk]
theorem mean_target (k : ℕ) : birthMean (visible k) false=3/4 :=by
  change birthMean (visible 0) false=3/4
  decide +kernel
theorem mean_wrong (k : ℕ) : birthMean (visible k) true=0 :=by simp [birthMean,visible]
theorem repair_choice : classify (1/5) (1/8) (3/4) (1/6) (sourceData low (1/8) raw)=.repair false :=by
  rw [low_data]
  decide +kernel
theorem idle_choice : classify (1/5) (1/8) (3/4) (1/6) (sourceData high (1/8) raw)=.idle false :=by
  rw [high_data]
  decide +kernel

theorem literal_trace_data : (probeTrace port low raw seed (registration 72)).map (recordObservation (1/8))=
    (registration 72).map (sourceData low (1/8) raw) :=actual_probe_trace_observations port low (1/8) raw seed rfl _
example : (probeTrace port low raw seed (registration 72)).length=144 :=by
  have hl (js : List (Coordinate 72)) (o : Organism 5) : (probeTrace port low raw o js).length=js.length :=by
    induction js generalizing o with
    | nil=>rfl
    | cons j js ih=>simpa only [probeTrace,List.length_cons] using congrArg Nat.succ (ih _)
  rw [hl,registration_length]
example : (postProbeParent port low raw seed).physical port=true :=rfl
example : (postProbeParent port low raw seed).history=seed.history :=postProbeParent_history port low raw seed
example : (postProbeParent port low raw seed).program=false :=postProbeParent_program port low raw seed
example : postProbeParent port low raw seed=(probeTrace port low raw seed (registration 72)).foldl (fun _ r=>r.transaction.parentAfter) seed :=postProbeParent_trace _ _ _ _

-- Mechanism provenance needs a true birth, not the Good calibration event.
example : false=low.goal :=accepted_repair_bit low (1/5) (1/8) (3/4) (1/6) raw false repair_choice
example : restorationCheck port low.goal (returnedAST port (classify (1/5) (1/8) (3/4) (1/6) (sourceData low (1/8) raw)))=true :=
  accepted_repair_restores port low (1/5) (1/8) (3/4) (1/6) raw false repair_choice
example : returnedAST port (classify (1/5) (1/8) (3/4) (1/6) (sourceData low (1/8) raw))=compile port false :=by rw [repair_choice];rfl
example : restorationCheck port high.goal (returnedAST port (classify (1/5) (1/8) (3/4) (1/6) (sourceData high (1/8) raw)))=false :=
  accepted_idle_not_restoring port high (1/5) (1/8) (3/4) (1/6) raw false idle_choice

theorem independent_good (noise : PMF Bool) : raw∈Good noise low (1/4) eps_ok 72 (1/8) ((1/6 : ℚ) : ℝ) :=by
  intro b
  change |empiricalRisk birthScore (sourceSample low (1/8) b) raw-
    trueRisk (row noise low (1/4) eps_ok (1/8) b).toMeasure birthScore|≤((1/6 : ℚ) : ℝ)
  rw [←birthMean_source,birth_mean,low_data]
  cases b <;> norm_num [mean_wrong,mean_target,low,repairChance]

theorem same_native_risk (noise : PMF Bool) :
    (jointLaw (N:=72) port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) seed).real
      (Prod.fst ⁻¹' Error (N:=72) port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) (by norm_num) (by norm_num))≤
      min 1 (4*Real.exp (-4)) :=by
  have h:=actual_joint_accepted_wrong_bound port noise low (1/4) eps_ok 72 (by decide)
    (1/5) (1/8) (3/4) (1/6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) seed
  convert h using 1
  norm_num

theorem risk_nonvacuous : 4*Real.exp (-(4 : ℝ))<1 :=by
  rw [Real.exp_neg,←div_eq_mul_inv]
  exact (div_lt_one (Real.exp_pos _)).mpr (by linarith [Real.add_one_lt_exp (show (4 : ℝ)≠0 by norm_num)])

def labels : PMF Bool:=PMF.uniformOfFintype Bool
theorem raw_word_positive : 0<rawLaw labels (1/4) eps_ok 72 {raw} :=by
  rw [rawLaw,VariableRegisteredSamples.productRowLaw,Measure.pi_singleton]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rcases j with ⟨b,k⟩
  cases hm : decide (k.val%4≠3) <;> cases hl : decide (k.val%5=1) <;>
    norm_num [raw,hm,hl,labels,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance]

open UEOT.V3.EvolutionPrice
open RegisterFaultJointRecord RegisterFaultDynamicProbePopulation RegisterFaultDynamicProbeHistoryPrice
open RegisterPopulationHistorySource (Store Request)

theorem actual_repair : classify (1/5) (1/8) (3/4) (1/6) (sourceData low (1/8) raw)=.repair false :=repair_choice

def word : Fin 3→Bool×Bool:=fun j=>if j.val=1 then (false,false) else (true,false)
def emptyWord : Fin 3→Bool×Bool:=fun _=>(false,false)
def S : Store 5:=afterFirst port low (1/5) (1/8) (3/4) (1/6) raw seed word
def p : Instruction 5:=returnedAST port (classify (1/5) (1/8) (3/4) (1/6) (sourceData low (1/8) raw))
def acts : ℕ→Action:=cohortActions p S
def ms : ℕ→Bool:=RegisterFaultDynamicProbeHistoryPrice.modes word
def ls : ℕ→Bool:=RegisterFaultDynamicProbeHistoryPrice.labels word
instance : NeZero S.length:=⟨by rw [S,afterFirst_length];decide⟩

theorem actual_post_shape : postProbeParent port low raw seed=seed :=by
  have hh:=RegisterFaultDynamicProbeLifecycle.postProbeParent_history port low raw seed
  have hp:=postProbeParent_program port low raw seed
  have hx : (postProbeParent port low raw seed).physical=seed.physical :=by
    funext j
    fin_cases j <;> rfl
  cases h : postProbeParent port low raw seed
  simp only [h] at hh hp hx
  cases hh
  cases hp
  cases hx
  rfl



theorem actual_first_request :
    astRequest p (registeredParent port low raw seed) 0 true false=⟨0,some false,true,false⟩ :=by
  rw [p,actual_repair,returnedAST]
  simp only [astRequest,registeredParent,actual_post_shape]
  simp [RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.lookup,compile,interpret,seed]

theorem actual_prefix_store : S=RegisterOwnProgramPopulation.next port low.writeCost
    (registeredParent port low raw seed) ⟨0,some false,true,false⟩ :=by
  change RegisterOwnProgramPopulation.next port low.writeCost (registeredParent port low raw seed)
    (astRequest p (registeredParent port low raw seed) 0 true false)=_
  rw [actual_first_request]

def concreteS : Store 5:=RegisterOwnProgramPopulation.next port low.writeCost
    (RegisterPopulationHistorySource.founders [seed]) ⟨0,some false,true,false⟩
theorem actual_store_shape : S=concreteS :=by
  rw [actual_prefix_store]
  simp only [registeredParent,actual_post_shape]
  rfl

theorem actual_requests : requests port low (1/5) (1/8) (3/4) (1/6) raw seed word=
    [⟨0,some false,true,false⟩,⟨0,none,false,false⟩,⟨1,none,true,false⟩] :=by
  rw [requests_actual_ast]
  rw [actual_repair,returnedAST]
  simp only [astEpisode,astRequest,registeredParent,actual_post_shape]
  norm_num [word,
    RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.lookup,
    RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.mechanism,
    RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.child,
    RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
    birthEvent,repairEvent,execute_compiled,compile,interpret,update,seed]



private theorem occupied (j : Fin S.length) : RegisterPopulationTypePrice.occupied S j :=by
  have hj : j.val=0 ∨ j.val=1 :=by
    have h:=j.isLt
    have hlen : S.length=2:=afterFirst_length _ _ _ _ _ _ _ _ _
    omega
  unfold RegisterPopulationTypePrice.occupied
  simp only [actual_store_shape]
  rcases hj with hj | hj <;>
    norm_num [hj,concreteS,
      RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.child,RegisterOwnProgramPopulation.mechanism,
      RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.child,RegisterPopulationHistorySource.transaction,
      RegisterPopulationHistorySource.lookup,registeredParent,actual_post_shape,RegisterPopulationHistorySource.founders,
      RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,birthEvent,repairEvent,execute_compiled,update,seed]



theorem actual_parent_count : RegisterPopulationTypePrice.parentCount S=2 :=by
  unfold RegisterPopulationTypePrice.parentCount
  simp only [occupied,Finset.filter_true]
  change Fintype.card (Fin 2)=2
  rfl



theorem actual_depths : parentDepth S 0=1 ∧ parentDepth S 1=2 :=by
  have hlen : S.length=2:=afterFirst_length _ _ _ _ _ _ _ _ _
  unfold parentDepth
  simp only [actual_store_shape]
  norm_num [hlen,concreteS,
    RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.child,RegisterOwnProgramPopulation.mechanism,
    RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.child,RegisterPopulationHistorySource.transaction,
    RegisterPopulationHistorySource.lookup,registeredParent,actual_post_shape,RegisterPopulationHistorySource.founders,
    RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,birthEvent,repairEvent,execute_compiled,update,seed]



theorem actual_born_iff (j : Fin S.length) : RegisterPopulationTypePrice.born port low S acts ms ls j ↔ j.val=1 :=by
  have hj : j.val=0 ∨ j.val=1 :=by
    have h:=j.isLt
    have hlen : S.length=2:=afterFirst_length _ _ _ _ _ _ _ _ _
    omega
  unfold RegisterPopulationTypePrice.born RegisterPopulationTypePrice.offspring RegisterPopulationTypePrice.before
  simp only [actual_store_shape]
  rcases hj with hj | hj <;>
    norm_num [hj,concreteS,
      RegisterPopulationTypePrice.cohortRequests,RegisterPopulationTypePrice.request,RegisterPopulationHistorySource.run,
      actual_store_shape,concreteS,acts,ms,ls,cohortActions,astRequest,p,actual_repair,returnedAST,
      RegisterFaultDynamicProbeHistoryPrice.modes,RegisterFaultDynamicProbeHistoryPrice.labels,word,
      RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.child,RegisterOwnProgramPopulation.mechanism,
      RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.child,RegisterPopulationHistorySource.transaction,
      RegisterPopulationHistorySource.lookup,registeredParent,actual_post_shape,RegisterPopulationHistorySource.founders,
      RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,birthEvent,repairEvent,execute_compiled,compile,interpret,update,seed,
      List.range_succ]

theorem actual_birth_count : RegisterPopulationTypePrice.birthCount port low S acts ms ls=1 :=by
  unfold RegisterPopulationTypePrice.birthCount
  rw [Fintype.card_subtype]
  simp only [actual_born_iff]
  change (Finset.univ.filter (fun j : Fin 2=>j.val=1)).card=1
  decide

theorem actual_frequencies : RegisterPopulationTypePrice.frequency S 0=1/2 ∧ RegisterPopulationTypePrice.frequency S 1=1/2 :=by
  constructor <;> rw [RegisterPopulationTypePrice.frequency,if_pos (occupied _),actual_parent_count] <;> norm_num

theorem actual_parent_mean : weightedMean (RegisterPopulationTypePrice.frequency S) (parentDepth S)=3/2 :=by
  unfold weightedMean
  change (∑j : Fin 2,RegisterPopulationTypePrice.frequency S j*parentDepth S j)=3/2
  rw [Fin.sum_univ_two]
  change RegisterPopulationTypePrice.frequency S 0*parentDepth S 0+RegisterPopulationTypePrice.frequency S 1*parentDepth S 1=3/2
  rw [actual_frequencies.1,actual_frequencies.2,actual_depths.1,actual_depths.2]
  norm_num

theorem actual_mean_fertility : weightedMean (RegisterPopulationTypePrice.frequency S)
    (RegisterPopulationTypePrice.fertility port low S acts ms ls)=1/2 :=by
  rw [RegisterPopulationTypePrice.mean_fertility_eq,actual_parent_count,actual_birth_count]
  norm_num

theorem actual_selection_term : weightedCov (RegisterPopulationTypePrice.frequency S)
    (RegisterPopulationTypePrice.fertility port low S acts ms ls) (parentDepth S) /
    weightedMean (RegisterPopulationTypePrice.frequency S) (RegisterPopulationTypePrice.fertility port low S acts ms ls)=1/2 :=by
  unfold weightedCov
  rw [actual_mean_fertility,actual_parent_mean]
  unfold weightedMean
  change ((∑j : Fin 2,RegisterPopulationTypePrice.frequency S j*
    (RegisterPopulationTypePrice.fertility port low S acts ms ls j*parentDepth S j))-(1/2)*(3/2))/(1/2)=1/2
  rw [Fin.sum_univ_two]
  change (RegisterPopulationTypePrice.frequency S 0*(RegisterPopulationTypePrice.fertility port low S acts ms ls 0*parentDepth S 0)+
    RegisterPopulationTypePrice.frequency S 1*(RegisterPopulationTypePrice.fertility port low S acts ms ls 1*parentDepth S 1)-(1/2)*(3/2))/(1/2)=1/2
  rw [actual_frequencies.1,actual_frequencies.2,actual_depths.1,actual_depths.2]
  have hlen : S.length=2:=afterFirst_length _ _ _ _ _ _ _ _ _
  simp [RegisterPopulationTypePrice.fertility,actual_born_iff,hlen]
  norm_num

theorem actual_nonconstant_price : actualMeanDepth port low S acts ms ls-3/2=1/2+1 :=by
  have h:=actual_history_price_selection_plus_one port low S acts ms ls
    (by rw [actual_birth_count];decide)
  rw [actual_parent_mean,actual_selection_term] at h
  exact h

theorem actual_child_mean : actualMeanDepth port low S acts ms ls=3 :=by
  linarith [actual_nonconstant_price]

theorem actual_transmission_term :
    weightedMean (RegisterPopulationTypePrice.frequency S)
      (fun j=>RegisterPopulationTypePrice.fertility port low S acts ms ls j *
        (transmittedTrait (RegisterPopulationTypePrice.transmission port low S acts ms ls
          (by rw [actual_birth_count];decide))
          (childDepth port low S acts ms ls) j-parentDepth S j)) /
      weightedMean (RegisterPopulationTypePrice.frequency S)
        (RegisterPopulationTypePrice.fertility port low S acts ms ls)=1 :=
  actual_history_transmission_one _ _ _ _ _ _ _

def events : List Request:=requests port low (1/5) (1/8) (3/4) (1/6) raw seed word
def at0 : Fin events.length:=⟨0,by rw [events,actual_requests];decide⟩
def at1 : Fin events.length:=⟨1,by rw [events,actual_requests];decide⟩
def at2 : Fin events.length:=⟨2,by rw [events,actual_requests];decide⟩

theorem actual_pairs_and_failed_slot :
    RegisterOwnProgramPopulation.observedChildID port low.writeCost (registeredParent port low raw seed) events at0=some 1 ∧
    RegisterOwnProgramPopulation.actualParent port low.writeCost (registeredParent port low raw seed) events at0=some 0 ∧
    RegisterOwnProgramPopulation.observedChildID port low.writeCost (registeredParent port low raw seed) events at1=none ∧
    RegisterOwnProgramPopulation.observedChildID port low.writeCost (registeredParent port low raw seed) events at2=some 3 ∧
    RegisterOwnProgramPopulation.actualParent port low.writeCost (registeredParent port low raw seed) events at2=some 1 :=by
  unfold RegisterOwnProgramPopulation.observedChildID RegisterOwnProgramPopulation.actualParent
    RegisterOwnProgramPopulation.childAt RegisterOwnProgramPopulation.storeBefore
  simp only [events,actual_requests,at0,at1,at2,
    registeredParent,actual_post_shape]
  norm_num [RegisterPopulationHistorySource.requestAt,RegisterOwnProgramPopulation.run,
    RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.lookup,
    RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.child,RegisterOwnProgramPopulation.mechanism,
    RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.child,
    RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
    birthEvent,repairEvent,execute_compiled,compile,interpret,update,seed]

theorem actual_first_failed_slot_missing :
    RegisterPopulationHistorySource.lookup
      (afterFirst port low (1/5) (1/8) (3/4) (1/6) raw seed emptyWord) 1=none :=
  first_failure_slot_missing _ _ _ _ _ _ _ _ _ rfl

theorem registered_word_positive : 0<rawLaw labels (1/4) eps_ok 72 {raw} :=raw_word_positive

theorem actual_future_mass : RegisterRotatingBodySource.roundLaw 3 IndependentHistoryPrice.labels (1/4) eps_ok {word}=9/512 :=by
  rw [RegisterRotatingBodySource.roundLaw,Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [Fin.prod_univ_succ,word,IndependentHistoryPrice.labels,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance,ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

theorem actual_empty_future_mass : RegisterRotatingBodySource.roundLaw 3 IndependentHistoryPrice.labels (1/4) eps_ok {emptyWord}=1/512 :=by
  rw [RegisterRotatingBodySource.roundLaw,Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [Fin.prod_univ_succ,emptyWord,IndependentHistoryPrice.labels,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance,ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

theorem actual_positive_joint : 0 < experimentLaw IndependentHistoryPrice.labels (1/4) eps_ok 72 ({raw}×ˢ{word}) :=by
  unfold experimentLaw
  rw [Measure.prod_prod,actual_future_mass]
  exact ENNReal.mul_pos registered_word_positive.ne' (by norm_num)

theorem actual_empty_joint_positive : 0 < experimentLaw IndependentHistoryPrice.labels (1/4) eps_ok 72 ({raw}×ˢ{emptyWord}) :=by
  unfold experimentLaw
  rw [Measure.prod_prod,actual_empty_future_mass]
  exact ENNReal.mul_pos registered_word_positive.ne' (by norm_num)

def emptyS : Store 5:=afterFirst port low (1/5) (1/8) (3/4) (1/6) raw seed emptyWord

theorem actual_empty_birth_count : RegisterPopulationTypePrice.birthCount port low emptyS
    (cohortActions p emptyS) (RegisterFaultDynamicProbeHistoryPrice.modes emptyWord)
    (RegisterFaultDynamicProbeHistoryPrice.labels emptyWord)=0 :=by
  have hm : RegisterFaultDynamicProbeHistoryPrice.modes emptyWord=(fun _=>false) :=by
    funext j
    simp [RegisterFaultDynamicProbeHistoryPrice.modes,emptyWord]
  rw [hm]
  exact RegisterPopulationTypePrice.all_faults_birthCount_zero _ _ _ _ _

theorem actual_literal_fees :
    (RegisterActuatorPopulationScale.transactionTrace port low.writeCost
      (registeredParent port low raw seed) events).map (fun r=>r.map (fun r=>r.expenditure))=
        [some (4 : ℝ),some 0,some 0] :=by
  simp only [events,actual_requests,registeredParent,actual_post_shape]
  norm_num [RegisterActuatorPopulationScale.transactionTrace,RegisterOwnProgramPopulation.transaction,
    RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.lookup,
    RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.child,RegisterOwnProgramPopulation.mechanism,
    RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.child,
    RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
    birthEvent,repairEvent,execute_compiled,compile,interpret,update,seed,cost,low]

theorem empty_requests : requests port low (1/5) (1/8) (3/4) (1/6) raw seed emptyWord=
    [⟨0,some false,false,false⟩,⟨0,some false,false,false⟩,⟨1,none,false,false⟩] :=by
  rw [requests_actual_ast]
  rw [actual_repair,returnedAST]
  simp only [astEpisode,astRequest,registeredParent,actual_post_shape]
  norm_num [emptyWord,
    RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.lookup,
    RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.mechanism,
    RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.child,
    RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
    birthEvent,repairEvent,execute_compiled,compile,interpret,update,seed]


theorem actual_empty_literal_fees :
    (RegisterActuatorPopulationScale.transactionTrace port low.writeCost
      (registeredParent port low raw seed)
      (requests port low (1/5) (1/8) (3/4) (1/6) raw seed emptyWord)).map
        (fun r=>r.map (fun r=>r.expenditure))=
        [some (0 : ℝ),some 0,none] :=by
  simp only [empty_requests,registeredParent,actual_post_shape]
  norm_num [RegisterActuatorPopulationScale.transactionTrace,RegisterOwnProgramPopulation.transaction,
    RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.lookup,
    RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.child,RegisterOwnProgramPopulation.mechanism,
    RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.child,
    RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
    birthEvent,repairEvent,execute_compiled,compile,interpret,update,seed,cost,low]

example : IsProbabilityMeasure (experimentRecords (N:=72) port IndependentHistoryPrice.labels low
    (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) seed) :=inferInstance

#print axioms empty_requests
#print axioms actual_empty_literal_fees

#print axioms actual_empty_birth_count
#print axioms actual_literal_fees

#print axioms actual_pairs_and_failed_slot
#print axioms actual_transmission_term
#print axioms actual_positive_joint
#print axioms actual_empty_joint_positive
#print axioms actual_first_failed_slot_missing

#print axioms actual_requests
#print axioms actual_depths
#print axioms actual_birth_count
#print axioms actual_selection_term
#print axioms actual_nonconstant_price
-- SAME unfiltered experiment includes the opposite realized selection sign.
-- TTF uses the SAME first real child/store, so no founder or raw Batch changes.
def ttf : Fin 3→Bool×Bool:=fun j=>if j.val=2 then (false,false) else (true,false)
def msTTF : ℕ→Bool:=RegisterFaultDynamicProbeHistoryPrice.modes ttf
def lsTTF : ℕ→Bool:=RegisterFaultDynamicProbeHistoryPrice.labels ttf
theorem ttf_born_iff (j : Fin S.length) : RegisterPopulationTypePrice.born port low S acts msTTF lsTTF j ↔ j.val=0 :=by
  have hj : j.val=0 ∨ j.val=1 :=by
    have h:=j.isLt
    have hlen : S.length=2:=afterFirst_length _ _ _ _ _ _ _ _ _
    omega
  unfold RegisterPopulationTypePrice.born RegisterPopulationTypePrice.offspring RegisterPopulationTypePrice.before
  simp only [actual_store_shape]
  rcases hj with hj | hj <;>
    norm_num [hj,concreteS,
      RegisterPopulationTypePrice.cohortRequests,RegisterPopulationTypePrice.request,RegisterPopulationHistorySource.run,
      actual_store_shape,concreteS,acts,msTTF,lsTTF,cohortActions,astRequest,p,actual_repair,returnedAST,
      RegisterFaultDynamicProbeHistoryPrice.modes,RegisterFaultDynamicProbeHistoryPrice.labels,ttf,
      RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.child,RegisterOwnProgramPopulation.mechanism,
      RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.child,RegisterPopulationHistorySource.transaction,
      RegisterPopulationHistorySource.lookup,registeredParent,actual_post_shape,RegisterPopulationHistorySource.founders,
      RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,birthEvent,repairEvent,execute_compiled,compile,interpret,update,seed,
      List.range_succ]

theorem ttf_birth_count : RegisterPopulationTypePrice.birthCount port low S acts msTTF lsTTF=1 :=by
  unfold RegisterPopulationTypePrice.birthCount
  rw [Fintype.card_subtype]
  simp only [ttf_born_iff]
  change (Finset.univ.filter (fun j : Fin 2=>j.val=0)).card=1
  decide

theorem ttf_mean_fertility : weightedMean (RegisterPopulationTypePrice.frequency S)
    (RegisterPopulationTypePrice.fertility port low S acts msTTF lsTTF)=1/2 :=by
  rw [RegisterPopulationTypePrice.mean_fertility_eq,actual_parent_count,ttf_birth_count]
  norm_num

theorem ttf_negative_selection : weightedCov (RegisterPopulationTypePrice.frequency S)
    (RegisterPopulationTypePrice.fertility port low S acts msTTF lsTTF) (parentDepth S) /
    weightedMean (RegisterPopulationTypePrice.frequency S) (RegisterPopulationTypePrice.fertility port low S acts msTTF lsTTF)= -1/2 :=by
  unfold weightedCov
  rw [ttf_mean_fertility,actual_parent_mean]
  unfold weightedMean
  change ((∑j : Fin 2,RegisterPopulationTypePrice.frequency S j*
    (RegisterPopulationTypePrice.fertility port low S acts msTTF lsTTF j*parentDepth S j))-(1/2)*(3/2))/(1/2)= -1/2
  rw [Fin.sum_univ_two]
  change (RegisterPopulationTypePrice.frequency S 0*(RegisterPopulationTypePrice.fertility port low S acts msTTF lsTTF 0*parentDepth S 0)+
    RegisterPopulationTypePrice.frequency S 1*(RegisterPopulationTypePrice.fertility port low S acts msTTF lsTTF 1*parentDepth S 1)-(1/2)*(3/2))/(1/2)= -1/2
  rw [actual_frequencies.1,actual_frequencies.2,actual_depths.1,actual_depths.2]
  have hlen : S.length=2:=afterFirst_length _ _ _ _ _ _ _ _ _
  simp [RegisterPopulationTypePrice.fertility,ttf_born_iff,hlen]
  norm_num


theorem ttf_core_price : actualMeanDepth port low S acts msTTF lsTTF-3/2= -1/2+1 :=by
  have h:=actual_history_price_selection_plus_one port low S acts msTTF lsTTF
    (by rw [ttf_birth_count];decide)
  rw [actual_parent_mean,ttf_negative_selection] at h
  exact h

theorem exact_same_full_joint_mass : experimentLaw IndependentHistoryPrice.labels (1/4) eps_ok 72 ({raw}×ˢ{word})=
    rawLaw IndependentHistoryPrice.labels (1/4) eps_ok 72 {raw}*(9/512) :=by
  unfold experimentLaw
  rw [Measure.prod_prod,actual_future_mass]

theorem exact_same_empty_joint_mass : experimentLaw IndependentHistoryPrice.labels (1/4) eps_ok 72 ({raw}×ˢ{emptyWord})=
    rawLaw IndependentHistoryPrice.labels (1/4) eps_ok 72 {raw}*(1/512) :=by
  unfold experimentLaw
  rw [Measure.prod_prod,actual_empty_future_mass]

example : (experimentLaw IndependentHistoryPrice.labels (1/4) eps_ok 72).fst=
    rawLaw IndependentHistoryPrice.labels (1/4) eps_ok 72 :=experimentLaw_training_marginal _ _ _ _

theorem ttf_future_mass : RegisterRotatingBodySource.roundLaw 3 IndependentHistoryPrice.labels (1/4) eps_ok {ttf}=9/512 :=by
  rw [RegisterRotatingBodySource.roundLaw,Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [Fin.prod_univ_succ,ttf,IndependentHistoryPrice.labels,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance,ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

theorem ttf_full_joint_positive : 0<experimentLaw IndependentHistoryPrice.labels (1/4) eps_ok 72 ({raw}×ˢ{ttf}) :=by
  unfold experimentLaw
  rw [Measure.prod_prod,ttf_future_mass]
  exact ENNReal.mul_pos registered_word_positive.ne' (by norm_num)

#print axioms ttf_full_joint_positive

#print axioms ttf_negative_selection
#print axioms ttf_core_price
#print axioms exact_same_full_joint_mass
#print axioms exact_same_empty_joint_mass

end
end IndependentHistoryPrice
