import UEOT
set_option maxRecDepth 16384
namespace IndependentParentDiscovery
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

abbrev port : Fin 2:=0
theorem repair_choice : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) rawWord)=.repair true :=by
  rw [low_actual_data];exact low_new
open RegisterFaultDynamicProbeLifecycle

open RegisterPopulationJournalLearning

def allNormal : Fin 3→Bool×Bool:=fun _=>(true,false)
def allFault : Fin 3→Bool×Bool:=fun _=>(false,false)
def firstFault : Fin 3→Bool×Bool:=fun j=>(decide (j.val≠0),false)
def middleFault : Fin 3→Bool×Bool:=fun j=>(decide (j.val≠1),false)
def requests (h : Bool) (w : Fin 3→Bool×Bool) := RegisterFaultDynamicProbeParentDiscovery.episode port low (1/2) (1/4) (1/2) (1/4) rawWord initial h w

theorem actual_post_parent : postProbeParent port low rawWord initial=initial :=by
  have hp : (postProbeParent port low rawWord initial).physical=initial.physical :=by funext j;fin_cases j <;> rfl
  have hh:=postProbeParent_history port low rawWord initial
  have hc:=postProbeParent_program port low rawWord initial
  cases he : postProbeParent port low rawWord initial with
  | mk hs xs bs=>simp only [he] at hp hh hc;rw [show hs=initial.history from hh,show xs=initial.physical from hp,show bs=initial.program from hc]

theorem third_two_real_owners :
    RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) rawWord initial false allNormal=some 0 ∧
    RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) rawWord initial true allNormal=some 1 :=by
  constructor <;> simp only [RegisterFaultDynamicProbeParentDiscovery.actualParent, RegisterOwnProgramPopulation.actualParent, RegisterOwnProgramPopulation.childAt, RegisterFaultDynamicProbeParentDiscovery.episode, repair_choice, RegisterFaultDynamicProbeParentDiscovery.third] <;> decide +kernel

theorem third_failed_slot_none :
    RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) rawWord initial true firstFault=none :=by
  simp only [RegisterFaultDynamicProbeParentDiscovery.actualParent, RegisterOwnProgramPopulation.actualParent, RegisterOwnProgramPopulation.childAt, RegisterFaultDynamicProbeParentDiscovery.episode, repair_choice, RegisterFaultDynamicProbeParentDiscovery.third]
  decide +kernel

-- A nonempty episode need NOT give the target third event an offspring.
theorem earlier_birth_does_not_supply_missing_third :
    (RegisterFaultDynamicProbeParentDiscovery.targetChild port low (1/2) (1/4) (1/2) (1/4) rawWord initial true firstFault 1).isSome=true ∧
    RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) rawWord initial true firstFault=none :=by
  constructor <;> simp only [RegisterFaultDynamicProbeParentDiscovery.actualParent, RegisterOwnProgramPopulation.actualParent, RegisterOwnProgramPopulation.childAt, RegisterFaultDynamicProbeParentDiscovery.targetChild, RegisterFaultDynamicProbeParentDiscovery.episode, repair_choice, RegisterFaultDynamicProbeParentDiscovery.third, RegisterFaultDynamicProbeParentDiscovery.eventIndex] <;> decide +kernel

theorem all_failed_nochild (h : Bool) :
    RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) rawWord initial h allFault=none :=by
  cases h <;> simp only [RegisterFaultDynamicProbeParentDiscovery.actualParent, RegisterOwnProgramPopulation.actualParent, RegisterOwnProgramPopulation.childAt, RegisterFaultDynamicProbeParentDiscovery.episode, repair_choice, RegisterFaultDynamicProbeParentDiscovery.third] <;> decide +kernel

-- Complete fresh source model, not a conditional law of successful outcomes.
theorem actual_joint_bound (noise : PMF Bool) (h : Bool) (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (e : Fin 3) :
    (RegisterFaultDynamicProbeParentDiscovery.jointLaw noise (1/4) eps_ok confuser 64 64).real {z |
      RegisterFaultDynamicProbeParentDiscovery.estimate (RegisterFaultDynamicProbeParentDiscovery.targetSensed port low (1/2) (1/4) (1/2) (1/4) z.1.1 initial h z.1.2 e z.2)≠
        RegisterFaultDynamicProbeParentDiscovery.targetParent port low (1/2) (1/4) (1/2) (1/4) z.1.1 initial h z.1.2 e}≤Real.exp (-(8 : ℝ)) :=by
  convert RegisterFaultDynamicProbeParentDiscovery.target_joint_parent_risk_le (N:=64) port noise low (1/4) eps_ok (1/2) (1/4) (1/2) (1/4) initial h e confuser 64 using 1; norm_num

theorem actual_episode_p12 (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3) (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) :
    Filter.Tendsto (fun B=>(RegisterPopulationJournalLearning.rawLaw (1/4) eps_ok confuser B).real {reads |
      RegisterFaultDynamicProbeParentDiscovery.estimate (RegisterFaultDynamicProbeParentDiscovery.targetSensed port low (1/2) (1/4) (1/2) (1/4) rawWord initial h w e reads)≠
        RegisterFaultDynamicProbeParentDiscovery.targetParent port low (1/2) (1/4) (1/2) (1/4) rawWord initial h w e}) Filter.atTop (nhds 0) :=
  RegisterFaultDynamicProbeParentDiscovery.target_episode_p12 port low (1/2) (1/4) (1/2) (1/4) rawWord initial h w e confuser

theorem actual_bridge (h : Bool) (w : Fin 3→Bool×Bool) :
    InverseObjecthood.ObjectClassParentBridge
      (RegisterOwnProgramJournalLearning.childJournalClass port low.writeCost (RegisterFaultDynamicProbePopulation.registeredParent port low rawWord initial) (requests h w))
      (RegisterOwnProgramPopulation.actualParent port low.writeCost (RegisterFaultDynamicProbePopulation.registeredParent port low rawWord initial) (requests h w)) :=
  RegisterFaultDynamicProbeParentDiscovery.actual_episode_parent_bridge port low (1/2) (1/4) (1/2) (1/4) rawWord initial h w

theorem candidate_not_extra_founder (h : Bool) (w : Fin 3→Bool×Bool) :
    let s:=RegisterFaultDynamicProbePopulation.registeredParent port low rawWord initial
    let p:=returnedAST port (classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) rawWord))
    RegisterPopulationHistorySource.lookup (RegisterOwnProgramPopulation.storeBefore port low.writeCost s (requests h w) 2) 1=
      RegisterOwnProgramPopulation.child port low.writeCost s (RegisterFaultDynamicProbePopulation.astRequest p s 0 (w 0).1 (w 0).2) :=
  RegisterFaultDynamicProbeParentDiscovery.candidate_one_is_first_birth port low (1/2) (1/4) (1/2) (1/4) rawWord initial h w

-- All64 reads are retained; one actual rawWord read word witnesses Good.
def honestReads : Raw RegisterFaultDynamicProbeParentDiscovery.Class 64:=fun _=>(true,0)
theorem honest_good : honestReads∈Good (J:=RegisterFaultDynamicProbeParentDiscovery.Class) 64 :=by
  simp [RegisterPopulationJournalLearning.Good,correctCount,honestReads]

theorem executable_selected_parent (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3) :
    RegisterFaultDynamicProbeParentDiscovery.estimate (RegisterFaultDynamicProbeParentDiscovery.targetSensed port low (1/2) (1/4) (1/2) (1/4) rawWord initial h w e honestReads)=
      RegisterFaultDynamicProbeParentDiscovery.targetParent port low (1/2) (1/4) (1/2) (1/4) rawWord initial h w e :=
  RegisterFaultDynamicProbeParentDiscovery.good_target_estimate_actual port low (1/2) (1/4) (1/2) (1/4) rawWord initial h w e honestReads honest_good

example : RegisterFaultDynamicProbeParentDiscovery.estimate (RegisterFaultDynamicProbeParentDiscovery.sensed port low (1/2) (1/4) (1/2) (1/4) rawWord initial false allNormal honestReads)=some 0 :=by
  rw [RegisterFaultDynamicProbeParentDiscovery.good_estimate_actual port low (1/2) (1/4) (1/2) (1/4) rawWord initial _ _ honestReads honest_good, third_two_real_owners.1]
example : RegisterFaultDynamicProbeParentDiscovery.estimate (RegisterFaultDynamicProbeParentDiscovery.sensed port low (1/2) (1/4) (1/2) (1/4) rawWord initial true allNormal honestReads)=some 1 :=by
  rw [RegisterFaultDynamicProbeParentDiscovery.good_estimate_actual port low (1/2) (1/4) (1/2) (1/4) rawWord initial _ _ honestReads honest_good, third_two_real_owners.2]
example : RegisterFaultDynamicProbeParentDiscovery.estimate (RegisterFaultDynamicProbeParentDiscovery.sensed port low (1/2) (1/4) (1/2) (1/4) rawWord initial true firstFault honestReads)=none :=by
  rw [RegisterFaultDynamicProbeParentDiscovery.good_estimate_actual port low (1/2) (1/4) (1/2) (1/4) rawWord initial _ _ honestReads honest_good, third_failed_slot_none]

-- Zero reads return None regardless of a genuine birth; no vacuous discovery.
example (data : Data 0) : RegisterFaultDynamicProbeParentDiscovery.estimate data=none :=RegisterFaultDynamicProbeParentDiscovery.estimate_zero data
example (data : Data 0) : RegisterFaultDynamicProbeParentDiscovery.estimate data≠RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) rawWord initial true allNormal :=by
  rw [RegisterFaultDynamicProbeParentDiscovery.estimate_zero,third_two_real_owners.2];decide

-- Incorrect reads may produce false positives on an actual failed birth.
def falsePositiveReads : Raw RegisterFaultDynamicProbeParentDiscovery.Class 3:=fun _=>(false,1)
example : RegisterFaultDynamicProbeParentDiscovery.estimate (RegisterFaultDynamicProbeParentDiscovery.sensed port low (1/2) (1/4) (1/2) (1/4) rawWord initial true firstFault falsePositiveReads)=some 0 :=by
  simp only [RegisterFaultDynamicProbeParentDiscovery.sensed, RegisterFaultDynamicProbeParentDiscovery.truth, RegisterFaultDynamicProbeParentDiscovery.actualChild, RegisterFaultDynamicProbeParentDiscovery.episode]
  decide +kernel

example : RegisterFaultDynamicProbeParentDiscovery.readCharge (1/20) 64=(16/5 : ℝ) :=by
  rw [RegisterFaultDynamicProbeParentDiscovery.readCharge_exact];norm_num

-- Allowed unmarked observation explicitly omits ancestry lists and owner edge.
-- It INCLUDES the full original Batch and returned AST, actual serial childUID, physical/protected code, action, birth,
-- fee and label/mode at all three ticks. UID is not full ancestry identity.
def bareRecord (j : ℕ) (r : Option (RegisterTimestampedBirthSource.ClockedRecord 2)) :=
  r.map (fun r=>(r.parentBefore.organism.physical,r.parentBefore.organism.program,
    r.action,r.repairMode,r.label,r.parentAfter.organism.physical,r.parentAfter.organism.program,
    r.child.map (fun c=>(j+1,c.organism.physical,c.organism.program)),r.expenditure))
abbrev Bare := List (Option ((State 2)×Bool×Action×Bool×Bool×(State 2)×Bool×Option (ℕ×(State 2)×Bool)×ℝ))
abbrev Visible := Batch 64 × Instruction 2 × Bare
def bareSource (h : Bool) (z : RegisterFaultDynamicProbeParentDiscovery.EpisodeRaw 64) : Visible :=
  (sourceData low (1/4) z.1, returnedAST port (classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1)),
  (RegisterActuatorPopulationScale.transactionTrace port low.writeCost
    (RegisterFaultDynamicProbePopulation.registeredParent port low z.1 initial)
    (RegisterFaultDynamicProbeParentDiscovery.episode port low (1/2) (1/4) (1/2) (1/4) z.1 initial h z.2)).mapIdx bareRecord)
def bareObservation (h : Bool) (w : Fin 3→Bool×Bool) := bareSource h (rawWord,w)

theorem same_unmarked_actual_records : bareObservation false allNormal=bareObservation true allNormal :=by
  simp only [bareObservation,bareSource,RegisterFaultDynamicProbeParentDiscovery.episode,repair_choice]
  simp only [RegisterFaultDynamicProbePopulation.registeredParent,actual_post_parent]
  norm_num [RegisterOwnProgramPopulation.child,RegisterPopulationHistorySource.child,RegisterPopulationHistorySource.founders,RegisterActuatorPopulationScale.transactionTrace,RegisterFaultDynamicProbePopulation.astEpisode,RegisterFaultDynamicProbePopulation.astRequest,RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.transaction,RegisterOwnProgramPopulation.mechanism,RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.lookup,RegisterTimestampedBirthSource.step,RegisterFaultJointRecord.modeRecordStep,RegisterJointRecord.recordStep,RegisterRepairHistory.birthEvent,RegisterRepairHistory.repairEvent,RegisterRepairSource.update,RegisterMechanismPurpose.cost,bareRecord,RegisterFaultDynamicProbeParentDiscovery.plan,RegisterFaultDynamicProbeParentDiscovery.address,allNormal,low,initial,RegisterFaultDynamicProbe.returnedAST,RegisterRepairSource.compile,RegisterRepairSource.interpret]

-- The equal visible value below occurs at a supported atom of the ORIGINAL
-- positive-noise full input law, not a conditioned/success-selected source.
local instance : MeasurableSpace (List (Option ((State 2)×Bool×Action×Bool×Bool×(State 2)×Bool×Option (ℕ×(State 2)×Bool)×ℝ))) := ⊤
theorem no_mark_parent_not_function
    (f : Visible→Option ℕ) :
    ¬(f (bareObservation false allNormal)=some 0 ∧ f (bareObservation true allNormal)=some 1) :=by
  rw [same_unmarked_actual_records]
  rintro ⟨ha,hb⟩
  have : (some (0 : ℕ))=some 1:=ha.symm.trans hb
  contradiction

def inputLaw : Measure (RegisterFaultDynamicProbeParentDiscovery.EpisodeRaw 64) :=
  RegisterFaultDynamicProbeHistoryPrice.experimentLaw (PMF.pure false) (1/4) eps_ok 64
instance inputLaw_probability : IsProbabilityMeasure inputLaw :=by unfold inputLaw;infer_instance

theorem original_atom_positive : 0 < inputLaw {(rawWord,allNormal)} :=by
  have hraw : 0<RegisterFaultFinitePurposeProbe.rawLaw (PMF.pure false) (1/4) eps_ok 64 {rawWord} :=by
    rw [RegisterFaultFinitePurposeProbe.rawLaw,VariableRegisteredSamples.productRowLaw,Measure.pi_singleton]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    rcases j with ⟨b,k⟩
    by_cases hk : k.val<48 <;> norm_num [rawWord,hk,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance]
  have hfuture : 0<RegisterRotatingBodySource.roundLaw 3 (PMF.pure false) (1/4) eps_ok {allNormal} :=by
    rw [RegisterRotatingBodySource.roundLaw,Measure.pi_singleton]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    norm_num [allNormal,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance]
  have hs : {(rawWord,allNormal)}=({rawWord}×ˢ{allNormal}) :=by ext z;simp
  rw [inputLaw,RegisterFaultDynamicProbeHistoryPrice.experimentLaw,hs,Measure.prod_prod]
  exact ENNReal.mul_pos hraw.ne' hfuture.ne'

theorem original_atom_real_positive : 0< inputLaw.real {(rawWord,allNormal)} :=
  ENNReal.toReal_pos (ne_of_gt original_atom_positive) (measure_ne_top _ _)

/-- Any deterministic unmarked decoder has a strictly positive finite error
sum under the two ORIGINAL complete positive-noise source hypotheses. Only
one supported common observation is needed; no full-law equality is claimed. -/
theorem positive_noise_unmarked_error_floor
    (f : Visible→Option ℕ) :
    inputLaw.real {(rawWord,allNormal)}≤
      inputLaw.real {z | f (bareSource false z)≠RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) z.1 initial false z.2}+
      inputLaw.real {z | f (bareSource true z)≠RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) z.1 initial true z.2} :=by
  have hor : f (bareObservation false allNormal)≠some 0 ∨ f (bareObservation true allNormal)≠some 1 :=by
    by_contra hh
    push Not at hh
    exact no_mark_parent_not_function f hh
  rcases hor with ha|hb
  · have hm : inputLaw.real {(rawWord,allNormal)}≤ inputLaw.real {z | f (bareSource false z)≠RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) z.1 initial false z.2} :=by
      apply measureReal_mono
      · intro z hz
        obtain rfl:=Set.mem_singleton_iff.mp hz
        simpa only [Set.mem_ofPred_eq,Prod.fst,Prod.snd,bareObservation,third_two_real_owners.1] using ha
      · exact measure_ne_top _ _
    exact hm.trans (le_add_of_nonneg_right measureReal_nonneg)
  · have hm : inputLaw.real {(rawWord,allNormal)}≤ inputLaw.real {z | f (bareSource true z)≠RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) z.1 initial true z.2} :=by
      apply measureReal_mono
      · intro z hz
        obtain rfl:=Set.mem_singleton_iff.mp hz
        simpa only [Set.mem_ofPred_eq,Prod.fst,Prod.snd,bareObservation,third_two_real_owners.2] using hb
      · exact measure_ne_top _ _
    exact hm.trans (le_add_of_nonneg_left measureReal_nonneg)

-- Marked half-noise has a stronger full-N read-law statistical obstruction.
theorem half_noise_full_read_obstruction (B : ℕ) (f : Data B→RegisterPopulationJournalLearning.Observation) :
    observedLaw (1/2) (by exact_mod_cast (by norm_num : (1/2 : ℝ)≤1)) (PMF.pure (2 : RegisterFaultDynamicProbeParentDiscovery.Class)) RegisterFaultDynamicProbeParentDiscovery.mark 1 B=
      observedLaw (1/2) (by exact_mod_cast (by norm_num : (1/2 : ℝ)≤1)) (PMF.pure (1 : RegisterFaultDynamicProbeParentDiscovery.Class)) RegisterFaultDynamicProbeParentDiscovery.mark 2 B ∧
    1≤(observedLaw (1/2) (by exact_mod_cast (by norm_num : (1/2 : ℝ)≤1)) (PMF.pure (2 : RegisterFaultDynamicProbeParentDiscovery.Class)) RegisterFaultDynamicProbeParentDiscovery.mark 1 B).real {data | f data≠some 0}+
      (observedLaw (1/2) (by exact_mod_cast (by norm_num : (1/2 : ℝ)≤1)) (PMF.pure (1 : RegisterFaultDynamicProbeParentDiscovery.Class)) RegisterFaultDynamicProbeParentDiscovery.mark 2 B).real {data | f data≠some 1} :=by
  exact ⟨half_noise_observed_swap RegisterFaultDynamicProbeParentDiscovery.mark 1 2 B,
    half_noise_parent_risk_sum RegisterFaultDynamicProbeParentDiscovery.mark 1 2 (some 0) (some 1) (by decide) B f⟩

#print axioms third_two_real_owners
#print axioms earlier_birth_does_not_supply_missing_third
#print axioms actual_joint_bound
#print axioms actual_episode_p12
#print axioms actual_bridge
#print axioms candidate_not_extra_founder
#print axioms executable_selected_parent
#print axioms same_unmarked_actual_records
#print axioms original_atom_positive
#print axioms original_atom_real_positive
#print axioms positive_noise_unmarked_error_floor
#print axioms no_mark_parent_not_function
#print axioms half_noise_full_read_obstruction
-- Actual registered read budget64 can produce a false positive. A learner
-- secretly filling from actualParent would incorrectly pass this boundary.
def falsePositive64 : Raw RegisterFaultDynamicProbeParentDiscovery.Class 64:=fun _=>(false,1)
theorem fixed64_executable_false_positive :
    RegisterFaultDynamicProbeParentDiscovery.estimate
      (RegisterFaultDynamicProbeParentDiscovery.sensed port low (1/2) (1/4) (1/2) (1/4) rawWord initial true firstFault falsePositive64)=some 0 ∧
    RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) rawWord initial true firstFault=none :=by
  refine ⟨?_,third_failed_slot_none⟩
  change RegisterFaultDynamicProbeParentDiscovery.estimate (fun _=>some 0)=some 0
  decide +kernel

theorem false_positive_read_atom_positive :
    0 < RegisterPopulationJournalLearning.rawLaw (1/4) eps_ok
      (PMF.pure (1 : RegisterFaultDynamicProbeParentDiscovery.Class)) 64 {falsePositive64} :=by
  rw [RegisterPopulationJournalLearning.rawLaw,VariableRegisteredSamples.productRowLaw,Measure.pi_singleton]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [falsePositive64,RegisterPopulationJournalLearning.primitive_apply,modeLaw,
    FiniteProbabilityRow.ofRealRow,modeProbability,repairChance]

theorem actual_read_account_limits_budget (B : ℕ)
    (h : RegisterFaultDynamicProbeParentDiscovery.readCharge (1/20) B≤(16/5 : ℝ)) : B≤64 :=by
  rw [RegisterFaultDynamicProbeParentDiscovery.readCharge_exact] at h
  have hh : (B : ℝ)≤64 :=by norm_num at h;nlinarith
  exact_mod_cast hh

local instance : MeasurableSpace RegisterPopulationJournalLearning.Observation:=⊤
local instance : MeasurableSingletonClass RegisterPopulationJournalLearning.Observation:=⟨fun _=>trivial⟩

-- Every pre-registered e gets its OWN product channel; this is not a claim
-- of simultaneous discovery of three events using one64-reading budget.
theorem any_target_actual_product (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3)
    (eta : NNReal) (he : eta≤1) (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (B : ℕ) :
    (RegisterPopulationJournalLearning.rawLaw eta he confuser B).map
      (RegisterFaultDynamicProbeParentDiscovery.targetSensed port low (1/2) (1/4) (1/2) (1/4) rawWord initial h w e)=
      VariableRegisteredSamples.productRowLaw (fun _ : Unit=>sensorLaw eta he confuser
        RegisterFaultDynamicProbeParentDiscovery.mark
        (RegisterFaultDynamicProbeParentDiscovery.targetTruth port low (1/2) (1/4) (1/2) (1/4) rawWord initial h w e)) (fun _=>B) :=
  observedLaw_product eta he confuser _ _ B

-- The common supported TTT observation is not a global pointwise identity
-- of bare sources: middlefault causes different next actions/fees for h0/h1.
theorem other_supported_word_has_different_bare_observation :
    bareObservation false middleFault≠bareObservation true middleFault :=by
  simp only [bareObservation,bareSource,RegisterFaultDynamicProbeParentDiscovery.episode,repair_choice]
  simp only [RegisterFaultDynamicProbePopulation.registeredParent,actual_post_parent]
  norm_num [RegisterOwnProgramPopulation.child,RegisterPopulationHistorySource.child,RegisterPopulationHistorySource.founders,RegisterActuatorPopulationScale.transactionTrace,RegisterFaultDynamicProbePopulation.astEpisode,RegisterFaultDynamicProbePopulation.astRequest,RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.transaction,RegisterOwnProgramPopulation.mechanism,RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.lookup,RegisterTimestampedBirthSource.step,RegisterFaultJointRecord.modeRecordStep,RegisterJointRecord.recordStep,RegisterRepairHistory.birthEvent,RegisterRepairHistory.repairEvent,RegisterRepairSource.update,RegisterMechanismPurpose.cost,bareRecord,RegisterFaultDynamicProbeParentDiscovery.plan,RegisterFaultDynamicProbeParentDiscovery.address,middleFault,low,initial,RegisterFaultDynamicProbe.returnedAST,RegisterRepairSource.compile,RegisterRepairSource.interpret]

#print axioms fixed64_executable_false_positive
#print axioms false_positive_read_atom_positive
#print axioms actual_read_account_limits_budget
#print axioms any_target_actual_product
#print axioms other_supported_word_has_different_bare_observation

-- Genuine source provenance at BOTH nontrivial hidden choices, not a class
-- assigned to an assumed child or a second founder.
theorem actual_third_birth_witness (h : Bool) :
    ∃child : RegisterTimestampedBirthSource.ClockedOrganism 2,
      RegisterFaultDynamicProbeParentDiscovery.actualChild port low (1/2) (1/4) (1/2) (1/4) rawWord initial h allNormal=some child ∧
      let s:=RegisterOwnProgramPopulation.storeBefore port low.writeCost
        (RegisterFaultDynamicProbePopulation.registeredParent port low rawWord initial) (requests h allNormal) 2
      let q:=RegisterPopulationHistorySource.requestAt (requests h allNormal)
        (RegisterFaultDynamicProbeParentDiscovery.third port low (1/2) (1/4) (1/2) (1/4) rawWord initial h allNormal)
      ∃parent,RegisterPopulationHistorySource.lookup s (RegisterFaultDynamicProbeParentDiscovery.address h)=some parent ∧
        (RegisterFaultJointRecord.modeRecordStep port ⟨parent.organism.program,low.writeCost⟩ parent.organism q.action q.mode q.label).transaction.child=some child.organism ∧
        child.organism.program=parent.organism.program :=by
  have hp : RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) rawWord initial h allNormal=
      some (RegisterFaultDynamicProbeParentDiscovery.address h) :=by
    cases h
    · exact third_two_real_owners.1
    · exact third_two_real_owners.2
  unfold RegisterFaultDynamicProbeParentDiscovery.actualParent RegisterOwnProgramPopulation.actualParent at hp
  rw [RegisterFaultDynamicProbeParentDiscovery.third_dispatch] at hp
  change (RegisterFaultDynamicProbeParentDiscovery.actualChild port low (1/2) (1/4) (1/2) (1/4) rawWord initial h allNormal).map
    (fun _=>RegisterFaultDynamicProbeParentDiscovery.address h)=some (RegisterFaultDynamicProbeParentDiscovery.address h) at hp
  obtain ⟨child,hc,_⟩:=Option.map_eq_some_iff.mp hp
  exact ⟨child,hc,RegisterFaultDynamicProbeParentDiscovery.actual_third_birth_source port low (1/2) (1/4) (1/2) (1/4) rawWord initial h allNormal child hc⟩

theorem high_idle_no_target_child (h : Bool) (e : Fin 3) :
    RegisterFaultDynamicProbeParentDiscovery.targetParent port high (1/2) (1/4) (1/2) (1/4) rawWord initial h allNormal e=none :=by
  have hi : classify (1/2) (1/4) (1/2) (1/4) (sourceData high (1/4) rawWord)=.idle true :=by
    rw [high_actual_data];exact high_new
  cases h <;> fin_cases e <;>
    simp only [RegisterFaultDynamicProbeParentDiscovery.targetParent,RegisterOwnProgramPopulation.actualParent,
      RegisterOwnProgramPopulation.childAt,RegisterFaultDynamicProbeParentDiscovery.episode,hi,
      RegisterFaultDynamicProbeParentDiscovery.eventIndex] <;> decide +kernel

#print axioms actual_third_birth_witness
#print axioms high_idle_no_target_child

-- Finite-budget false positives are not merely a possible raw word: the
-- SAME complete joint law gives the actual wrong-output event positive risk.
theorem finite64_actual_false_positive_risk_positive :
    0 < (RegisterFaultDynamicProbeParentDiscovery.jointLaw (PMF.pure false) (1/4) eps_ok
      (PMF.pure (1 : RegisterFaultDynamicProbeParentDiscovery.Class)) 64 64).real {z |
      RegisterFaultDynamicProbeParentDiscovery.estimate
        (RegisterFaultDynamicProbeParentDiscovery.sensed port low (1/2) (1/4) (1/2) (1/4) z.1.1 initial true z.1.2 z.2)≠
      RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) z.1.1 initial true z.1.2} :=by
  have hraw : 0<RegisterFaultFinitePurposeProbe.rawLaw (PMF.pure false) (1/4) eps_ok 64 {rawWord} :=by
    rw [RegisterFaultFinitePurposeProbe.rawLaw,VariableRegisteredSamples.productRowLaw,Measure.pi_singleton]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    rcases j with ⟨b,k⟩
    by_cases hk : k.val<48 <;> norm_num [rawWord,hk,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance]
  have hfuture : 0<RegisterRotatingBodySource.roundLaw 3 (PMF.pure false) (1/4) eps_ok {firstFault} :=by
    rw [RegisterRotatingBodySource.roundLaw,Measure.pi_singleton]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    by_cases hj : j.val≠0 <;> norm_num [firstFault,hj,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance]
  have hworld : 0 < inputLaw {(rawWord,firstFault)} :=by
    have hs : {(rawWord,firstFault)}=({rawWord}×ˢ{firstFault}) :=by ext z;simp
    rw [inputLaw,RegisterFaultDynamicProbeHistoryPrice.experimentLaw,hs,Measure.prod_prod]
    exact ENNReal.mul_pos hraw.ne' hfuture.ne'
  have hatom : 0<(RegisterFaultDynamicProbeParentDiscovery.jointLaw (PMF.pure false) (1/4) eps_ok
      (PMF.pure (1 : RegisterFaultDynamicProbeParentDiscovery.Class)) 64 64)
      ({(rawWord,firstFault)}×ˢ{falsePositive64}) :=by
    rw [RegisterFaultDynamicProbeParentDiscovery.jointLaw,Measure.prod_prod]
    exact ENNReal.mul_pos hworld.ne' false_positive_read_atom_positive.ne'
  apply ENNReal.toReal_pos
  · apply ne_of_gt (lt_of_lt_of_le hatom (measure_mono ?_))
    rintro ⟨world,reads⟩ ⟨hw,hr⟩
    obtain rfl:=Set.mem_singleton_iff.mp hw
    obtain rfl:=Set.mem_singleton_iff.mp hr
    change RegisterFaultDynamicProbeParentDiscovery.estimate
      (RegisterFaultDynamicProbeParentDiscovery.sensed port low (1/2) (1/4) (1/2) (1/4) rawWord initial true firstFault falsePositive64)≠
        RegisterFaultDynamicProbeParentDiscovery.actualParent port low (1/2) (1/4) (1/2) (1/4) rawWord initial true firstFault
    rw [fixed64_executable_false_positive.1,fixed64_executable_false_positive.2]
    decide
  · exact measure_ne_top _ _

#print axioms finite64_actual_false_positive_risk_positive

end
end IndependentParentDiscovery
