import UEOT
set_option maxRecDepth 32768
namespace IndependentDataPopulation
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

example (rs : ℕ→ModeRecord 5) : balance port low seed (1/3) 5 (raw,rs) 1=4/3 :=by
  have hf : (wholeRecords port low seed (raw,rs) 0).transaction.expenditure=(low.writeCost : ℝ):=rfl
  simp only [balance,cumulativeResourceBalance,Finset.sum_range_one,hf]
  norm_num [low]


open RegisterFaultDynamicProbePopulation
open RegisterPopulationHistorySource (Store Request)
open RegisterTimestampedBirthSource (ClockedOrganism)

def success : Fin 2→Bool×Bool:=fun _=>(true,false)
def failedFirst : Fin 2→Bool×Bool:=fun j=>if j=0 then (false,false) else (true,false)
def s0 : Store 5:=registeredParent port low raw seed
def p : Instruction 5:=returnedAST port (classify (1/5) (1/8) (3/4) (1/6) (sourceData low (1/8) raw))
def events : List Request:=episode port low (1/5) (1/8) (3/4) (1/6) raw seed success
instance : NeZero events.length:=⟨by rw [events,episode_length];decide⟩

theorem actual_requests : events=[⟨0,some false,true,false⟩,⟨1,none,true,false⟩] :=by
  unfold events episode
  rw [repair_choice,returnedAST]
  rfl

example : (postProbeParent port low raw seed).physical port=true :=rfl
example : RegisterPopulationHistorySource.lookup s0 0=some ⟨postProbeParent port low raw seed,[(0,false)],0⟩ :=registered_lookup _ _ _ _
example : (trace port low (1/5) (1/8) (3/4) (1/6) raw seed success).length=2 :=actual_trace_length _ _ _ _ _ _ _ _ _
example : events=RegisterActuatorPopulationScale.compiledEpisode port low.writeCost s0 (plan success) :=
  actual_episode_eq_compiled port low (1/5) (1/8) (3/4) (1/6) raw seed rfl false repair_choice success

theorem first_erases_same_actual_step (mode label : Bool) :
    (RegisterOwnProgramPopulation.transaction port low.writeCost s0 (astRequest p s0 0 mode label)).map
      RegisterTimestampedBirthSource.eraseRecord=
      some (modeRecordStep port low (postProbeParent port low raw seed)
        (interpret p (postProbeParent port low raw seed).physical) mode label) :=
  actual_first_erasure port low (1/5) (1/8) (3/4) (1/6) raw seed rfl mode label

theorem actual_paid_fees :
    ((trace port low (1/5) (1/8) (3/4) (1/6) raw seed success).map
      (fun r=>r.map RegisterTimestampedBirthSource.ClockedRecord.expenditure))=[some 4,some 0] :=by
  let q0:=astRequest p s0 0 true false
  let s1:=RegisterOwnProgramPopulation.next port low.writeCost s0 q0
  let q1:=astRequest p s1 1 true false
  obtain ⟨c1,c2,hc1,hl,hc2,_⟩:=actual_two_generation_births port low
    (1/5) (1/8) (3/4) (1/6) raw seed rfl false repair_choice false false
  have heq : [q0,q1]=[⟨0,some false,true,false⟩,⟨1,none,true,false⟩]:=actual_requests
  have hq1:=(List.cons.inj (List.cons.inj heq).2).1
  have hf0 : (RegisterOwnProgramPopulation.transaction port low.writeCost s0 q0).map
      RegisterTimestampedBirthSource.ClockedRecord.expenditure=some 4 :=by
    have h:=congrArg (fun rs=>rs.map (fun r : ModeRecord 5=>r.transaction.expenditure)) (first_erases_same_actual_step true false)
    simp only [Option.map_map] at h
    change (RegisterOwnProgramPopulation.transaction port low.writeCost s0 q0).map
      RegisterTimestampedBirthSource.ClockedRecord.expenditure=some _ at h
    have hactive : (postProbeParent port low raw seed).physical port=true:=rfl
    have ha : interpret p (postProbeParent port low raw seed).physical=some false :=by
      unfold p
      rw [repair_choice,returnedAST]
      simp only [compile,interpret,hactive,Bool.true_eq_false,if_false]
    rw [ha] at h
    simpa [modeRecordStep,RegisterJointRecord.recordStep,cost,low] using h
  have hf1 : (RegisterOwnProgramPopulation.transaction port low.writeCost s1 q1).map
      RegisterTimestampedBirthSource.ClockedRecord.expenditure=some 0 :=by
    have ht:=RegisterOwnProgramPopulation.transaction_erasure port low.writeCost s1 q1 c1 hl
    have h:=congrArg (fun rs=>rs.map (fun r : ModeRecord 5=>r.transaction.expenditure)) ht
    simp only [Option.map_map] at h
    change (RegisterOwnProgramPopulation.transaction port low.writeCost s1 q1).map
      RegisterTimestampedBirthSource.ClockedRecord.expenditure=some _ at h
    simpa only [hq1,modeRecordStep,if_true,RegisterJointRecord.recordStep,cost] using h
  change ([RegisterOwnProgramPopulation.transaction port low.writeCost s0 q0,
    RegisterOwnProgramPopulation.transaction port low.writeCost s1 q1].map _)=_
  simp only [List.map_cons,List.map_nil,hf0,hf1]

theorem actual_failed_trace :
    (trace port low (1/5) (1/8) (3/4) (1/6) raw seed failedFirst).map
      (fun r=>r.map RegisterTimestampedBirthSource.ClockedRecord.repairMode)=[some false,none] :=by
  unfold trace episode
  rw [repair_choice,returnedAST]
  rfl

-- These two protocols intentionally differ after a failed first dispatch.
def futureStream : RegisterSemanticInstructionInfinite.Stream:=fun t=>if t=0 then (false,false) else (true,false)
example : (RegisterSemanticInstructionInfinite.recordAt port low p (postProbeParent port low raw seed) futureStream 1).transaction.expenditure=4 :=by
  unfold p
  rw [repair_choice,returnedAST]
  rfl

-- Real child OWN P5, not a replacement child or a literal-clock claim.
def ownP5 (node : ClockedOrganism 5) : Prop:=
  let b:=node.organism.program
  let os : OntogeneticSeed (State 5) Bool:=⟨node.organism.physical,b⟩
  let S:=finiteJointRecurrentHomeostasisSystem
    (physical port) (target port b) (target_fixed port b) (certificate port b)
    (substrate port) RegisterFaultSource.codec b (compiled_dynamics_implements port b)
    (RegisterFaultSource.fault port) (1/4) eps_ok (RegisterFaultSource.actual_fault_envelope port b)
  UEOT.V3.ViabilityKernel.StaysIn (PMF.pure (assembleRepairOrganization (substrate port) RegisterFaultSource.codec os)) S.carrier

theorem two_real_generations_and_ownP5 :
    let q0:=astRequest p s0 0 true false
    let s1:=RegisterOwnProgramPopulation.next port low.writeCost s0 q0
    let q1:=astRequest p s1 1 true false
    ∃c1 c2,RegisterOwnProgramPopulation.child port low.writeCost s0 q0=some c1 ∧
      RegisterPopulationHistorySource.lookup s1 1=some c1 ∧
      RegisterOwnProgramPopulation.child port low.writeCost s1 q1=some c2 ∧
      RegisterOwnProgramPopulation.childID port low.writeCost s0 q0=some 1 ∧
      RegisterOwnProgramPopulation.parentID port low.writeCost s0 q0=some 0 ∧
      RegisterOwnProgramPopulation.childID port low.writeCost s1 q1=some 2 ∧
      RegisterOwnProgramPopulation.parentID port low.writeCost s1 q1=some 1 ∧
      compile port c1.organism.program=p ∧ compile port c2.organism.program=p ∧ ownP5 c1 ∧ ownP5 c2 :=by
  dsimp only
  obtain ⟨c1,c2,hc1,hl,hc2,hi1,hp0,hi2,hp1,hcompile1,hcompile2⟩:=actual_two_generation_births port low
    (1/5) (1/8) (3/4) (1/6) raw seed rfl false repair_choice false false
  refine ⟨c1,c2,hc1,hl,hc2,hi1,hp0,hi2,hp1,hcompile1,hcompile2,?_,?_⟩
  · exact RegisterOwnProgramPopulation.actual_child_enters_own_maintenance port low.writeCost s0 _ c1 hc1 (1/4) eps_ok
  · exact RegisterOwnProgramPopulation.actual_child_enters_own_maintenance port low.writeCost _ _ c2 hc2 (1/4) eps_ok

theorem actual_idle_no_child (mode label : Bool) :
    let s:=registeredParent port high raw seed
    let idle:=returnedAST port (classify (1/5) (1/8) (3/4) (1/6) (sourceData high (1/8) raw))
    RegisterOwnProgramPopulation.child port high.writeCost s (astRequest idle s 0 mode label)=none ∧
      RegisterPopulationHistorySource.lookup (RegisterOwnProgramPopulation.next port high.writeCost s (astRequest idle s 0 mode label)) 1=none :=
  actual_idle_first_none port high (1/5) (1/8) (3/4) (1/6) raw seed rfl false idle_choice (by decide) mode label

-- Only the actual first frozen one-parent cohort supplies this census.
def censusActions : ℕ→Action:=cohortActions p s0
example : RegisterPopulationTypePrice.birthCount port low s0 censusActions (fun _=>true) (fun _=>false)=1 :=
  actual_first_cohort_count port low (1/5) (1/8) (3/4) (1/6) raw seed rfl false repair_choice

theorem actual_first_cohort_Price (z : Bool→ℝ) :
    RegisterPopulationTypePrice.empiricalOffspringMean port low s0 censusActions (fun _=>true) (fun _=>false) z-
      UEOT.V3.EvolutionPrice.weightedMean (RegisterPopulationTypePrice.frequency s0) (RegisterPopulationTypePrice.parentTrait s0 z)=
      UEOT.V3.EvolutionPrice.weightedCov (RegisterPopulationTypePrice.frequency s0)
        (RegisterPopulationTypePrice.fertility port low s0 censusActions (fun _=>true) (fun _=>false)) (RegisterPopulationTypePrice.parentTrait s0 z)/
      UEOT.V3.EvolutionPrice.weightedMean (RegisterPopulationTypePrice.frequency s0)
        (RegisterPopulationTypePrice.fertility port low s0 censusActions (fun _=>true) (fun _=>false)) :=
  actual_first_cohort_price port low (1/5) (1/8) (3/4) (1/6) raw seed rfl false repair_choice z

example (noise : PMF Bool) : IsProbabilityMeasure (inputLaw noise (1/4) eps_ok 72) :=inferInstance
example (noise : PMF Bool) : (inputLaw noise (1/4) eps_ok 72).fst=rawLaw noise (1/4) eps_ok 72 :=inputLaw_training_marginal _ _ _ _
example (noise : PMF Bool) : IsProbabilityMeasure (RegisterFaultDynamicProbePopulation.recordLaw (N:=72) port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) seed) :=inferInstance


def failedSecond : Fin 2→Bool×Bool:=fun j=>if j=0 then (true,false) else (false,false)
example : (trace port low (1/5) (1/8) (3/4) (1/6) raw seed failedSecond).map
    (fun r=>r.map RegisterTimestampedBirthSource.ClockedRecord.repairMode)=[some true,some false] :=by
  unfold trace episode
  rw [repair_choice,returnedAST]
  rfl

theorem future_success_word_mass : RegisterRotatingBodySource.roundLaw 2 labels (1/4) eps_ok {success}=9/64 :=by
  rw [RegisterRotatingBodySource.roundLaw,Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [Fin.prod_univ_succ,success,labels,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance,ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

theorem future_failed_word_mass : RegisterRotatingBodySource.roundLaw 2 labels (1/4) eps_ok {failedFirst}=3/64 :=by
  rw [RegisterRotatingBodySource.roundLaw,Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [Fin.prod_univ_succ,failedFirst,labels,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance,ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

theorem actual_success_positive_joint_mass : 0 < inputLaw labels (1/4) eps_ok 72 ({raw}×ˢ{success}) :=by
  unfold inputLaw
  rw [Measure.prod_prod,future_success_word_mass]
  exact ENNReal.mul_pos raw_word_positive.ne' (by norm_num)
theorem actual_failure_positive_joint_mass : 0 < inputLaw labels (1/4) eps_ok 72 ({raw}×ˢ{failedFirst}) :=by
  unfold inputLaw
  rw [Measure.prod_prod,future_failed_word_mass]
  exact ENNReal.mul_pos raw_word_positive.ne' (by norm_num)

example (noise : PMF Bool) : RegisterRotatingBodyReturns.successMass 2 (1/4)≤
    RegisterRotatingBodySource.roundLaw 2 noise (1/4) eps_ok {w | TwoBorn port low (1/5) (1/8) (3/4) (1/6) raw seed w} :=
  actual_two_generation_mass_lower port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) raw seed rfl false repair_choice

#print axioms first_erases_same_actual_step
#print axioms actual_paid_fees
#print axioms actual_failed_trace
#print axioms two_real_generations_and_ownP5
#print axioms actual_idle_no_child
#print axioms actual_first_cohort_Price
#print axioms actual_success_positive_joint_mass
#print axioms actual_failure_positive_joint_mass
end
end IndependentDataPopulation
