import UEOT
set_option maxRecDepth 16384
namespace UEOTP9SixIndependent
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

-- SAME immutable 6/16-per-row raw word, with the ORIGINAL existing width1/4 protocol.
-- This is a separate identity-matching formal reuse check, not a change to the width1/100 registration.
-- In this original coarser read the old low-cost verdict is UNKNOWN; no old idle fact is transported across bins.
def rawWord : Coordinate 8→Bool×Bool:=fun j=>if j.2.val<6 then (true,true) else (false,true)
def visible (k : ℕ) : Batch 8:=fun j=>(decide (j.2.val<6) && j.1,if j.2.val<6 then k else 0)
def low : Mechanism:=⟨true,21/10⟩
def high : Mechanism:=⟨true,7⟩
def initial : Organism 2:=⟨[false,true],(fun j=>if j=0 then false else true),true⟩
theorem half_price : priceValue (1/2) (by norm_num)=(1/2 : NNReal) :=by
  unfold priceValue
  apply Subtype.ext
  change ((1/2 : ℚ) : ℝ)=(1/2 : ℝ)
  norm_num
theorem eps_ok : (1/4 : NNReal)≤1:=by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)
theorem low_bin : feeBin (1/4) low.writeCost=8:=by norm_num [feeBin,low]
theorem high_bin : feeBin (1/4) high.writeCost=28:=by norm_num [feeBin,high]

theorem low_actual_data : sourceData low (1/4) rawWord=visible 8 :=by
  funext j
  rcases j with ⟨b,k⟩
  have hgoal : low.goal=true:=rfl
  cases b <;> by_cases hk : k.val<6 <;>
    simp only [sourceData,feature,rawWord,hk,if_true,if_false,low_bin] <;>
    simp [visible,hgoal,hk]
theorem high_actual_data : sourceData high (1/4) rawWord=visible 28 :=by
  funext j
  rcases j with ⟨b,k⟩
  have hgoal : high.goal=true:=rfl
  cases b <;> by_cases hk : k.val<6 <;>
    simp only [sourceData,feature,rawWord,hk,if_true,if_false,high_bin] <;>
    simp [visible,hgoal,hk]

theorem mean_true (k : ℕ) : birthMean (visible k) true=3/4 :=by
  change birthMean (visible 0) true=3/4
  decide +kernel
theorem mean_false (k : ℕ) : birthMean (visible k) false=0 :=by simp [birthMean,visible]

theorem low_new : classify (1/2) (1/4) (1/2) (1/4) (visible 8)=.repair true :=by decide +kernel
theorem low_old : select (1/2) (1/4) (visible 8)=.unknown :=by decide +kernel
theorem high_new : classify (1/2) (1/4) (1/2) (1/4) (visible 28)=.idle true :=by decide +kernel

example : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) rawWord)=.repair true :=by rw [low_actual_data];exact low_new
example : select (1/2) (1/4) (sourceData low (1/4) rawWord)=.unknown :=by rw [low_actual_data];exact low_old
example : classify (1/2) (1/4) (1/2) (1/4) (sourceData high (1/4) rawWord)=.idle true :=by rw [high_actual_data];exact high_new

-- Actual original trace/terminal parent, with all 128 transactions retained.
example : (probeTrace (0 : Fin 2) low rawWord initial (registration 8)).map (recordObservation (1/4))=
    (registration 8).map (sourceData low (1/4) rawWord) :=actual_probe_trace_observations 0 low (1/4) rawWord initial rfl _
example : postProbeParent (0 : Fin 2) low rawWord initial=
    (probeTrace 0 low rawWord initial (registration 8)).foldl (fun _ r=>r.transaction.parentAfter) initial :=postProbeParent_trace _ _ _ _
example : (postProbeParent (0 : Fin 2) low rawWord initial).physical 0=false :=rfl
example : (postProbeParent (0 : Fin 2) low rawWord initial).physical 1=true :=rfl
example : (postProbeParent (0 : Fin 2) low rawWord initial).program=true :=postProbeParent_program _ _ _ _

theorem low_good (noise : PMF Bool) : rawWord∈Good noise low (1/4) eps_ok 8 (1/4) ((1/4 : ℚ) : ℝ) :=by
  intro b
  change |empiricalRisk birthScore (sourceSample low (1/4) b) rawWord-
    trueRisk (row noise low (1/4) eps_ok (1/4) b).toMeasure birthScore|≤((1/4 : ℚ) : ℝ)
  rw [←birthMean_source,birth_mean,low_actual_data]
  cases b <;> norm_num [mean_false,mean_true,low,repairChance]
theorem high_good (noise : PMF Bool) : rawWord∈Good noise high (1/4) eps_ok 8 (1/4) ((1/4 : ℚ) : ℝ) :=by
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

open RegisterFaultJointRecord RegisterFaultInfiniteRecord RegisterInstructionScaleSource RegisterInstructionRecoveryScale
open RegisterInstructionNativeSource RegisterFaultDynamicProbeNativeHomeostasis RegisterFaultDynamicProbeLifecycle
open RegisterFaultDynamicProbeResource UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterFaultDynamicProbeP9Terminal RegisterFaultDynamicProbeClocked
open RegisterTimestampedBirthSource (ClockedOrganism Identity)
local instance {n : ℕ} : MeasurableSpace (RegisterTimestampedBirthSource.ClockedRecord n):=⊤
open RegisterActuatorPopulationScale

def founder : ClockedOrganism 2:=⟨initial,[(8,false),(13,true)],17⟩
def postOwner : ClockedOrganism 2:=postClocked 0 low rawWord founder
def actualObj : Carrier (0 : Fin 2):=dataObject 0 low (1/2) (1/4) (1/2) (1/4) rawWord founder

theorem actual_choice : classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) rawWord)=.repair true :=by
  rw [low_actual_data];exact low_new

-- SAME complete N8 input word has positive mass; no selected-success source.
theorem actual_word_positive : 0<rawLaw (PMF.pure true) (1/4) eps_ok 8 {rawWord} :=by
  rw [rawLaw,VariableRegisteredSamples.productRowLaw,Measure.pi_singleton]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rcases j with ⟨b,k⟩
  by_cases hk : k.val<6 <;>
    norm_num [rawWord,hk,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance]

-- Non-total fault is a CONSEQUENCE of this actual supported accepted record.
theorem actual_source_non_total : (1/4 : NNReal)<1 :=
  supported_repair_non_total (PMF.pure true) low (1/4) eps_ok (1/2) (1/4) (1/2) (1/4)
    rawWord actual_word_positive true actual_choice

theorem actual_clock : postOwner.clock=33 :=by
  rw [postOwner,actual_post_clock]
  rfl

theorem actual_owner : postOwner.identity=founder.identity :=actual_post_identity _ _ _ _
example : postOwner.organism=postProbeParent 0 low rawWord initial :=actual_post_erase _ _ _ _
example : postOwner.organism.physical 0=false ∧ postOwner.organism.physical 1=true :=by
  rw [postOwner,actual_post_erase]
  exact ⟨rfl,rfl⟩

theorem actual_complete_probe_erasure :
    (RegisterTimestampedBirthSource.trace (0 : Fin 2) low founder (probeEvents rawWord (registration 8))).map
      RegisterTimestampedBirthSource.eraseRecord=probeTrace 0 low rawWord initial (registration 8) :=
  actual_probe_trace_erase _ _ _ _ _

theorem actual_six : Six (0 : Fin 1) (PMF.pure true) low (priceValue (1/2) (by norm_num)) (1/4) eps_ok
    (1/2) (by norm_num) founder.identity 33 ((clockedScale 0).objectMap actualObj) :=by
  have h:=data_actual_p9_six 0 (PMF.pure true) low (1/4) actual_source_non_total (1/2) (1/4) (1/2) (1/4)
    (by norm_num) (by norm_num) (by norm_num) rawWord founder rfl (low_good _) true actual_choice

  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
  exact h

-- The selected/coarse programs are actual synthesiser outputs and the
-- baseline is a DIFFERENT actual AST and its own actual returned decoder.
example : synthesize (0 : Fin 2) actualObj.2.1.val.1=some actualObj.2.1.val.2 :=actualObj.2.1.property
example : synthesize (0 : Fin 2) actualObj.2.2.val.1=some actualObj.2.2.val.2 :=actualObj.2.2.property
example : actualObj.2.1.val.1≠actualObj.2.2.val.1 :=by
  change returnedAST 0 (classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) rawWord))≠Instruction.emit none
  rw [actual_choice,returnedAST]
  simp [compile]

theorem actual_native_goa_readout :
    (recordPathLaw (0 : Fin 2) (PMF.pure true) low (1/4) eps_ok (astPolicy actualObj.2.1.val.1)
      ⟨0,postOwner.organism.physical,postOwner.organism⟩).map
        (fun rs=>(rs 13).transaction.parentAfter.physical)=
      (RegisterInstructionGOASource.sourceLaw 0 low (1/4) eps_ok postOwner.organism.physical).toMeasure :=
  native_goa_marginal _ _ _ _ _ _ (accepted_repair_restores 0 low (1/2) (1/4) (1/2) (1/4) rawWord true actual_choice) _ _

example : IsProbabilityMeasure (RegisterFaultDynamicProbeClocked.pathLaw (0 : Fin 2) (PMF.pure true) low
    (1/4) eps_ok actualObj.2.1.val.1 postOwner) :=inferInstance

theorem actual_full_clocked_law_erases :
    (RegisterFaultDynamicProbeClocked.pathLaw (0 : Fin 2) (PMF.pure true) low (1/4) eps_ok actualObj.2.1.val.1 postOwner).map
      (fun rs t=>RegisterTimestampedBirthSource.eraseRecord (rs t))=
      recordPathLaw 0 (PMF.pure true) low (1/4) eps_ok (astPolicy actualObj.2.1.val.1)
        ⟨0,postOwner.organism.physical,postOwner.organism⟩ :=actual_path_erases _ _ _ _ _ _ _

example (z : ℕ→List Event) (t : ℕ) :
    (RegisterFaultDynamicProbeClocked.recordAt (0 : Fin 2) low postOwner z t).parentBefore.identity=founder.identity ∧
    (RegisterFaultDynamicProbeClocked.recordAt (0 : Fin 2) low postOwner z t).parentAfter.identity=founder.identity :=by
  rw [←actual_owner]
  exact actual_native_parent_id _ _ _ _ _

example : ∀ᵐ z ∂wordPathLaw (0 : Fin 2) (PMF.pure true) low (1/4) eps_ok (astPolicy actualObj.2.1.val.1)
    ⟨0,postOwner.organism.physical,postOwner.organism⟩,
    ∀t : ℕ,(RegisterFaultDynamicProbeClocked.recordAt 0 low postOwner z t).parentBefore.clock=33+t ∧
      (RegisterFaultDynamicProbeClocked.recordAt 0 low postOwner z t).parentAfter.clock=33+t+1 :=by
  simpa only [actual_clock] using actual_native_clock 0 (PMF.pure true) low (1/4) eps_ok actualObj.2.1.val.1 postOwner


-- Same physical source/data, distinct registered owners: the old selector
-- has not gained an ID oracle from this source-view extension.
def otherFounder : ClockedOrganism 2:={founder with identity:=[(9,false),(12,true)]}
theorem old_batch_no_owner_decoder : ¬∃decode : Batch 8→Identity,
    decode (sourceData low (1/4) rawWord)=(postClocked (0 : Fin 2) low rawWord founder).identity ∧
    decode (sourceData low (1/4) rawWord)=(postClocked (0 : Fin 2) low rawWord otherFounder).identity :=
  no_batch_owner_decoder _ _ _ _ _ _ (by decide)

-- Joint P6/prepay/history, actual native future life and all six coarse
-- terminal semantics refer to this SAME actual registered training source.
theorem actual_joint_terminal :
    ∀ᵐ z ∂jointLaw (N:=8) (0 : Fin 2) (PMF.pure true) low (1/4) eps_ok (1/2) (1/4) (1/2) (1/4) initial,
      wholeRecords 0 low initial z∈SameParentTrace initial.history ∧
      ResourceViable 0 (fun _=>3) (fun t=>(wholeRecords 0 low initial z t).transaction.expenditure) ∧
      (z.1∈Good (PMF.pure true) low (1/4) eps_ok 8 (1/4) ((1/4 : ℚ) : ℝ)→∀b : Bool,
        classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) z.1)=.repair b→
        Six (0 : Fin 1) (PMF.pure true) low (priceValue (1/2) (by norm_num)) (1/4) eps_ok (1/2) (by norm_num)
          founder.identity 33 ((clockedScale 0).objectMap (dataObject 0 low (1/2) (1/4) (1/2) (1/4) z.1 founder))) :=by
  have h:=actual_joint_funded_p9_six (N:=8) (0 : Fin 2) (PMF.pure true) low (1/4) eps_ok
    (1/2) (1/4) (1/2) (1/4) (by norm_num) (by norm_num) (by norm_num) founder rfl
    3 3 0 (by norm_num [low]) (by norm_num) (by norm_num)
  filter_upwards [h] with z hz
  have hs:=hz.2.2.2.2
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hs
  have hclock : founder.clock+16=33:=rfl
  rw [hclock] at hs
  refine ⟨hz.1,hz.2.1,?_⟩
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hs

-- Idle branch remains outside repairability, and a total-fault zero-rate
-- source cannot satisfy the positive-life sixth terminal property.
example : restorationCheck (0 : Fin 2) high.goal
    (returnedAST 0 (classify (1/2) (1/4) (1/2) (1/4) (sourceData high (1/4) rawWord)))=false :=
  accepted_idle_not_restoring 0 high (1/2) (1/4) (1/2) (1/4) rawWord true
    (by rw [high_actual_data];exact high_new)
example (obj : ClockedOrganism 1×Instruction 1×Instruction 1) :
    ¬Six (0 : Fin 1) (PMF.pure true) low 1 1 (by norm_num) (1/2) (by norm_num)
      founder.identity 33 obj :=by
  intro h
  exact (lt_irrefl (1 : NNReal)) h.2.2.2.2.2.1
-- Original P8 source identity really is consumed, independently of Batch.
example : (RegisterTimestampedBirthSource.lineage (0 : Fin 2) low).SameObject postOwner founder :=actual_owner
example : founder.identity.map Prod.snd=initial.history :=by decide
example (z : ℕ→List Event) (t : ℕ) :
    ¬(RegisterTimestampedBirthSource.lineage (0 : Fin 2) low).OffspringOf
      (RegisterTimestampedBirthSource.runParent 0 low postOwner (z t))
      (RegisterFaultDynamicProbeClocked.recordAt 0 low postOwner z t).parentAfter :=
  RegisterTimestampedBirthSource.retained_parent_not_offspring _ _ _ _ _ _

#print axioms actual_six
#print axioms actual_joint_terminal
#print axioms actual_word_positive
#print axioms actual_full_clocked_law_erases
#print axioms old_batch_no_owner_decoder
-- The identical raw accepted word still computes repair at total noise;
-- it has zero source mass, so pointwise non-totality would be false.
theorem total_fault_raw_word_zero :
    rawLaw (PMF.pure true) 1 (by norm_num) 8 {rawWord}=0 :=by
  rw [rawLaw,VariableRegisteredSamples.productRowLaw,Measure.pi_singleton]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨false,(0 : Fin 8)⟩ : Coordinate 8))
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [rawWord,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance]

theorem total_fault_unknown_source : ∀ᵐ omega ∂rawLaw (PMF.pure true) 1 (by norm_num) 8,
    classify (1/2) (1/4) (1/2) (1/4) (sourceData low (1/4) omega)=.unknown :=
  RegisterFaultDynamicProbe.total_fault_unknown_ae _ _ _ _ _ _ _

#print axioms total_fault_raw_word_zero
#print axioms total_fault_unknown_source
end
end UEOTP9SixIndependent
