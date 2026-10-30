import UEOT
set_option maxRecDepth 32768
namespace IndependentDynamicLifecycle
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

-- This type is EXPLICITLY primitive iidSource, not a deploymentKernel law equality.
theorem primitive_pq (noise : PMF Bool) :
    let parent:=postProbeParent port low raw seed
    let p:=returnedAST port (classify (1/5) (1/8) (3/4) (1/6) (sourceData low (1/8) raw))
    let q:=returnedProgram port p
    QuantitativeHomeostasis port false 4 parent noise (1/4) eps_ok p ∧
    QuantitativeHomeostasis (0 : Fin 1) false 4 (projectOrganism port parent) noise (1/4) eps_ok q :=
  accepted_repair_actual_homeostasis port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) raw seed rfl false repair_choice

theorem native_god (noise : PMF Bool) :
    IsBellmanGODSelector (model port noise low (priceValue (1/5) (by norm_num)) (1/4) eps_ok ((3/4 : ℚ) : ℝ) (by norm_num))
      (interpret (returnedAST port (classify (1/5) (1/8) (3/4) (1/6) (sourceData low (1/8) raw)))) :=by
  have h:=actual_good_returned_program port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6)
    (by norm_num) (by norm_num) (by norm_num) raw seed rfl (independent_good noise)
    (by rw [repair_choice];decide)
  exact h.2.1

theorem native_same_joint_parent_and_p6 (noise : PMF Bool) :
    ∀ᵐ p ∂jointLaw (N:=72) port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) seed,
      wholeRecords port low seed p∈SameParentTrace seed.history ∧
      ResourceViable (1/3) (fun _=>(5 : ℝ)) (fun t=>(wholeRecords port low seed p t).transaction.expenditure) ∧
      ∀t,(wholeRecords port low seed p t).transaction.expenditure≤balance port low seed (1/3) 5 p t+5 :=
  funded_joint_same_parent port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) seed (9/2) 5 (1/3)
    (by norm_num [low]) (by norm_num) (by norm_num)

example (noise : PMF Bool) :
    (fundedLaw (N:=72) port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) seed (1/3) 5).map Prod.fst=
      jointLaw port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) seed :=fundedLaw_erasure _ _ _ _ _ _ _ _ _ _ _ _

-- This is the P5 ORGANIZATIONAL clock; no identification with literal ticks.
theorem damaged_parent_p12 :
    let parent:=postProbeParent port low raw seed
    let os : OntogeneticSeed (State 5) Bool:=⟨parent.physical,false⟩
    let start:=PMF.pure (assembleRepairOrganization (substrate port) RegisterFaultSource.codec os)
    let S:=finiteJointRecurrentHomeostasisSystem
      (physical port) (target port false) (target_fixed port false) (certificate port false)
      (substrate port) RegisterFaultSource.codec false (compiled_dynamics_implements port false)
      (RegisterFaultSource.fault port) (1/4) eps_ok (RegisterFaultSource.actual_fault_envelope port false)
    parentView seed.history (assembleRepairOrganization (substrate port) RegisterFaultSource.codec os)=parent ∧
    UEOT.V3.ViabilityKernel.StaysIn start S.carrier ∧
    ∀k s,s∈(homeostaticMarginal S.mixedKernel start k).support →
      (lineage port).SameObject (parentView seed.history s) parent :=
  actual_post_parent_p12_carrier port low (1/4) eps_ok raw seed rfl

example : other.physical=seed.physical ∧ other.program=seed.program :=⟨rfl,rfl⟩
example : (probeTrace port low raw seed (registration 72)).map (recordObservation (1/8))=
    (probeTrace port low raw other (registration 72)).map (recordObservation (1/8)) :=by
  rw [actual_probe_trace_observations port low (1/8) raw seed rfl,actual_probe_trace_observations port low (1/8) raw other rfl]

theorem no_shared_batch_decoder :
    ¬∃ decode : Batch 72→List Bool,
      decode (sourceData low (1/8) raw)=(postProbeParent port low raw seed).history ∧
      decode (sourceData low (1/8) raw)=(postProbeParent port low raw other).history :=
  no_batch_decoder_of_distinct_parent_histories port low (1/8) raw seed other (by decide)

theorem no_uniform_ae_parent_decoder (noise : PMF Bool) :
    ¬∃ decode : Batch 72→List Bool,
      (∀ᵐ w ∂rawLaw noise (1/4) eps_ok 72,decode (sourceData low (1/8) w)=(postProbeParent port low w seed).history) ∧
      (∀ᵐ w ∂rawLaw noise (1/4) eps_ok 72,decode (sourceData low (1/8) w)=(postProbeParent port low w other).history) :=
  no_batch_ae_decoder_of_distinct_parent_histories 72 port noise low (1/4) eps_ok (1/8) seed other (by decide)

example (noise : PMF Bool) (decode : Batch 72→List Bool) :
    1≤(rawLaw noise (1/4) eps_ok 72).real {w | decode (sourceData low (1/8) w)≠(postProbeParent port low w seed).history}+
      (rawLaw noise (1/4) eps_ok 72).real {w | decode (sourceData low (1/8) w)≠(postProbeParent port low w other).history} :=
  batch_parent_error_sum_ge_one 72 port noise low (1/4) eps_ok (1/8) seed other (by decide) decode

#print axioms literal_trace_data
#print axioms same_native_risk
#print axioms risk_nonvacuous
#print axioms raw_word_positive
#print axioms primitive_pq
#print axioms native_god
#print axioms native_same_joint_parent_and_p6
#print axioms damaged_parent_p12
#print axioms no_shared_batch_decoder
#print axioms no_uniform_ae_parent_decoder
end
end IndependentDynamicLifecycle
