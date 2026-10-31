import UEOT
set_option maxRecDepth 32768
namespace IndependentNativeOrganization
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


open UEOT.V3.DynamicsKernel UEOT.V3.ViabilityTrajectory
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open RegisterFaultInfiniteRecord RegisterFaultNativeOrganization RegisterInstructionGOASource
open RegisterFaultDynamicProbeNativeHomeostasis
local instance : MeasurableSpace (RepairOrganizationState (State 5) Action Bool):=⊤
local instance : MeasurableSingletonClass (RepairOrganizationState (State 5) Action Bool):=⟨fun _=>trivial⟩
local instance : MeasurableSpace (RepairOrganizationState (State 1) Action Bool):=⊤
local instance : MeasurableSingletonClass (RepairOrganizationState (State 1) Action Bool):=⟨fun _=>trivial⟩

def actualParent : Organism 5:=postProbeParent port low raw seed
def chosen : Instruction 5:=returnedAST port (classify (1/5) (1/8) (3/4) (1/6) (sourceData low (1/8) raw))
def actualQ : Instruction 1:=returnedProgram port chosen

theorem checked_chosen : restorationCheck port low.goal chosen=true :=
  accepted_repair_restores port low (1/5) (1/8) (3/4) (1/6) raw false repair_choice

theorem actual_full_organization_law (noise : PMF Bool) :
    (recordPathLaw port noise low (1/4) eps_ok (astPolicy chosen) ⟨0,actualParent.physical,actualParent⟩).map
      (mapPath (readRecord port))=
      homTrajMeasure (Measure.dirac (organization port low actualParent.physical)) (organizationKernel port low (1/4) eps_ok) :=
  actual_record_organization_path_law port noise low (1/4) eps_ok chosen checked_chosen actualParent (postProbeParent_program _ _ _ _)

theorem actual_returned_q_organization_law (noise : PMF Bool) :
    (recordPathLaw (0 : Fin 1) noise low (1/4) eps_ok (astPolicy actualQ)
      ⟨0,(projectOrganism port actualParent).physical,projectOrganism port actualParent⟩).map
      (mapPath (readRecord 0))=
      homTrajMeasure (Measure.dirac (organization 0 low (projectOrganism port actualParent).physical)) (organizationKernel 0 low (1/4) eps_ok) :=
  (accepted_pair_organization_laws port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) raw seed rfl false repair_choice).2

theorem all_actual_time_marginals (noise : PMF Bool) (t : ℕ) :
    (recordPathLaw port noise low (1/4) eps_ok (astPolicy chosen) ⟨0,actualParent.physical,actualParent⟩).map
      (fun rs=>readRecord port (rs t))=
      (homeostaticMarginal (system port low (1/4) eps_ok).mixedKernel
        (PMF.pure (organization port low actualParent.physical)) t).toMeasure :=
  actual_organization_marginal port noise low (1/4) eps_ok chosen checked_chosen actualParent (postProbeParent_program _ _ _ _) t

example (noise : PMF Bool) :
    (recordPathLaw port noise low (1/4) eps_ok (astPolicy chosen) ⟨0,actualParent.physical,actualParent⟩).map
      (fun rs=>readRecord port (rs 0))=(PMF.pure (organization port low actualParent.physical)).toMeasure :=
  all_actual_time_marginals noise 0
example (noise : PMF Bool) :
    (recordPathLaw port noise low (1/4) eps_ok (astPolicy chosen) ⟨0,actualParent.physical,actualParent⟩).map
      (fun rs=>readRecord port (rs 1))=((system port low (1/4) eps_ok).mixedKernel (organization port low actualParent.physical)).toMeasure :=by
  rw [all_actual_time_marginals]
  simp only [homeostaticMarginal_succ,homeostaticMarginal_zero,PMF.pure_bind]
example (noise : PMF Bool) :
    (recordPathLaw port noise low (1/4) eps_ok (astPolicy chosen) ⟨0,actualParent.physical,actualParent⟩).map
      (fun rs=>readRecord port (rs 19))=
      (homeostaticMarginal (system port low (1/4) eps_ok).mixedKernel (PMF.pure (organization port low actualParent.physical)) 19).toMeasure :=
  all_actual_time_marginals noise 19

-- Time0 is the actual damaged post-probe state, not a repaired new seed.
example : (organization port low actualParent.physical).physical port=true :=rfl
example : (organization port low actualParent.physical).repairProgram=actualParent.program :=rfl

-- Readout t is BEFORE transaction t: the actual path defeats two-tick grouping.
def alternating : RegisterSemanticInstructionInfinite.Stream:=fun t=>(decide (t%2=0),false)
example : (readRecord port (RegisterSemanticInstructionInfinite.recordAt port low chosen actualParent alternating 0)).physical port=true :=rfl
example : (readRecord port (RegisterSemanticInstructionInfinite.recordAt port low chosen actualParent alternating 1)).physical port=false :=by
  unfold chosen
  rw [repair_choice,returnedAST]
  rfl
example : (readRecord port (RegisterSemanticInstructionInfinite.recordAt port low chosen actualParent alternating 2)).physical port=true :=by
  unfold chosen
  rw [repair_choice,returnedAST]
  rfl

theorem actual_native_p12_alltimes (noise : PMF Bool) :
    ∀ᵐ rs ∂deploymentKernel port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) seed raw,
      ∀t : ℕ,readRecord port (rs t)∈(system port low (1/4) eps_ok).carrier ∧
        (lineage port).SameObject (parentView seed.history (readRecord port (rs t))) actualParent :=
  actual_post_parent_p12_native port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) raw seed rfl false repair_choice

theorem same_joint_p5_p12_parent_resource_life (noise : PMF Bool) :
    ∀ᵐ z ∂jointLaw (N:=72) port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) seed,
      wholeRecords port low seed z∈SameParentTrace seed.history ∧
      ResourceViable (1/3) (fun _=>5) (fun t=>(wholeRecords port low seed z t).transaction.expenditure) ∧
      (∀t,(wholeRecords port low seed z t).transaction.expenditure≤balance port low seed (1/3) 5 z t+5) ∧
      ∀b : Bool,classify (1/5) (1/8) (3/4) (1/6) (sourceData low (1/8) z.1)=.repair b→
        z.2∈frequency port (1/4) ∧
        ((1/4 : NNReal)<1→∀N : ℕ,∃t≥N,Legitimate port (z.2 t).transaction.parentAfter) ∧
        ∀t : ℕ,readRecord port (z.2 t)∈(system port low (1/4) eps_ok).carrier ∧
          (lineage port).SameObject (parentView seed.history (readRecord port (z.2 t))) (postProbeParent port low z.1 seed) :=
  funded_joint_p5_p12_native port noise low (1/4) eps_ok (1/5) (1/8) (3/4) (1/6) seed rfl
    (9/2) 5 (1/3) (by norm_num [low]) (by norm_num) (by norm_num)

-- This exact reconstruction holds for ANY AST/actual code, without ho.
def wrongParent : Organism 5:={actualParent with program:=true}
def wrongRecord : ModeRecord 5:=modeRecordStep port low wrongParent (interpret chosen wrongParent.physical) true false
example : (readRecord port wrongRecord).repairProgram=true :=rfl
example : (readRecord port wrongRecord).repairProgram≠low.goal :=by decide
example : readRecord port wrongRecord≠organization port low wrongParent.physical :=by
  intro hh
  have hp:=congrArg (fun s=>s.repairProgram) hh
  change true=false at hp
  contradiction
example (noise : PMF Bool) :
    ∀ᵐ rs ∂recordPathLaw port noise low (1/4) eps_ok (astPolicy chosen) ⟨0,wrongParent.physical,wrongParent⟩,
      ∀t : ℕ,parentView wrongParent.history (readRecord port (rs t))=(rs t).transaction.parentBefore :=
  native_parent_reconstructed port noise low (1/4) eps_ok chosen wrongParent

-- Equal organization laws intentionally forget actual paid action/cost fields.
def paidAST : Instruction 5:=.emit (some false)
theorem paid_restores : restorationCheck port low.goal paidAST=true :=by decide +kernel
theorem two_ASTs_same_lossy_organization_law (noise : PMF Bool) :
    (recordPathLaw port noise low (1/4) eps_ok (astPolicy paidAST) ⟨0,actualParent.physical,actualParent⟩).map (mapPath (readRecord port))=
      (recordPathLaw port noise low (1/4) eps_ok (astPolicy chosen) ⟨0,actualParent.physical,actualParent⟩).map (mapPath (readRecord port)) :=by
  rw [actual_record_organization_path_law port noise low (1/4) eps_ok paidAST paid_restores actualParent (postProbeParent_program _ _ _ _),
    actual_record_organization_path_law port noise low (1/4) eps_ok chosen checked_chosen actualParent (postProbeParent_program _ _ _ _)]

def reachableGoodParent : Organism 5:=(modeRecordStep port low actualParent (some false) true false).transaction.parentAfter
example : (modeRecordStep port low reachableGoodParent (interpret (compile port false) reachableGoodParent.physical) true false).transaction.expenditure=0 :=rfl
example : (modeRecordStep port low reachableGoodParent (interpret paidAST reachableGoodParent.physical) true false).transaction.expenditure=4 :=rfl
example : readRecord port (modeRecordStep port low reachableGoodParent none true false)=
    readRecord port (modeRecordStep port low reachableGoodParent (some false) true false) :=rfl

-- Same original epsilon0/1 family, no changed clock and no positive-health claim at1.
example (noise : PMF Bool) :
    (recordPathLaw port noise low 1 (by norm_num) (astPolicy chosen) ⟨0,actualParent.physical,actualParent⟩).map (mapPath (readRecord port))=
      homTrajMeasure (Measure.dirac (organization port low actualParent.physical)) (organizationKernel port low 1 (by norm_num)) :=
  actual_record_organization_path_law port noise low 1 (by norm_num) chosen checked_chosen actualParent (postProbeParent_program _ _ _ _)
example (noise : PMF Bool) :
    (recordPathLaw port noise low 0 (by norm_num) (astPolicy chosen) ⟨0,actualParent.physical,actualParent⟩).map (mapPath (readRecord port))=
      homTrajMeasure (Measure.dirac (organization port low actualParent.physical)) (organizationKernel port low 0 (by norm_num)) :=
  actual_record_organization_path_law port noise low 0 (by norm_num) chosen checked_chosen actualParent (postProbeParent_program _ _ _ _)

-- Original144-probe prefix offset, not a slowed deployment clock or new idle protocol.
theorem exact_probe_prefix_offset (rs : ℕ→ModeRecord 5) (t : ℕ) : wholeRecords port low seed (raw,rs) (144+t)=rs t :=by
  have hpre (pre : List (ModeRecord 5)) (k : ℕ) : RegisterFaultFundedProbe.prepend pre rs (pre.length+k)=rs k :=by
    induction pre with
    | nil=>simp [RegisterFaultFundedProbe.prepend]
    | cons r pre ih=>simpa only [List.length_cons,Nat.succ_add,RegisterFaultFundedProbe.prepend] using ih
  have hlen : (probeTrace port low raw seed (registration 72)).length=144 :=by
    have hh (js : List (Coordinate 72)) (o : Organism 5) : (probeTrace port low raw o js).length=js.length :=by
      induction js generalizing o with
      | nil=>rfl
      | cons j js ih=>simpa only [probeTrace,List.length_cons] using congrArg Nat.succ (ih _)
    rw [hh,registration_length]
  change RegisterFaultFundedProbe.prepend (probeTrace port low raw seed (registration 72)) rs (144+t)=_
  rw [←hlen]
  exact hpre _ t

#print axioms actual_full_organization_law
#print axioms actual_returned_q_organization_law
#print axioms all_actual_time_marginals
#print axioms actual_native_p12_alltimes
#print axioms same_joint_p5_p12_parent_resource_life
#print axioms two_ASTs_same_lossy_organization_law
#print axioms exact_probe_prefix_offset
end
end IndependentNativeOrganization
