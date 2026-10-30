import UEOT
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace IndependentDynamicResource
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.Objecthood.ResourceClosure UEOT.V3.BoundedLossSampling
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
open RegisterFaultJointRecord RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite
open RegisterFaultDynamicProbe RegisterFaultDynamicProbeInfinite RegisterFaultDynamicPrice
open RegisterInstructionPurposeScale RegisterActuatorScaleSource RegisterSemanticInstructionScale RegisterFaultDynamicProbeResource
open scoped BigOperators ENNReal
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩

def rawWord : Coordinate 80→Bool×Bool:=fun j=>if j.2.val%4=3 then (false,false) else (true,false)
def visible (k : ℕ) : Batch 80:=fun j=>(decide (j.2.val%4≠3) && j.1,if j.2.val%4=3 then 0 else k)
def low : Mechanism:=⟨true,13/5⟩
def initial : Organism 3:=⟨[true,false,false,true],fun j=>j=0,true⟩
theorem eps_ok : (1/4 : NNReal)≤1 :=by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)
theorem price_exact : priceValue (2/5) (by norm_num)=(2/5 : NNReal) :=by
  apply Subtype.ext
  norm_num [priceValue]
theorem actual_bin : feeBin (1/5) low.writeCost=13 :=by norm_num [feeBin,low]
theorem actual_data : sourceData low (1/5) rawWord=visible 13 :=by
  funext j
  rcases j with ⟨b,k⟩
  cases b <;> by_cases hk : k.val%4=3 <;>
    simp only [sourceData,feature,rawWord,hk,if_true,if_false,actual_bin] <;>
    simp [visible,low,hk]
theorem mean_true (k : ℕ) : birthMean (visible k) true=3/4 :=by
  change birthMean (visible 0) true=3/4
  decide +kernel
theorem mean_false (k : ℕ) : birthMean (visible k) false=0 :=by simp [birthMean,visible]
theorem new_choice : classify (2/5) (1/5) (3/5) (1/4) (visible 13)=.repair true :=by decide +kernel
theorem old_choice : select (2/5) (1/5) (visible 13)=.idle true :=by decide +kernel

theorem actual_good (noise : PMF Bool) : rawWord∈Good noise low (1/4) eps_ok 80 (1/5) ((1/4 : ℚ) : ℝ) :=by
  intro b
  change |empiricalRisk birthScore (sourceSample low (1/5) b) rawWord-
    trueRisk (row noise low (1/4) eps_ok (1/5) b).toMeasure birthScore|≤((1/4 : ℚ) : ℝ)
  rw [←birthMean_source,birth_mean,actual_data]
  cases b <;> norm_num [mean_false,mean_true,low,repairChance]

example : (probeTrace (2 : Fin 3) low rawWord initial (registration 80)).map (recordObservation (1/5))=
    (registration 80).map (sourceData low (1/5) rawWord) :=actual_probe_trace_observations 2 low (1/5) rawWord initial rfl _
example : postProbeParent (2 : Fin 3) low rawWord initial=
    (probeTrace 2 low rawWord initial (registration 80)).foldl (fun _ r=>r.transaction.parentAfter) initial :=
  postProbeParent_trace _ _ _ _
example : (postProbeParent (2 : Fin 3) low rawWord initial).physical 2=false :=rfl
example : (postProbeParent (2 : Fin 3) low rawWord initial).physical 0=true :=rfl
example : (postProbeParent (2 : Fin 3) low rawWord initial).program=true :=postProbeParent_program _ _ _ _

-- The entire original 2N trace remains; no idle-only funding protocol is substituted.
theorem trace_costs (js : List (Coordinate 80)) (o : Organism 3) :
    (probeTrace (2 : Fin 3) low rawWord o js).map (fun r=>r.transaction.expenditure)=
      js.map (fun j=>if j.2.val%4=3 then 0 else (13/5 : ℝ)) :=by
  induction js generalizing o with
  | nil=>rfl
  | cons j js ih=>
    simp only [probeTrace,List.map_cons,ih]
    congr 1
    by_cases hk : j.2.val%4=3 <;>
      simp [rawWord,hk,modeRecordStep,RegisterJointRecord.recordStep,cost,low]
example : ((probeTrace (2 : Fin 3) low rawWord initial (registration 80)).map (fun r=>r.transaction.expenditure)).sum=312 :=by
  rw [trace_costs]
  norm_num [registration,List.finRange]

theorem risk_nonvacuous : 4*Real.exp (-(10 : ℝ))<1 :=by
  have hp:=Real.exp_pos (10 : ℝ)
  have hl:=Real.add_one_le_exp (10 : ℝ)
  rw [Real.exp_neg,←div_eq_mul_inv]
  exact (div_lt_one hp).mpr (by linarith)

-- Known external cap4, arrival9/2 BEFORE each actual transaction, stock1/2.
-- These are explicit independent permissions, never selector inputs.
theorem common_same_source (noise : PMF Bool) :
    (∀ᵐ z ∂jointLaw (N:=80) (2 : Fin 3) noise low (1/4) eps_ok (2/5) (1/5) (3/5) (1/4) initial,
      ResourceViable (1/2) (fun _=>(9/2 : ℝ)) (fun t=>(wholeRecords 2 low initial z t).transaction.expenditure)) ∧
    (let parent:=postProbeParent (2 : Fin 3) low rawWord initial
     let p:=returnedAST 2 (classify (2/5) (1/5) (3/5) (1/4) (sourceData low (1/5) rawWord))
     let q:=returnedProgram 2 p
     actualValue 2 noise low (1/4) eps_ok (priceValue (2/5) (by norm_num)) (3/5) parent p=321/400 ∧
     actualValue (0 : Fin 1) noise low (1/4) eps_ok (priceValue (2/5) (by norm_num)) (3/5) (projectOrganism 2 parent) q=321/400) ∧
    (jointLaw (N:=80) (2 : Fin 3) noise low (1/4) eps_ok (2/5) (1/5) (3/5) (1/4) initial).real
      (Prod.fst ⁻¹' Error (N:=80) (2 : Fin 3) noise low (1/4) eps_ok (2/5) (1/5) (3/5) (1/4) (by norm_num) (by norm_num))<1 :=by
  have hh:=funded_actual_purpose_and_risk (2 : Fin 3) noise low (1/4) eps_ok 80 (by decide)
    (2/5) (1/5) (3/5) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) initial rfl
    4 (9/2) (1/2) (by norm_num [low]) (by norm_num) (by norm_num)
  have ha : classify (2/5) (1/5) (3/5) (1/4) (sourceData low (1/5) rawWord)≠.unknown :=by rw [actual_data,new_choice];decide
  have hv:=hh.2.1 rawWord (actual_good noise) ha
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hv
  have hopt : (model (2 : Fin 3) noise low (priceValue (2/5) (by norm_num)) (1/4) eps_ok (3/5) (by norm_num)).optimalValue
      (postProbeParent 2 low rawWord initial).physical=321/400 :=by
    rw [←repair_value_eq_optimal 2 noise low (priceValue (2/5) (by norm_num)) (1/4) eps_ok (3/5) (by norm_num)
      (by rw [price_exact];norm_num [RepairRegion,low,repairChance])]
    have hx : (postProbeParent (2 : Fin 3) low rawWord initial).physical 2=false:=rfl
    simp only [value,hx]
    rw [price_exact]
    norm_num [goodValue,badValue,low,repairChance]
  have hrisk : (jointLaw (N:=80) (2 : Fin 3) noise low (1/4) eps_ok (2/5) (1/5) (3/5) (1/4) initial).real
      (Prod.fst ⁻¹' Error (N:=80) (2 : Fin 3) noise low (1/4) eps_ok (2/5) (1/5) (3/5) (1/4) (by norm_num) (by norm_num))≤
      min 1 (4*Real.exp (-10)) :=by
    convert hh.2.2 using 1
    norm_num
  exact ⟨hh.1,⟨hv.2.2.1.trans hopt,hv.2.2.2.trans hopt⟩,(hrisk.trans (min_le_right _ _)).trans_lt risk_nonvacuous⟩

example (noise : PMF Bool) :
    ∀ᵐ p ∂jointLaw (N:=80) (2 : Fin 3) noise low (1/4) eps_ok (2/5) (1/5) (3/5) (1/4) initial,
      ∀t,(wholeRecords 2 low initial p t).transaction.expenditure≤balance 2 low initial (1/2) (9/2) p t+9/2 :=by
  filter_upwards [actual_joint_prepay_funded (N:=80) (2 : Fin 3) noise low (1/4) eps_ok
    (2/5) (1/5) (3/5) (1/4) initial 4 (9/2) (1/2) (by norm_num [low]) (by norm_num) (by norm_num)] with p hp
  exact hp.2
example (noise : PMF Bool) : IsProbabilityMeasure
    (fundedLaw (N:=80) (2 : Fin 3) noise low (1/4) eps_ok (2/5) (1/5) (3/5) (1/4) initial (1/2) (9/2)) :=inferInstance
example (noise : PMF Bool) :
    (fundedLaw (N:=80) (2 : Fin 3) noise low (1/4) eps_ok (2/5) (1/5) (3/5) (1/4) initial (1/2) (9/2)).map Prod.fst=
      jointLaw (N:=80) (2 : Fin 3) noise low (1/4) eps_ok (2/5) (1/5) (3/5) (1/4) initial :=fundedLaw_erasure _ _ _ _ _ _ _ _ _ _ _ _

example (rs : ℕ→ModeRecord 3) : balance (2 : Fin 3) low initial (1/2) (9/2) (rawWord,rs) 1=12/5 :=by
  have hfee : (wholeRecords (2 : Fin 3) low initial (rawWord,rs) 0).transaction.expenditure=(low.writeCost : ℝ):=rfl
  simp only [balance,cumulativeResourceBalance,Finset.sum_range_one,hfee]
  norm_num [low]
example (rs : ℕ→ModeRecord 3) : balance (2 : Fin 3) low initial (1/2) (1/2) (rawWord,rs) 1= -(8/5) :=by
  have hfee : (wholeRecords (2 : Fin 3) low initial (rawWord,rs) 0).transaction.expenditure=(low.writeCost : ℝ):=rfl
  simp only [balance,cumulativeResourceBalance,Finset.sum_range_one,hfee]
  norm_num [low]

theorem word_positive : 0<rawLaw (PMF.pure false) (1/4) eps_ok 80 {rawWord} :=by
  rw [rawLaw,VariableRegisteredSamples.productRowLaw,Measure.pi_singleton]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rcases j with ⟨b,k⟩
  by_cases hk : k.val%4=3 <;>
    norm_num [rawWord,hk,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance]

theorem low_prepay_negative_positive_mass :
    0<(jointLaw (N:=80) (2 : Fin 3) (PMF.pure false) low (1/4) eps_ok (2/5) (1/5) (3/5) (1/4) initial)
      {p | balance 2 low initial (1/2) (1/2) p 1<0} :=by
  let mu:=jointLaw (N:=80) (2 : Fin 3) (PMF.pure false) low (1/4) eps_ok (2/5) (1/5) (3/5) (1/4) initial
  have hm : mu (Prod.fst ⁻¹' {rawWord})=rawLaw (PMF.pure false) (1/4) eps_ok 80 {rawWord} :=by
    rw [←Measure.fst_apply (measurableSet_singleton _),actual_joint_training_marginal]
  have hsub : Prod.fst ⁻¹' {rawWord}⊆{p | balance (2 : Fin 3) low initial (1/2) (1/2) p 1<0} :=by
    rintro ⟨omega,rs⟩ homega
    have ho : omega=rawWord:=homega
    subst omega
    have hfee : (wholeRecords (2 : Fin 3) low initial (rawWord,rs) 0).transaction.expenditure=(low.writeCost : ℝ):=rfl
    change balance (2 : Fin 3) low initial (1/2) (1/2) (rawWord,rs) 1<0
    simp only [balance,cumulativeResourceBalance,Finset.sum_range_one,hfee]
    norm_num [low]
  have hp : 0 < mu (Prod.fst ⁻¹' {rawWord}) :=by rw [hm];exact word_positive
  exact hp.trans_le (measure_mono hsub)

#print axioms common_same_source
#print axioms low_prepay_negative_positive_mass
#print axioms funded_actual_purpose_and_risk
end
end IndependentDynamicResource
