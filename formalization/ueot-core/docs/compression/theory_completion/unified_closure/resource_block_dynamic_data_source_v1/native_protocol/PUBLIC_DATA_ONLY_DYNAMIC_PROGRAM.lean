import UEOT
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.FiniteDiscountedControl UEOT.V3.BoundedLossSampling
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
open RegisterFaultJointRecord RegisterFaultInfiniteRecord RegisterFaultFinitePurposeProbe
open RegisterFaultFinitePurposeInfinite RegisterFaultDynamicProbe RegisterFaultDynamicProbeInfinite
open RegisterFaultDynamicPrice RegisterSemanticInstructionScale RegisterInstructionPurposeScale
open scoped ENNReal NNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def mode (k : Fin 96) : Bool:=decide (k.val%4≠0)
def label (k : Fin 96) : Bool:=decide (k.val%3=0)
def omega : Coordinate 96→Bool×Bool:=fun j=>(mode j.2,label j.2)
def observed (bin : ℕ) : Batch 96:=fun j=>(mode j.2 && j.1,if mode j.2 then bin else 0)
example : classify (1/3) (1/20) (2/3) (1/8) (observed 72)=.repair true :=by decide +kernel
example : classify (1/3) (1/20) (2/3) (1/8) (observed 240)=.idle true :=by decide +kernel
example : select (1/3) (1/20) (observed 72)=.idle true :=by decide +kernel
example (bin : ℕ) : birthMean (observed bin) true=3/4 :=by
  change birthMean (observed 0) true=3/4
  decide +kernel
example (bin : ℕ) : birthMean (observed bin) false=0 :=by simp [birthMean,observed]
#eval classify (1/3) (1/20) (2/3) (1/8) (observed 72)
#eval classify (1/3) (1/20) (2/3) (1/8) (observed 240)
#eval select (1/3) (1/20) (observed 72)

noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩
def low : Mechanism:=⟨true,18/5⟩
def high : Mechanism:=⟨true,12⟩
def seed : Organism 3:=⟨[false,true,false],fun _=>false,true⟩
def i : Fin 3:=1
def eps : NNReal:=1/4
theorem he : eps≤1 :=by change (1/4 : ℝ)≤1; norm_num
-- Both labels of the separately frozen raw word are supported by this source.
def noise : PMF Bool:=PMF.uniformOfFintype Bool

theorem low_bin : feeBin (1/20) low.writeCost=72 :=by norm_num [feeBin,low]
theorem high_bin : feeBin (1/20) high.writeCost=240 :=by norm_num [feeBin,high]
theorem data_low : sourceData low (1/20) omega=observed 72 :=by
  funext j
  rcases j with ⟨b,k⟩
  cases b <;> simp only [sourceData,feature,omega,low_bin] <;> simp [observed,show low.goal=true from rfl]
theorem data_high : sourceData high (1/20) omega=observed 240 :=by
  funext j
  rcases j with ⟨b,k⟩
  cases b <;> simp only [sourceData,feature,omega,high_bin] <;> simp [observed,show high.goal=true from rfl]

theorem row_mean (bin : ℕ) (b : Bool) : birthMean (observed bin) b=if b then (3/4 : ℚ) else 0 :=by
  cases b
  · simp [birthMean,observed]
  · change birthMean (observed 0) true=3/4
    decide +kernel

theorem good_low : omega∈Good noise low eps he 96 (1/20) ((1/8 : ℚ) : ℝ) :=by
  intro b
  change |empiricalRisk birthScore (sourceSample low (1/20) b) omega-
    trueRisk (row noise low eps he (1/20) b).toMeasure birthScore|≤((1/8 : ℚ) : ℝ)
  rw [←birthMean_source,birth_mean,data_low,row_mean]
  cases b <;> norm_num [low,eps,repairChance]
theorem good_high : omega∈Good noise high eps he 96 (1/20) ((1/8 : ℚ) : ℝ) :=by
  intro b
  change |empiricalRisk birthScore (sourceSample high (1/20) b) omega-
    trueRisk (row noise high eps he (1/20) b).toMeasure birthScore|≤((1/8 : ℚ) : ℝ)
  rw [←birthMean_source,birth_mean,data_high,row_mean]
  cases b <;> norm_num [high,eps,repairChance]

theorem select_low : classify (1/3) (1/20) (2/3) (1/8) (sourceData low (1/20) omega)=.repair true :=by
  rw [data_low]
  decide +kernel
theorem select_high : classify (1/3) (1/20) (2/3) (1/8) (sourceData high (1/20) omega)=.idle true :=by
  rw [data_high]
  decide +kernel

/-- The final probe really repairs, so this changed complete word leaves a
GOOD actual terminal parent; it is not the original fixture's damaged seed. -/
theorem actual_post_good (m : Mechanism) : (postProbeParent i m omega seed).physical i=true :=by rfl

example : (postProbeParent i low omega seed).program=seed.program :=postProbeParent_program i low omega seed
example : (probeTrace i low omega seed (registration 96)).map (recordObservation (1/20))=
    (registration 96).map (observed 72) :=by
  rw [actual_probe_trace_observations i low (1/20) omega seed rfl,data_low]

example := actual_good_returned_program i noise low eps he (1/3) (1/20) (2/3) (1/8)
  (by norm_num) (by norm_num) (by norm_num) omega seed rfl good_low (by rw [select_low];decide)
example := actual_good_returned_program i noise high eps he (1/3) (1/20) (2/3) (1/8)
  (by norm_num) (by norm_num) (by norm_num) omega seed rfl good_high (by rw [select_high];decide)
example (k : ℕ) := actual_deployment_prefix i noise low eps he (1/3) (1/20) (2/3) (1/8) seed omega k
example := actual_joint_training_marginal (N:=96) i noise low eps he (1/3) (1/20) (2/3) (1/8) seed
example := actual_joint_accepted_wrong_bound i noise low eps he 96 (by norm_num) (1/3) (1/20) (2/3) (1/8)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num) seed
theorem third_price : priceValue (1/3) (by norm_num)=(1/3 : NNReal) :=by
  apply Subtype.ext
  norm_num [priceValue]

theorem low_value :
    let parent:=postProbeParent i low omega seed
    let p:=returnedAST i (classify (1/3) (1/20) (2/3) (1/8) (sourceData low (1/20) omega))
    let q:=returnedProgram i p
    actualValue i noise low eps he (priceValue (1/3) (by norm_num)) (2/3) parent p=9/5 ∧
      actualValue (0 : Fin 1) noise low eps he (priceValue (1/3) (by norm_num)) (2/3)
        (RegisterActuatorScaleSource.projectOrganism i parent) q=9/5 :=by
  have hh:=actual_good_returned_program i noise low eps he (1/3) (1/20) (2/3) (1/8)
    (by norm_num) (by norm_num) (by norm_num) omega seed rfl good_low (by rw [select_low];decide)
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hh
  have hv : (model i noise low (priceValue (1/3) (by norm_num)) eps he (2/3) (by norm_num)).optimalValue
      (postProbeParent i low omega seed).physical=9/5 :=by
    rw [←repair_value_eq_optimal i noise low (priceValue (1/3) (by norm_num)) eps he (2/3) (by norm_num)
      (by rw [third_price];norm_num [RepairRegion,low,eps,repairChance])]
    simp only [value,actual_post_good,show low.goal=true from rfl]
    rw [third_price]
    norm_num [goodValue,low,eps,repairChance]
  exact ⟨hh.2.2.2.2.1.trans hv,hh.2.2.2.2.2.trans hv⟩

theorem high_value :
    let parent:=postProbeParent i high omega seed
    let p:=returnedAST i (classify (1/3) (1/20) (2/3) (1/8) (sourceData high (1/20) omega))
    let q:=returnedProgram i p
    actualValue i noise high eps he (priceValue (1/3) (by norm_num)) (2/3) parent p=3/2 ∧
      actualValue (0 : Fin 1) noise high eps he (priceValue (1/3) (by norm_num)) (2/3)
        (RegisterActuatorScaleSource.projectOrganism i parent) q=3/2 :=by
  have hh:=actual_good_returned_program i noise high eps he (1/3) (1/20) (2/3) (1/8)
    (by norm_num) (by norm_num) (by norm_num) omega seed rfl good_high (by rw [select_high];decide)
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hh
  have hv : (model i noise high (priceValue (1/3) (by norm_num)) eps he (2/3) (by norm_num)).optimalValue
      (postProbeParent i high omega seed).physical=3/2 :=by
    rw [←idle_value_eq_optimal i noise high (priceValue (1/3) (by norm_num)) eps he (2/3) (by norm_num)
      (by rw [third_price];norm_num [high,eps,repairChance])]
    simp only [idleValue,actual_post_good,show high.goal=true from rfl]
    norm_num [idleGoodValue,eps,repairChance]
  exact ⟨hh.2.2.2.2.1.trans hv,hh.2.2.2.2.2.trans hv⟩

theorem separated_low : DynamicallySeparated low eps (1/3) (1/20) (2/3) (1/8) :=by
  unfold DynamicallySeparated
  rw [low_bin]
  left
  norm_num [eps,repairChance]
theorem separated_high : DynamicallySeparated high eps (1/3) (1/20) (2/3) (1/8) :=by
  unfold DynamicallySeparated
  rw [high_bin]
  right
  norm_num [eps,repairChance]
example :=actual_joint_undecided_or_wrong_bound i noise low eps he 96 (by norm_num) (1/3) (1/20) (2/3) (1/8)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num) seed separated_low (by norm_num [eps,repairChance])
example :=actual_joint_undecided_or_wrong_bound i noise high eps he 96 (by norm_num) (1/3) (1/20) (2/3) (1/8)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num) seed separated_high (by norm_num [eps,repairChance])
theorem budget_nonvacuous : 4*Real.exp (-(3 : ℝ))<1 :=by
  rw [Real.exp_neg,←div_eq_mul_inv]
  exact (div_lt_one (Real.exp_pos _)).mpr (by linarith [Real.add_one_lt_exp (show (3 : ℝ)≠0 by norm_num)])

-- Original c3 uncertainty remains: no threshold/budget changed to make it accept.
def legacyVisible (bin : ℕ) : Batch 64:=fun j=>(decide (j.2.val<48) && j.1,if j.2.val<48 then bin else 0)
example : classify (1/2) (1/4) (1/2) (1/4) (legacyVisible 12)=.unknown :=by decide +kernel
example : classify (1/2) (1/100) (1/2) (1/4) (legacyVisible 300)=.unknown :=by decide +kernel

-- The new complete formal source word has strictly positive original probability.
theorem actual_word_positive : 0<rawLaw noise eps he 96 {omega} :=by
  rw [rawLaw,VariableRegisteredSamples.productRowLaw,Measure.pi_singleton]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rcases j with ⟨b,k⟩
  cases hm : mode k <;> cases hl : label k <;>
    norm_num [omega,hm,hl,noise,eps,primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance]

#print axioms data_low
#print axioms good_low
#print axioms actual_post_good
#print axioms low_value
#print axioms high_value
#print axioms actual_word_positive

end
