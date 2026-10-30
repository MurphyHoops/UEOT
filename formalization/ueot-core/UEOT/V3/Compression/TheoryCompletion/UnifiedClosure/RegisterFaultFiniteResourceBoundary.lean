import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFiniteResourceWitness

/-!
Original commitment: the universal positive-fault/fee resource obstruction must state strict parameter boundaries on its actual native source.
Existing theorem: original complete-record prefix expectation, true P6 cost and all-causal occupation bound.
Premise reduced: compute excluded-boundary health marginals from actual finite source rows, rather than assert another law has the same distribution.
Model/boundary: zero fee always writes; zero fault makes one allowed first repair sufficient; original labels/failed records/retained parent remain.
Consumer: exact recordPathLaw expected-health nonsummability, not an unproved product-law equivalence or a discounted/eventual-event substitution.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFiniteResourceBoundary
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord RegisterFaultInfiniteRecord
open RegisterActuatorScaleSource RegisterFaultControlModel RegisterFaultFiniteResourceMaintenance RegisterFaultFiniteResourceWitness
open scoped NNReal ENNReal Topology
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _=>trivial⟩
set_option maxHeartbeats 1000000

private theorem sum_pmf (q : PMF Bool) : ∑ b,(q b).toReal=1 :=by
  have h:=congrArg ENNReal.toReal (PMF.tsum_coe q)
  rw [tsum_fintype,ENNReal.toReal_sum (fun b _=>PMF.apply_ne_top _ b)] at h
  simpa using h

/-- Original allowed always-write controller, with no mode/fee oracle. -/
abbrev paid (n : ℕ) (b : Bool) :=selectorPolicy (fun _ : State n=>some b)

private theorem paid_prefix_expectation {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) : ∀ N {t : ℕ} (h : State n) (o : Organism n),o.program=m.goal →
    actualExpectation i noise m epsilon he (paid n m.goal) 0 1 N (t:=t) h o=(N : ℝ)*repairChance epsilon :=by
  intro N
  induction N with
  | zero => intros; simp [actualExpectation,discountedPayoff,Tape,records]
  | succ N ih =>
    intro t h o hp
    rw [actualExpectation_succ i noise m epsilon he (paid n m.goal) 0 1 N (t:=t) h o]
    rw [Finset.sum_eq_single (some m.goal)
      (fun a _ ha=>by simp [paid,selectorPolicy_actionProb,ha]) (by simp)]
    dsimp only [paid,selectorPolicy]
    simp only [if_true,one_mul]
    have hnext (mode label : Bool) : actualExpectation i noise m epsilon he (paid n m.goal) 0 1 N (t:=t+1)
        (modeRecordStep i m o (some m.goal) mode label).transaction.parentAfter.physical
        (modeRecordStep i m o (some m.goal) mode label).transaction.parentAfter=(N : ℝ)*repairChance epsilon :=
      ih _ _ ((step_program i m o _ mode label).trans hp)
    have hpay (mode label : Bool) : RegisterJointRecord.payoff 0
        (modeRecordStep i m o (some m.goal) mode label).transaction=if mode then (1 : ℝ) else 0 :=by
      rw [step_payoff i m 0 o _ _ _ hp]
      cases mode <;> simp [modePayoff,outcome,childCount,update]
    dsimp only [paid,selectorPolicy] at hnext
    simp only [hnext,hpay]
    conv_lhs => arg 2; ext mode; arg 2; ext label; rw [mul_assoc,mul_comm ((noise label).toReal),←mul_assoc]
    simp_rw [←Finset.mul_sum,sum_pmf,mul_one]
    simp [modeLaw,modeProbability,FiniteProbabilityRow.ofRealRow_apply_toReal]
    unfold repairChance
    ring

private theorem expected_prefix_sum {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action))
    {t : ℕ} (h : pi.Memory t) (o : Organism n) (hp : o.program=m.goal) (N : ℕ) :
    (∑ k∈Finset.range N,∫ rs,recordHealth i (rs k) ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩)=
      actualExpectation i noise m epsilon he pi 0 1 N h o :=by
  rw [←actual_prefix_health_expectation i noise m epsilon he pi h o hp N]
  symm
  apply integral_finsetSum
  intro k _
  exact Integrable.of_bound ((recordHealth_measurable i).comp (measurable_pi_apply k)).aestronglyMeasurable 1
    (ae_of_all _ (fun _=>recordHealth_norm_le i _))

/-- SAME native source: always writing the goal has maintained marginal
1-epsilon at EVERY post-transaction clock. No invariant/frequency law is an input. -/
theorem paid_actual_health_mean {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) {t : ℕ} (h : State n) (o : Organism n)
    (hp : o.program=m.goal) (k : ℕ) :
    (∫ rs,recordHealth i (rs k) ∂recordPathLaw i noise m epsilon he (paid n m.goal) ⟨t,h,o⟩)=repairChance epsilon :=by
  have hN (N : ℕ) := (expected_prefix_sum i noise m epsilon he (paid n m.goal) (t:=t) h o hp N).trans
    (paid_prefix_expectation i noise m epsilon he N (t:=t) h o hp)
  have hs:=hN (k+1)
  rw [Finset.sum_range_succ,hN k,Nat.cast_add,Nat.cast_one] at hs
  nlinarith

/-- With literally zero write fee, every original policy's original complete
record law is P6 feasible from zero reserve and zero income. -/
theorem zero_fee_actual_funded {n : ℕ} (i : Fin n) (noise : PMF Bool) (b : Bool)
    (epsilon : NNReal) (he : epsilon ≤ 1) (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) (c : Config pi) :
    ∀ᵐ rs ∂recordPathLaw i noise ⟨b,0⟩ epsilon he pi c,
      ResourceViable 0 (fun _=>0) (fun k=>(rs k).transaction.expenditure) :=by
  rw [recordPathLaw]
  apply (ae_map_iff (measurable_recordStream i ⟨b,0⟩ pi c).aemeasurable
    (measurable_zero_income_viability 0)).mpr
  exact ae_of_all _ (fun z=>actual_infinite_resource_viable i ⟨b,0⟩ pi c z 0 0 (by norm_num) (by norm_num))

/-- Strict native zero-fee counterexample: actual zero-stock viability and
positive fault epsilon<1 coexist with NONsummable expected actual health.
This refutes dropping the positive-fee premise; it asserts no law equality. -/
theorem native_zero_fee_boundary {n : ℕ} (i : Fin n) (noise : PMF Bool) (b : Bool)
    (epsilon : NNReal) (he : epsilon<1) {t : ℕ} (h : State n) (o : Organism n) (hp : o.program=b) :
    (∀ᵐ rs ∂recordPathLaw i noise ⟨b,0⟩ epsilon he.le (paid n b) ⟨t,h,o⟩,
      ResourceViable 0 (fun _=>0) (fun k=>(rs k).transaction.expenditure)) ∧
    ¬Summable (fun k=>∫ rs,recordHealth i (rs k) ∂recordPathLaw i noise ⟨b,0⟩ epsilon he.le (paid n b) ⟨t,h,o⟩) :=by
  refine ⟨zero_fee_actual_funded i noise b epsilon he.le _ _,?_⟩
  intro hs
  have ht:=hs.tendsto_atTop_zero
  have heq (k : ℕ) :=paid_actual_health_mean i noise ⟨b,0⟩ epsilon he.le (t:=t) h o hp k
  simp only [heq] at ht
  have hz : repairChance epsilon=0 :=tendsto_nhds_unique tendsto_const_nhds ht
  have heR : (epsilon : ℝ)<1 :=by exact_mod_cast he
  unfold repairChance at hz
  linarith

private theorem oneAttempt_no_fault_expectation {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) :
    ∀ N {t : ℕ} (h : State n) (o : Organism n),o.program=m.goal → (t=0 ∨ o.physical i=m.goal) →
      actualExpectation i noise m 0 (by norm_num) (oneAttempt n m.goal) 0 1 N (t:=t) h o=(N : ℝ) :=by
  intro N
  induction N with
  | zero => intros; simp [actualExpectation,discountedPayoff,Tape,records]
  | succ N ih =>
    intro t h o hp hx
    rw [actualExpectation_succ i noise m 0 (by norm_num) (oneAttempt n m.goal) 0 1 N (t:=t) h o]
    let a : Action:=if t=0 then some m.goal else none
    rw [Finset.sum_eq_single a (fun aa _ ha=>by simp [oneAttempt,show aa≠(if t=0 then some m.goal else none) from ha]) (by simp)]
    dsimp only [oneAttempt]
    simp only [show a=(if t=0 then some m.goal else none) from rfl,if_true,one_mul]
    have hg : (modeRecordStep i m o a true false).transaction.parentAfter.physical i=m.goal :=by
      rcases hx with ht|hx
      · simp [a,ht,modeRecordStep,RegisterJointRecord.recordStep,update]
      · by_cases ht : t=0 <;> simp [a,ht,modeRecordStep,RegisterJointRecord.recordStep,update,hx]
    have hgood (label : Bool) : (modeRecordStep i m o a true label).transaction.parentAfter.physical i=m.goal :=by
      simpa only [step_physical] using hg
    have hnext (label : Bool) : actualExpectation i noise m 0 (by norm_num) (oneAttempt n m.goal) 0 1 N (t:=t+1)
        (modeRecordStep i m o a true label).transaction.parentAfter.physical
        (modeRecordStep i m o a true label).transaction.parentAfter=(N : ℝ) :=
      ih _ _ ((step_program i m o a true label).trans hp) (Or.inr (hgood label))
    have hpay (label : Bool) : RegisterJointRecord.payoff 0 (modeRecordStep i m o a true label).transaction=1 :=by
      rw [step_payoff i m 0 o _ _ _ hp]
      have ha : update i o.physical a i=m.goal :=by simpa only [step_physical,modeNext,if_true] using hgood label
      simp [modePayoff,outcome,ha,childCount]
    dsimp only [oneAttempt,a] at hnext hpay
    simp only [step_physical] at hnext
    simp [modeLaw,modeProbability,FiniteProbabilityRow.ofRealRow_apply_toReal,repairChance]
    simp only [hnext,hpay]
    have hn:=sum_pmf noise
    simp only [Fintype.sum_bool] at hn
    nlinarith


/-- Strict native zero-fault boundary, even at POSITIVE write cost: one
actually funded repair attempt gives every post-health mean exactly one. -/
theorem native_zero_fault_boundary {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (o : Organism n) (hp : o.program=m.goal) :
    (∀ᵐ rs ∂recordPathLaw i noise m 0 (by norm_num) (oneAttempt n m.goal) ⟨0,o.physical,o⟩,
      ResourceViable m.writeCost (fun _=>0) (fun k=>(rs k).transaction.expenditure)) ∧
    (∀ k,(∫ rs,recordHealth i (rs k) ∂recordPathLaw i noise m 0 (by norm_num) (oneAttempt n m.goal) ⟨0,o.physical,o⟩)=1) ∧
    ¬Summable (fun k=>∫ rs,recordHealth i (rs k) ∂recordPathLaw i noise m 0 (by norm_num) (oneAttempt n m.goal) ⟨0,o.physical,o⟩) :=by
  have hN (N : ℕ) := (expected_prefix_sum i noise m 0 (by norm_num) (oneAttempt n m.goal) (t:=0) o.physical o hp N).trans
    (oneAttempt_no_fault_expectation i noise m N (t:=0) o.physical o hp (Or.inl rfl))
  have hm (k : ℕ) : (∫ rs,recordHealth i (rs k) ∂recordPathLaw i noise m 0 (by norm_num) (oneAttempt n m.goal) ⟨0,o.physical,o⟩)=1 :=by
    have hh:=hN (k+1)
    rw [Finset.sum_range_succ,hN k,Nat.cast_add,Nat.cast_one] at hh
    linarith
  refine ⟨oneAttempt_actual_funded i noise m 0 (by norm_num) o,hm,?_⟩
  intro hs
  have ht:=hs.tendsto_atTop_zero
  simp only [hm] at ht
  have hz : (1 : ℝ)=0 :=tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at hz

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFiniteResourceBoundary
