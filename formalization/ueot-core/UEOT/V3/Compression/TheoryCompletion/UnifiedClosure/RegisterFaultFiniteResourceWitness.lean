import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFiniteResourceMaintenance

/-!
Original commitment: universal closed-stock obstruction must have an actual affordable policy and strict excluded-boundary witnesses.
Existing theorem: SAME complete-record source, every fine causal policy satisfying actual P6 budget, positive fault/fee implies finite occupation and eventual loss.
Premise reduced: derive affordability of a clock-visible single repair attempt, rather than assuming its budget certificate.
Model/boundary: original allowed write once then idle, all failed transactions retained; zero fault and zero fee are separate source cases.
Consumer: native ResourceViable and actual retained-parent health; no income port, reset, observation or success filtering is introduced.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFiniteResourceWitness
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord RegisterFaultInfiniteRecord
open RegisterActuatorScaleSource RegisterFaultFiniteResourceMaintenance
open scoped NNReal ENNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
local instance (k : ℕ) : MeasurableSpace (Tape k) := ⊤
local instance (k : ℕ) : MeasurableSingletonClass (Tape k) := ⟨fun _=>trivial⟩
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _=>trivial⟩
local instance {n : ℕ} : MeasurableSpace (List (ModeRecord n)) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (List (ModeRecord n)) := ⟨fun _=>trivial⟩

/-- One original allowed goal write at clock zero, then original idle forever.
The rule reads no execution mode, fee, label or future event. -/
def oneAttempt (n : ℕ) (goal : Bool) : CausalPolicy.{0,0,0} (State n) (fun _=>Action) where
  Memory:=fun _=>State n
  current:=fun x=>x
  advance:=fun _ _ y=>y
  current_advance:=by intros; rfl
  actionProb:=fun {t} _ a=>if a=(if t=0 then some goal else none) then 1 else 0
  actionProb_nonneg:=by intros; split_ifs <;> norm_num
  actionProb_sum_one:=by intros; simp

/-- Sum of the actual fees in every retained transaction, including faults. -/
def listCost {n : ℕ} (rs : List (ModeRecord n)) : ℝ :=(rs.map (fun r=>r.transaction.expenditure)).sum

private theorem step_cost_le {n : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n) (a : Action) (mode label : Bool) :
    (modeRecordStep i m o a mode label).transaction.expenditure ≤ (m.writeCost : ℝ) :=by
  cases mode <;> cases a <;> simp [modeRecordStep,RegisterJointRecord.recordStep,cost,m.writeCost.coe_nonneg]

private theorem supported_cost {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) : ∀ k {t : ℕ} (h : State n) (o : Organism n) (w : Tape k),
    0 < weight i noise m epsilon he (oneAttempt n m.goal) k (t:=t) h o w →
      listCost (records i m (oneAttempt n m.goal) k (t:=t) h o w) ≤ if t=0 then (m.writeCost : ℝ) else 0 :=by
  intro k
  induction k with
  | zero => intros; simp only [records,listCost,List.map_nil,List.sum_nil]; split_ifs <;> positivity
  | succ k ih =>
    rintro t h o ⟨a,mode,label,rest⟩ hw
    have ha : a=(if t=0 then some m.goal else none) :=by
      by_contra hn
      simp only [weight,oneAttempt,if_neg hn,zero_mul] at hw
      exact (lt_irrefl 0) hw
    have hr : 0 < weight i noise m epsilon he (oneAttempt n m.goal) k (t:=t+1)
        (modeRecordStep i m o a mode label).transaction.parentAfter.physical
        (modeRecordStep i m o a mode label).transaction.parentAfter rest :=by
      simp only [weight] at hw
      exact pos_of_mul_pos_right hw (mul_nonneg (mul_nonneg (CausalPolicy.actionProb_nonneg _ _ _) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
    have hb:=ih _ _ _ hr
    simp only [show t+1≠0 by omega,if_false] at hb
    change (modeRecordStep i m o a mode label).transaction.expenditure+
      listCost (records i m (oneAttempt n m.goal) k
        (modeRecordStep i m o a mode label).transaction.parentAfter.physical
        (modeRecordStep i m o a mode label).transaction.parentAfter rest) ≤ _
    by_cases ht : t=0
    · simp only [ht,if_true]
      linarith [step_cost_le i m o a mode label]
    · simp only [ht,if_false] at ha ⊢
      subst a
      have hz : (modeRecordStep i m o none mode label).transaction.expenditure=0 :=by
        cases mode <;> rfl
      simpa only [hz,zero_add] using hb

private theorem oneAttempt_finite_cost {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism n) (k : ℕ) :
    ∀ᵐ rs ∂(recordLaw i noise m epsilon he (oneAttempt n m.goal) k (t:=0) o.physical o).toMeasure,
      listCost rs ≤ (m.writeCost : ℝ) :=by
  let q:=tapeLaw i noise m epsilon he (oneAttempt n m.goal) k (t:=0) o.physical o
  have hsupp : ∀ᵐ w ∂q.toMeasure,q w≠0 :=by
    rw [ae_iff,PMF.toMeasure_apply_eq_zero_iff _ (by trivial)]
    exact Set.disjoint_left.mpr (fun w hw hn=>hn hw)
  let f:=records i m (oneAttempt n m.goal) k (t:=0) o.physical o
  change ∀ᵐ rs ∂(q.map f).toMeasure,listCost rs ≤ (m.writeCost : ℝ)
  rw [←PMF.toMeasure_map _ _ (measurable_of_finite f)]
  apply (ae_map_iff (measurable_of_finite f).aemeasurable (by trivial)).mpr
  filter_upwards [hsupp] with w hw
  have hwpos:=ENNReal.toReal_pos hw (PMF.apply_ne_top _ _)
  change 0 < (tapeLaw i noise m epsilon he (oneAttempt n m.goal) k (t:=0) o.physical o w).toReal at hwpos
  simp only [tapeLaw,FiniteProbabilityRow.ofRealRow_apply_toReal] at hwpos
  simpa only [if_true] using supported_cost i noise m epsilon he k (t:=0) o.physical o w hwpos

private theorem listCost_ofFn {n : ℕ} (rs : ℕ→ModeRecord n) (k : ℕ) :
    listCost (List.ofFn (fun j : Fin k=>rs j))=prefixCost k rs :=by
  simp only [listCost,prefixCost,List.map_ofFn,List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun j=>(rs j).transaction.expenditure) k

theorem measurable_zero_income_viability {n : ℕ} (R : ℝ) :
    MeasurableSet {rs : ℕ→ModeRecord n | ResourceViable R (fun _=>0) (fun k=>(rs k).transaction.expenditure)} :=by
  have heq : {rs : ℕ→ModeRecord n | ResourceViable R (fun _=>0) (fun k=>(rs k).transaction.expenditure)} =
      ⋂ k : ℕ,{rs : ℕ→ModeRecord n | 0 ≤ cumulativeResourceBalance R (fun _=>0) (fun k=>(rs k).transaction.expenditure) k} := by
    ext rs
    simp [ResourceViable]
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  apply measurableSet_le measurable_const
  unfold cumulativeResourceBalance
  apply Measurable.sub (measurable_const.add measurable_const)
  apply Finset.measurable_sum
  intro j _
  exact (show Measurable (fun r : ModeRecord n=>r.transaction.expenditure) from fun _ _=>trivial).comp (measurable_pi_apply j)

/-- Literal first attempt costs at most the single actual initial reserve;
no later income, reset, or free extra repair is assumed. -/
theorem oneAttempt_actual_funded {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism n) :
    ∀ᵐ rs ∂recordPathLaw i noise m epsilon he (oneAttempt n m.goal) ⟨0,o.physical,o⟩,
      ResourceViable m.writeCost (fun _=>0) (fun k=>(rs k).transaction.expenditure) :=by
  let pi:=oneAttempt n m.goal
  let c : Config pi:=⟨0,o.physical,o⟩
  have hf (k : ℕ) : ∀ᵐ z ∂wordPathLaw i noise m epsilon he pi c,listCost (trace i m pi c (z k)) ≤ (m.writeCost : ℝ) :=by
    have hh:=oneAttempt_finite_cost i noise m epsilon he o k
    rw [←actual_record_prefix_law i noise m epsilon he pi o.physical o k] at hh
    exact ae_of_ae_map ((measurable_of_countable _).comp (measurable_pi_apply k)).aemeasurable hh
  change ∀ᵐ rs ∂(wordPathLaw i noise m epsilon he pi c).map (fun z k=>recordAt i m pi c z k),_
  apply (ae_map_iff (measurable_recordStream i m pi c).aemeasurable (measurable_zero_income_viability _)).mpr
  filter_upwards [ae_all_iff.mpr hf,wordPathLaw_ae_coherent i noise m epsilon he pi c] with z hz hc
  apply (resourceViable_iff_cumulative_cost_le _ _ _).mpr
  intro k
  have hh:=hz k
  rw [coherent_trace_eq_stream i m pi c z hc.1 hc.2 k,listCost_ofFn] at hh
  simpa only [prefixCost,Finset.sum_const_zero,add_zero] using hh

/-- Actual policy consumer of the universal obstruction, with its funding
premise derived from the actual complete records. -/
theorem oneAttempt_eventual_loss {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (hepos : 0 < epsilon) (hcpos : 0 < m.writeCost)
    (o : Organism n) (hp : o.program=m.goal) :
    ∀ᵐ rs ∂recordPathLaw i noise m epsilon he (oneAttempt n m.goal) ⟨0,o.physical,o⟩,
      ∃ N,∀ k≥N,¬Legitimate i (rs k).transaction.parentAfter :=
  actual_eventually_never_legitimate i noise m epsilon he hepos hcpos (oneAttempt n m.goal) (t:=0) o.physical o rfl hp m.writeCost
    (oneAttempt_actual_funded i noise m epsilon he o)


end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFiniteResourceWitness
