import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeInfinite
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFundedProbe

/-!
Original promise: the same actual learning/returned-program chain must pay its preserved training and ongoing execution fees.
Existing source: original constant-per-transaction replenishment/P6 theorem covers any allowed action/mode; the old idle-before-write protocol has a DIFFERENT 4N+1 path and cannot replace the present 2N trace/postProbeParent.
Reduced premise: derive cost bounds on the literal unchanged probe+native infinite records, then all-prefix balance and PREPAY affordability from a registered cap c<=C, external arrival g>=C, and R0>=0; no ResourceViable field is supplied.
Model/boundary: the ALREADY declared constant-per-real-transaction external source, with g arriving BEFORE each fee, is used; it is DIFFERENT from the idle-only feedback channel, creates no internal energy, and changes no action/observation/state/probe/selector.
Consumer: native P6 on the SAME DynamicProbe jointLaw, actual returned-p/q GOD/P9 and infinite values, unchanged single calibration risk; zero-income positive-fault/cost compiled no-AE boundary is reused with its original policy scope.

Every tick here is a real retained-parent transaction, including fault/failed
births; credits are not issued to an absent population slot. Arrival before fee
is part of this explicit open-environment permission. R0=0 is allowed because
that FIRST arrival is available to pay the FIRST actual write. Arrival after
payment would require a different initial-stock contract. The registered cap
and port are independent resource permissions, not estimates read by classify.
Only the old abstract write tariff is accounted for, without a thermodynamic
interpretation, extra unregistered construction cost, or a training-net-value
optimality claim. The complete native path and its data law remain unchanged.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeResource
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
open RegisterFaultJointRecord RegisterFaultInfiniteRecord RegisterFaultFinitePurposeProbe
open RegisterFaultFinitePurposeInfinite RegisterFaultDynamicProbe RegisterFaultDynamicProbeInfinite
open RegisterSemanticInstructionScale RegisterInstructionPurposeScale RegisterActuatorScaleSource
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩

/-- Reuse the actual old prepend, without padding, inserting idle or replacing
any training/post-probe state. Deployment is already seeded by postProbeParent. -/
def wholeRecords {n N : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n)
    (p : (Coordinate N→Bool×Bool)×(ℕ→ModeRecord n)) : ℕ→ModeRecord n :=
  RegisterFaultFundedProbe.prepend (probeTrace i m p.1 o (registration N)) p.2

@[fun_prop] theorem measurable_wholeRecords {n N : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n) :
    Measurable (wholeRecords (N:=N) i m o) :=
  by
    apply measurable_from_prod_countable_right
    intro omega
    change Measurable (RegisterFaultFundedProbe.prepend (probeTrace i m omega o (registration N)))
    exact RegisterFaultFundedProbe.measurable_prepend _

private theorem literal_cost_bounds {n : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n)
    (a : Action) (mode label : Bool) :
    0 ≤ (modeRecordStep i m o a mode label).transaction.expenditure ∧
      (modeRecordStep i m o a mode label).transaction.expenditure ≤ m.writeCost := by
  cases mode <;> cases a <;>
    simp [modeRecordStep,RegisterJointRecord.recordStep,cost,m.writeCost.coe_nonneg]

private theorem training_cost_bounds {n N : ℕ} (i : Fin n) (m : Mechanism)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (js : List (Coordinate N))
    (r : ModeRecord n) (hr : r∈probeTrace i m omega o js) :
    0 ≤ r.transaction.expenditure ∧ r.transaction.expenditure ≤ m.writeCost := by
  induction js generalizing o with
  | nil=>simp [probeTrace] at hr
  | cons j js ih=>
    simp only [probeTrace,List.mem_cons] at hr
    rcases hr with he | hr
    · subst r;exact literal_cost_bounds i m o _ _ _
    · exact ih _ hr

private def CostBound {n : ℕ} (C : ℝ) : Set (ℕ→ModeRecord n) :=
  {rs | ∀t,0 ≤ (rs t).transaction.expenditure ∧ (rs t).transaction.expenditure ≤ C}

private theorem measurable_costBound {n : ℕ} (C : ℝ) : MeasurableSet (CostBound (n:=n) C) := by
  have hexp (t : ℕ) : Measurable (fun rs : ℕ→ModeRecord n=>(rs t).transaction.expenditure) :=
    (show Measurable (fun r : ModeRecord n=>r.transaction.expenditure) from fun _ _=>trivial).comp (measurable_pi_apply t)
  have heq : CostBound (n:=n) C=⋂t : ℕ,{rs | 0 ≤ (rs t).transaction.expenditure ∧ (rs t).transaction.expenditure ≤ C}:=by ext rs;simp [CostBound]
  rw [heq]
  exact MeasurableSet.iInter fun t=>(measurableSet_le measurable_const (hexp t)).inter (measurableSet_le (hexp t) measurable_const)

/-- Original native path construction alone supplies the actual future fee
bounds, for any represented causal policy; no desired cost-field assumption. -/
private theorem future_cost_bounds {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) (c : Config pi) :
    ∀ᵐ rs ∂recordPathLaw i noise m epsilon he pi c,rs∈CostBound (m.writeCost : ℝ) := by
  change ∀ᵐ rs ∂(wordPathLaw i noise m epsilon he pi c).map (fun z k=>recordAt i m pi c z k),_
  apply (ae_map_iff (measurable_recordStream i m pi c).aemeasurable (measurable_costBound _)).mpr
  exact ae_of_all _ fun z t=>literal_cost_bounds i m _ _ _ _

private theorem prepend_cost_bounds {n : ℕ} (C : ℝ) (pre : List (ModeRecord n)) (rs : ℕ→ModeRecord n)
    (hp : ∀r∈pre,0 ≤ r.transaction.expenditure ∧ r.transaction.expenditure ≤ C) (hf : rs∈CostBound C) :
    RegisterFaultFundedProbe.prepend pre rs∈CostBound C := by
  induction pre with
  | nil=>exact hf
  | cons r pre ih=>
    intro t
    cases t with
    | zero=>exact hp r (by simp)
    | succ t=>exact ih (fun r hr=>hp r (by simp [hr])) t

/-- All genuine training+deployment costs satisfy the SAME tariff, on the
original joint law, including UNKNOWN and mistaken classifier outputs. -/
theorem actual_whole_cost_bounds {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price width d u : ℚ) (o : Organism n) :
    ∀ᵐ p ∂jointLaw (N:=N) i noise m epsilon he price width d u o,
      ∀t,0 ≤ (wholeRecords i m o p t).transaction.expenditure ∧
        (wholeRecords i m o p t).transaction.expenditure ≤ m.writeCost := by
  apply Measure.ae_compProd_of_ae_ae ((measurable_costBound _).preimage (measurable_wholeRecords i m o))
  apply ae_of_all
  intro omega
  have hf:=future_cost_bounds i noise m epsilon he
    (astPolicy (returnedAST i (classify price width d u (sourceData m width omega))))
    ⟨0,(postProbeParent i m omega o).physical,postProbeParent i m omega o⟩
  filter_upwards [hf] with rs hrs
  exact prepend_cost_bounds _ _ _ (fun r hr=>training_cost_bounds i m omega o _ r hr) hrs

/-- One continuous cash coordinate of the unchanged full transaction path. -/
def balance {n N : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n) (initial g : ℝ)
    (p : (Coordinate N→Bool×Bool)×(ℕ→ModeRecord n)) (t : ℕ) : ℝ :=
  cumulativeResourceBalance initial (fun _=>g) (fun k=>(wholeRecords i m o p k).transaction.expenditure) t

/-- The actual continuous account credits this tick BEFORE subtracting its
literal fee; the formula includes the training/deployment boundary unchanged. -/
theorem actual_balance_step {n N : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n)
    (initial g : ℝ) (p : (Coordinate N→Bool×Bool)×(ℕ→ModeRecord n)) (t : ℕ) :
    balance i m o initial g p (t+1)=balance i m o initial g p t+g-
      (wholeRecords i m o p t).transaction.expenditure := by
  simp only [balance,cumulativeResourceBalance,Finset.sum_range_succ]
  ring

@[fun_prop] theorem measurable_balance {n N : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n) (initial g : ℝ) :
    Measurable (balance (N:=N) i m o initial g) := by
  apply measurable_pi_lambda
  intro t
  have hexp (k : ℕ) : Measurable (fun p : (Coordinate N→Bool×Bool)×(ℕ→ModeRecord n)=>
      (wholeRecords i m o p k).transaction.expenditure) :=
    (show Measurable (fun r : ModeRecord n=>r.transaction.expenditure) from fun _ _=>trivial).comp
      ((measurable_pi_apply k).comp (measurable_wholeRecords i m o))
  exact (measurable_const.add measurable_const).sub (Finset.measurable_sum (Finset.range t) (fun k _=>hexp k))

/-- Source-level P6 and payment BEFORE every fee. The known cap and external
port permissions imply the entire actual budget, not a supplied viability field. -/
theorem actual_joint_prepay_funded {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price width d u : ℚ) (o : Organism n)
    (cap g initial : ℝ) (hcap : (m.writeCost : ℝ) ≤ cap) (hg : cap ≤ g) (hi : 0 ≤ initial) :
    ∀ᵐ p ∂jointLaw (N:=N) i noise m epsilon he price width d u o,
      ResourceViable initial (fun _=>g) (fun t=>(wholeRecords i m o p t).transaction.expenditure) ∧
      ∀t,(wholeRecords i m o p t).transaction.expenditure ≤ balance i m o initial g p t+g := by
  filter_upwards [actual_whole_cost_bounds i noise m epsilon he price width d u o] with p hp
  have hb (t : ℕ) : (wholeRecords i m o p t).transaction.expenditure ≤ g:=(hp t).2.trans (hcap.trans hg)
  have hv:=resourceViable_of_pointwise_cost_le_replenish initial (fun _=>g)
    (fun t=>(wholeRecords i m o p t).transaction.expenditure) hi hb
  refine ⟨hv,fun t=>?_⟩
  have ht:=hv t
  change 0 ≤ balance i m o initial g p t at ht
  linarith [hb t]

/-- The resource coordinate is a deterministic open-environment augmentation;
erasing it returns the EXACT original training/deployment joint source. -/
def fundedLaw {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price width d u : ℚ) (o : Organism n) (initial g : ℝ) :=
  (jointLaw (N:=N) i noise m epsilon he price width d u o).map
    (fun p=>(p,balance i m o initial g p))

instance fundedLaw_probability {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price width d u : ℚ) (o : Organism n) (initial g : ℝ) :
    IsProbabilityMeasure (fundedLaw (N:=N) i noise m epsilon he price width d u o initial g) :=
  Measure.isProbabilityMeasure_map (measurable_id.prodMk (measurable_balance i m o initial g)).aemeasurable

theorem fundedLaw_erasure {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price width d u : ℚ) (o : Organism n) (initial g : ℝ) :
    (fundedLaw (N:=N) i noise m epsilon he price width d u o initial g).map Prod.fst=
      jointLaw i noise m epsilon he price width d u o := by
  have hm : Measurable (fun p : (Coordinate N→Bool×Bool)×(ℕ→ModeRecord n)=>(p,balance i m o initial g p)) :=
    measurable_id.prodMk (measurable_balance i m o initial g)
  rw [fundedLaw,Measure.map_map measurable_fst hm]
  exact Measure.map_id

/-- No extra funding-failure probability is added: P6 is a.e. on ALL data,
while the original one Good budget controls UNKNOWN/incorrect purpose evidence. -/
theorem funded_actual_purpose_and_risk {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (N : ℕ) (hN : 0<N) (price width d u : ℚ)
    (hp : 0 ≤ price) (hw : 0<width) (hd : 0<d ∧ d<1) (hu : 0 ≤ u) (o : Organism n) (ho : o.program=m.goal)
    (cap g initial : ℝ) (hcap : (m.writeCost : ℝ) ≤ cap) (hg : cap ≤ g) (hi : 0 ≤ initial) :
    (∀ᵐ p ∂jointLaw (N:=N) i noise m epsilon he price width d u o,
      ResourceViable initial (fun _=>g) (fun t=>(wholeRecords i m o p t).transaction.expenditure)) ∧
    (∀omega∈Good noise m epsilon he N width (u : ℝ),
      classify price width d u (sourceData m width omega)≠.unknown →
      let parent:=postProbeParent i m omega o
      let p:=returnedAST i (classify price width d u (sourceData m width omega))
      let q:=returnedProgram i p
      let M:=model i noise m (priceValue price hp) epsilon he (d : ℝ) (by exact_mod_cast hd)
      IsBellmanGODSelector M (interpret p) ∧
      IsBellmanGODSelector (model (0 : Fin 1) noise m (priceValue price hp) epsilon he (d : ℝ) (by exact_mod_cast hd)) (interpret q) ∧
      actualValue i noise m epsilon he (priceValue price hp) (d : ℝ) parent p=M.optimalValue parent.physical ∧
      actualValue (0 : Fin 1) noise m epsilon he (priceValue price hp) (d : ℝ) (projectOrganism i parent) q=M.optimalValue parent.physical) ∧
    (jointLaw (N:=N) i noise m epsilon he price width d u o).real
      (Prod.fst ⁻¹' Error (N:=N) i noise m epsilon he price width d u hp hd) ≤ 
      min 1 (4*Real.exp (-2*(N : ℝ)*(u : ℝ)^2)) := by
  refine ⟨(actual_joint_prepay_funded i noise m epsilon he price width d u o cap g initial hcap hg hi).mono fun _ h=>h.1,?_,
    actual_joint_accepted_wrong_bound i noise m epsilon he N hN price width d u hp hw hd hu o⟩
  intro omega hgood ha
  have h:=actual_good_returned_program i noise m epsilon he price width d u hp hw hd omega o ho hgood ha
  exact ⟨h.2.1,h.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

/-- Exact old closed-source obstruction, reusing its ORIGINAL compiled-policy,
one-bit, positive-fault/cost quantifiers. This is not a no-go for every policy. -/
theorem zero_supply_compiled_boundary (c epsilon : NNReal) (he : epsilon ≤ 1)
    (hc : 0<c) (he0 : 0<epsilon) (he1 : epsilon<1) (history : List Bool) (reserve : ℝ) :
    let sigma:=selectorPolicy ((substrate (0 : Fin 1)).execute true)
    let o:=RegisterFaultFeedbackResource.closedParent history
    ¬∀ᵐ rs ∂recordPathLaw (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he sigma ⟨0,o.physical,o⟩,
      ResourceViable reserve (fun _=>0) (fun t=>(rs t).transaction.expenditure) := by
  simpa only [RegisterFaultFeedbackResource.idleInflow,ite_self] using
    RegisterFaultFeedbackResource.closed_not_ae_infinite_viable c epsilon he hc he0 he1 history reserve

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeResource
