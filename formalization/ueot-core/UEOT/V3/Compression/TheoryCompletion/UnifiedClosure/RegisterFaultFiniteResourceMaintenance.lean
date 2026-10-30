import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultInfiniteRecord
import UEOT.V3.Compression.Objecthood.ResourceClosure.ResourceAccounting
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterActuatorScaleSource
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
Original commitment: persistent health must be checked against SAME actual finite resource stock and full causal execution costs.
Existing result: original complete-record/all-fine-causal source, P6 actual prefix accounting, and specific compiled-policy closed-source failures.
Premise reduced: derive a universal health occupation bound and eventual loss from actual finite zero-income funding of THIS policy, not assumed affordability of all policies.
Model/boundary: original one-port mode source, positive fault epsilon and positive actual writeCost, protected program=goal, arbitrary original fine physical/action-history causal policy; epsilon0/cost0 separate.
Consumer: original ResourceViable on SAME expenditure records; auxiliary price is only a proof multiplier and changes neither actual source/policy nor original purpose evaluation.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFiniteResourceMaintenance
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord RegisterFaultInfiniteRecord
open RegisterActuatorScaleSource
open RegisterFaultControlModel
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _=>trivial⟩

/-- Actual physical health, with the protected program/goal alignment kept
explicit at the later true-record consumer. -/
def health {n : ℕ} (i : Fin n) (m : Mechanism) (x : State n) : ℝ := if x i=m.goal then 1 else 0

theorem health_nonneg {n : ℕ} (i : Fin n) (m : Mechanism) (x : State n) : 0≤health i m x := by
  unfold health; split_ifs <;> norm_num

theorem health_le_one {n : ℕ} (i : Fin n) (m : Mechanism) (x : State n) : health i m x≤1 := by
  unfold health; split_ifs <;> norm_num

/-- PROOF multiplier only. It does not select a new actual controller or
replace a registered reward contract. -/
def auxiliaryPrice (epsilon c : NNReal) : NNReal := (epsilon*c)⁻¹

theorem auxiliaryPrice_mul (epsilon c : NNReal) (he : 0<epsilon) (hc : 0<c) :
    (auxiliaryPrice epsilon c : ℝ)*(c : ℝ)=1/(epsilon : ℝ) := by
  have heR : (epsilon : ℝ)≠0 := ne_of_gt (by exact_mod_cast he)
  have hcR : (c : ℝ)≠0 := ne_of_gt (by exact_mod_cast hc)
  simp only [auxiliaryPrice,NNReal.coe_inv,NNReal.coe_mul]
  field_simp

/-- A source-derived superpotential, not a resource reserve or source field. -/
def maintenancePotential {n : ℕ} (i : Fin n) (m : Mechanism) (epsilon : NNReal) (x : State n) : ℝ :=
  (repairChance epsilon/(epsilon : ℝ))*health i m x

theorem maintenancePotential_nonneg {n : ℕ} (i : Fin n) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (x : State n) : 0≤ maintenancePotential i m epsilon x :=
  mul_nonneg (div_nonneg (sub_nonneg.mpr (by exact_mod_cast he)) epsilon.coe_nonneg) (health_nonneg i m x)

/-- EVERY actual allowed action is dominated by this same-source
superpotential, even though the auxiliary price is outside the old sufficient
optimal-selector price regime. No optimizer or budget certificate is input. -/
theorem actual_qValue_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (hepos : 0<epsilon) (hcpos : 0 < m.writeCost)
    (d : ℝ) (hd : 0<d ∧ d<1) (x : State n) (a : Action) :
    (model i noise m (auxiliaryPrice epsilon m.writeCost) epsilon he d hd).qValue
      (maintenancePotential i m epsilon) x a≤ maintenancePotential i m epsilon x := by
  have hr : 0≤repairChance epsilon := sub_nonneg.mpr (by exact_mod_cast he)
  have heR : 0<(epsilon : ℝ) := by exact_mod_cast hepos
  have hv : 0≤repairChance epsilon/(epsilon : ℝ) := div_nonneg hr heR.le
  have hbal : repairChance epsilon+repairChance epsilon*(repairChance epsilon/(epsilon : ℝ))=
      repairChance epsilon/(epsilon : ℝ) := by
    unfold repairChance
    field_simp
    ring
  have hdv := mul_le_of_le_one_left (mul_nonneg hr hv) hd.2.le
  have hbase : repairChance epsilon+d*(repairChance epsilon*(repairChance epsilon/(epsilon : ℝ)))≤
      repairChance epsilon/(epsilon : ℝ) := by linarith
  have hinv : 1/(epsilon : ℝ)=1+repairChance epsilon/(epsilon : ℝ) := by
    unfold repairChance
    field_simp
    ring
  have hbad : maintenancePotential i m epsilon (Function.update x i (!m.goal))=0 := by
    cases hg:m.goal <;> simp [maintenancePotential,health,hg]
  rw [qValue_source,hbad,mul_zero,add_zero]
  cases a with
  | none =>
    by_cases hx : x i=m.goal
    · simpa [maintenancePotential,health,update,cost,hx] using hbase
    · simp [maintenancePotential,health,update,cost,hx]
  | some b =>
    have hp:=auxiliaryPrice_mul epsilon m.writeCost hepos hcpos
    by_cases hb : b=m.goal <;> by_cases hx : x i=m.goal <;>
      simp [maintenancePotential,health,update,cost,hb,hx,hp,hinv] <;>
      nlinarith [mul_nonneg hr (one_div_nonneg.mpr heR.le)]

/-- Native recursive causal-policy verification, specialized to the SAME
original model. Arbitrary time-varying randomized full fine-history policies
are retained; no Markov or coarse-factor restriction is added. -/
theorem actual_truncatedValue_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (hepos : 0<epsilon) (hcpos : 0 < m.writeCost)
    (d : ℝ) (hd : 0<d ∧ d<1) (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) :
    ∀ k {t : ℕ} (h : pi.Memory t),pi.truncatedValue
      (model i noise m (auxiliaryPrice epsilon m.writeCost) epsilon he d hd) k h≤
      maintenancePotential i m epsilon (pi.current h) := by
  let M:=model i noise m (auxiliaryPrice epsilon m.writeCost) epsilon he d hd
  intro k
  induction k with
  | zero => intro t h; exact maintenancePotential_nonneg i m epsilon he _
  | succ k ih =>
    intro t h
    rw [CausalPolicy.truncatedValue_succ]
    calc
      _ ≤ ∑ a,pi.actionProb h a*M.qValue (maintenancePotential i m epsilon) (pi.current h) a := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (pi.actionProb_nonneg h a)
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ hd.1.le
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ (M.transition_nonneg _ _ _)
        simpa only [pi.current_advance] using ih (pi.advance h a y)
      _ ≤ ∑ a,pi.actionProb h a*maintenancePotential i m epsilon (pi.current h) :=
        Finset.sum_le_sum (fun a _=>mul_le_mul_of_nonneg_left
          (actual_qValue_bound i noise m epsilon he hepos hcpos d hd _ a) (pi.actionProb_nonneg h a))
      _ = _ := by rw [←Finset.sum_mul,pi.actionProb_sum_one,one_mul]

private def discountApproach (n : ℕ) : ℝ := 1-1/((n+2 : ℕ) : ℝ)
private theorem discountApproach_valid (n : ℕ) : 0<discountApproach n ∧ discountApproach n<1 := by
  have hn : (1 : ℝ)<((n+2 : ℕ) : ℝ) := by exact_mod_cast (show 1<n+2 by omega)
  have hp : 0<((n+2 : ℕ) : ℝ) := by positivity
  unfold discountApproach
  exact ⟨sub_pos.mpr ((div_lt_one hp).mpr hn),sub_lt_self _ (one_div_pos.mpr hp)⟩
private theorem discountApproach_tendsto : Tendsto discountApproach atTop (𝓝 1) := by
  have hd : Tendsto (fun n : ℕ=>((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hi : Tendsto (fun n : ℕ=>1/((n+2 : ℕ) : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hd
  change Tendsto (fun n : ℕ=>1-1/((n+2 : ℕ) : ℝ)) atTop (𝓝 1)
  simpa only [sub_zero] using hi.const_sub 1

private theorem discountedPayoff_continuous {n : ℕ} (price : NNReal) (rs : List (ModeRecord n)) :
    Continuous (fun d : ℝ=>discountedPayoff price d rs) := by
  induction rs with
  | nil => exact continuous_const
  | cons r rs ih => exact continuous_const.add (continuous_id.mul ih)

/-- The discount-one expression is a finite ACTUAL prefix polynomial.
No discount-one infinite model or exchange of infinite limits is used. -/
theorem actual_net_prefix_expectation_le {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (hepos : 0<epsilon) (hcpos : 0 < m.writeCost)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) (N : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n)
    (hx : o.physical=pi.current h) (hp : o.program=m.goal) :
    actualExpectation i noise m epsilon he pi (auxiliaryPrice epsilon m.writeCost) 1 N h o≤
      maintenancePotential i m epsilon o.physical := by
  have hc : Continuous (fun d : ℝ=>actualExpectation i noise m epsilon he pi (auxiliaryPrice epsilon m.writeCost) d N h o) :=
    continuous_finsetSum _ (fun w _=>continuous_const.mul (discountedPayoff_continuous _ _))
  apply le_of_tendsto (hc.continuousAt.tendsto.comp discountApproach_tendsto)
  apply Eventually.of_forall
  intro j
  dsimp only [Function.comp_apply]
  rw [actualExpectation_eq_truncatedValue i noise m epsilon he pi (auxiliaryPrice epsilon m.writeCost)
    (discountApproach j) (discountApproach_valid j) N h o hx hp,hx]
  exact actual_truncatedValue_bound i noise m epsilon he hepos hcpos _ (discountApproach_valid j) pi N h

local instance {n : ℕ} (i : Fin n) (o : Organism n) : Decidable (Legitimate i o) :=
  inferInstanceAs (Decidable (o.physical i=o.program))
local instance {n : ℕ} : MeasurableSpace (List (ModeRecord n)) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (List (ModeRecord n)) := ⟨fun _=>trivial⟩

/-- SAME actual post-transaction legitimacy, not a desired health variable. -/
def recordHealth {n : ℕ} (i : Fin n) (r : ModeRecord n) : ℝ :=
  if Legitimate i r.transaction.parentAfter then 1 else 0

def prefixHealth {n : ℕ} (i : Fin n) (N : ℕ) (rs : ℕ→ModeRecord n) : ℝ :=
  ∑ k∈Finset.range N,recordHealth i (rs k)
def prefixCost {n : ℕ} (N : ℕ) (rs : ℕ→ModeRecord n) : ℝ :=
  ∑ k∈Finset.range N,(rs k).transaction.expenditure
private def prefixPayoff {n : ℕ} (price : NNReal) (N : ℕ) (rs : ℕ→ModeRecord n) : ℝ :=
  ∑ k∈Finset.range N,RegisterJointRecord.payoff price (rs k).transaction

@[fun_prop] theorem recordHealth_measurable {n : ℕ} (i : Fin n) : Measurable (recordHealth i) := by
  intro s hs;trivial

theorem recordHealth_nonneg {n : ℕ} (i : Fin n) (r : ModeRecord n) : 0≤recordHealth i r := by
  unfold recordHealth;split_ifs <;>norm_num
theorem recordHealth_norm_le {n : ℕ} (i : Fin n) (r : ModeRecord n) : ‖recordHealth i r‖≤1 := by
  unfold recordHealth;split_ifs <;>norm_num

private theorem prefix_measurable {n : ℕ} (F : ModeRecord n→ℝ) (N : ℕ) :
    Measurable (fun rs : ℕ→ModeRecord n=>∑ k∈Finset.range N,F (rs k)) :=
  Finset.measurable_fun_sum _ (fun k _=>(show Measurable F by intro s hs;trivial).comp (measurable_pi_apply k))

private theorem run_program {n : ℕ} (i : Fin n) (m : Mechanism)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) (c : Config pi) (es : List Event) :
    (run i m pi c es).2.2.program=c.2.2.program := by
  induction es generalizing c with
  | nil =>rfl
  | cons e es ih =>
    change (run i m pi (advance i m pi c e) es).2.2.program=_
    rw [ih]
    exact step_program i m c.2.2 e.1 e.2.1 e.2.2

private theorem step_payoff_health {n : ℕ} (i : Fin n) (m : Mechanism) (price : NNReal)
    (o : Organism n) (hp : o.program=m.goal) (a : Action) (mode label : Bool) :
    RegisterJointRecord.payoff price (modeRecordStep i m o a mode label).transaction=
      recordHealth i (modeRecordStep i m o a mode label)-
      (price : ℝ)*(modeRecordStep i m o a mode label).transaction.expenditure := by
  cases mode
  · cases hg:m.goal <;> simp [RegisterJointRecord.payoff,recordHealth,Legitimate,modeRecordStep,hp,hg,childCount]
  · by_cases h : update i o.physical a i=o.program <;>
      simp [RegisterJointRecord.payoff,recordHealth,Legitimate,modeRecordStep,RegisterJointRecord.recordStep,h,childCount]

private theorem step_cost_bound {n : ℕ} (i : Fin n) (m : Mechanism)
    (o : Organism n) (a : Action) (mode label : Bool) :
    0≤(modeRecordStep i m o a mode label).transaction.expenditure ∧
      (modeRecordStep i m o a mode label).transaction.expenditure≤ m.writeCost := by
  cases mode <;> cases a <;> simp [modeRecordStep,RegisterJointRecord.recordStep,cost,m.writeCost.coe_nonneg]

private theorem integrable_prefix_source {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) (c : Config pi)
    (F : ModeRecord n→ℝ) (C : ℝ)
    (hb : ∀ o a mode label,‖F (modeRecordStep i m o a mode label)‖≤C) (N : ℕ) :
    Integrable (fun rs : ℕ→ModeRecord n=>∑ k∈Finset.range N,F (rs k)) (recordPathLaw i noise m epsilon he pi c) := by
  rw [recordPathLaw]
  apply (integrable_map_measure (prefix_measurable F N).aestronglyMeasurable
    (measurable_recordStream i m pi c).aemeasurable).mpr
  apply Integrable.of_bound ((prefix_measurable F N).comp (measurable_recordStream i m pi c)).aestronglyMeasurable
    ((N : ℝ)*C)
  apply ae_of_all
  intro z
  calc
    _ ≤ ∑ k∈Finset.range N,‖F (recordAt i m pi c z k)‖ := norm_sum_le _ _
    _ ≤ ∑ k∈Finset.range N,C := Finset.sum_le_sum (fun k _=>hb _ _ _ _)
    _ = _ := by simp

private theorem integrable_prefixCost {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) (c : Config pi) (N : ℕ) :
    Integrable (prefixCost N) (recordPathLaw i noise m epsilon he pi c) :=
  integrable_prefix_source i noise m epsilon he pi c (fun r=>r.transaction.expenditure) m.writeCost
    (fun o a mode label=>by
      rw [Real.norm_of_nonneg (step_cost_bound i m o a mode label).1]
      exact (step_cost_bound i m o a mode label).2) N

private theorem prefixPayoff_integral {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action))
    {t : ℕ} (h : pi.Memory t) (o : Organism n) (price : NNReal) (N : ℕ) :
    (∫ rs,prefixPayoff price N rs ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩)=
      actualExpectation i noise m epsilon he pi price 1 N h o := by
  let c : Config pi:=⟨t,h,o⟩
  have hpref : Measurable (prefixPayoff (n:=n) price N) :=
    prefix_measurable (fun r : ModeRecord n=>RegisterJointRecord.payoff price r.transaction) N
  rw [recordPathLaw,integral_map (measurable_recordStream i m pi c).aemeasurable hpref.aestronglyMeasurable]
  have ha : (fun z=>prefixPayoff price N (fun k=>recordAt i m pi c z k))=ᵐ[wordPathLaw i noise m epsilon he pi c]
      fun z=>discountedPayoff price 1 (trace i m pi c (z N)) := by
    filter_upwards [wordPathLaw_ae_coherent i noise m epsilon he pi c] with z hz
    rw [coherent_trace_eq_stream i m pi c z hz.1 hz.2 N,stream_prefix_payoff_sum]
    simp only [discountedTerm,stageAt,one_pow,one_mul,prefixPayoff]
  rw [integral_congr_ae ha]
  have hm : Measurable (fun z : ℕ→List Event=>trace i m pi c (z N)) :=
    (measurable_of_countable _).comp (measurable_pi_apply N)
  rw [←integral_map hm.aemeasurable (show Measurable (discountedPayoff (n:=n) price 1) by intro s hs;trivial).aestronglyMeasurable,
    actual_record_prefix_law,integral_recordLaw_eq_actualExpectation]

private theorem prefixPayoff_health_cost {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action))
    {t : ℕ} (h : pi.Memory t) (o : Organism n) (hp : o.program=m.goal) (price : NNReal) (N : ℕ) :
    prefixPayoff price N=ᵐ[recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩]
      fun rs=>prefixHealth i N rs-(price : ℝ)*prefixCost N rs := by
  rw [recordPathLaw]
  apply (ae_map_iff (measurable_recordStream i m pi ⟨t,h,o⟩).aemeasurable
    ((show Measurable (prefixPayoff (n:=n) price N) from
        prefix_measurable (fun r : ModeRecord n=>RegisterJointRecord.payoff price r.transaction) N).stronglyMeasurable.measurableSet_eq_fun
      (((show Measurable (prefixHealth i N) from prefix_measurable (recordHealth i) N).sub
        (measurable_const.mul (show Measurable (prefixCost (n:=n) N) from
          prefix_measurable (fun r : ModeRecord n=>r.transaction.expenditure) N))).stronglyMeasurable))).mpr
  apply ae_of_all
  intro z
  simp only [Pi.sub_apply,Pi.mul_apply,prefixPayoff,prefixHealth,prefixCost,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hpr : (run i m pi ⟨t,h,o⟩ (z k)).2.2.program=m.goal :=
    (run_program i m pi ⟨t,h,o⟩ (z k)).trans hp
  exact step_payoff_health i m price _ hpr _ _ _

private theorem recordHealth_integrable {n : ℕ} (i : Fin n) (mu : Measure (ℕ→ModeRecord n)) [IsFiniteMeasure mu] (k : ℕ) :
    Integrable (fun rs=>recordHealth i (rs k)) mu :=
  Integrable.of_bound ((recordHealth_measurable i).comp (measurable_pi_apply k)).aestronglyMeasurable 1
    (ae_of_all _ (fun _rs=>recordHealth_norm_le i _))

/-- Original P6 viability, applied to literal recorded cost and ZERO income,
not a reserve certificate field or a claim that every policy is affordable. -/
theorem actual_prefix_health_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (hepos : 0<epsilon) (hcpos : 0 < m.writeCost)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) {t : ℕ} (h : pi.Memory t) (o : Organism n)
    (hx : o.physical=pi.current h) (hp : o.program=m.goal) (R : NNReal)
    (hfund : ∀ᵐ rs ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩,
      ResourceViable R (fun _=>0) (fun k=>(rs k).transaction.expenditure)) (N : ℕ) :
    (∑ k∈Finset.range N,∫ rs,recordHealth i (rs k) ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩)≤
      maintenancePotential i m epsilon o.physical+(auxiliaryPrice epsilon m.writeCost : ℝ)*(R : ℝ) := by
  let mu:=recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩
  let price:=auxiliaryPrice epsilon m.writeCost
  have hH : Integrable (prefixHealth i N) mu := integrable_finsetSum _ (fun k _=>recordHealth_integrable i mu k)
  have hC : Integrable (prefixCost N) mu := integrable_prefixCost i noise m epsilon he pi ⟨t,h,o⟩ N
  have hcost : (∫ rs,prefixCost N rs ∂mu)≤(R : ℝ) := by
    have hle : ∀ᵐ rs ∂mu,prefixCost N rs≤(R : ℝ) := hfund.mono (fun rs hr=>by
      have hh:=(resourceViable_iff_cumulative_cost_le (R : ℝ) (fun _=>0) (fun k=>(rs k).transaction.expenditure)).mp hr N
      simpa only [prefixCost,Finset.sum_const_zero,add_zero] using hh)
    simpa only [integral_const,probReal_univ,one_smul] using integral_mono_ae hC (integrable_const (R : ℝ)) hle
  have hnet : (∫ rs,prefixPayoff price N rs ∂mu)≤ maintenancePotential i m epsilon o.physical := by
    rw [prefixPayoff_integral i noise m epsilon he pi h o price N]
    exact actual_net_prefix_expectation_le i noise m epsilon he hepos hcpos pi N h o hx hp
  rw [integral_congr_ae (prefixPayoff_health_cost i noise m epsilon he pi h o hp price N),
    integral_sub hH (hC.const_mul (price : ℝ)),integral_const_mul] at hnet
  have hs : (∫ rs,prefixHealth i N rs ∂mu)=∑ k∈Finset.range N,∫ rs,recordHealth i (rs k) ∂mu :=
    integral_finsetSum _ (fun k _=>recordHealth_integrable i mu k)
  rw [hs] at hnet
  have hpR:=mul_le_mul_of_nonneg_left hcost price.coe_nonneg
  linarith

/-- Quantitative health-time budget, including the actual initial health.
The same fixed epsilon/fee/stock/source is used for EVERY original causal pi
that satisfies its actual P6 zero-income record budget. -/
theorem actual_finite_health_time_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (hepos : 0<epsilon) (hcpos : 0 < m.writeCost)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) {t : ℕ} (h : pi.Memory t) (o : Organism n)
    (hx : o.physical=pi.current h) (hp : o.program=m.goal) (R : NNReal)
    (hfund : ∀ᵐ rs ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩,
      ResourceViable R (fun _=>0) (fun k=>(rs k).transaction.expenditure)) (N : ℕ) :
    (epsilon : ℝ)*(health i m o.physical+
      ∑ k∈Finset.range N,∫ rs,recordHealth i (rs k) ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩)≤
      health i m o.physical+(R : ℝ)/(m.writeCost : ℝ) := by
  have hb:=actual_prefix_health_bound i noise m epsilon he hepos hcpos pi h o hx hp R hfund N
  have hs:=mul_le_mul_of_nonneg_left hb epsilon.coe_nonneg
  have heR : (epsilon : ℝ)≠0 := ne_of_gt (by exact_mod_cast hepos)
  have hcR : (m.writeCost : ℝ)≠0 := ne_of_gt (by exact_mod_cast hcpos)
  have hpot : (epsilon : ℝ)*maintenancePotential i m epsilon o.physical=repairChance epsilon*health i m o.physical := by
    unfold maintenancePotential
    field_simp
  have hpR : (epsilon : ℝ)*(auxiliaryPrice epsilon m.writeCost : ℝ)=1/(m.writeCost : ℝ) := by
    simp only [auxiliaryPrice,NNReal.coe_inv,NNReal.coe_mul]
    field_simp
  rw [mul_add,hpot,←mul_assoc,hpR] at hs
  unfold repairChance at hs
  simp only [div_eq_mul_inv, one_mul] at hs ⊢
  nlinarith

/-- Expected actual post-legitimacy occupation is summable; no discount or
change of the event/source is inserted in this infinite-time conclusion. -/
theorem actual_expected_health_summable {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (hepos : 0<epsilon) (hcpos : 0 < m.writeCost)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) {t : ℕ} (h : pi.Memory t) (o : Organism n)
    (hx : o.physical=pi.current h) (hp : o.program=m.goal) (R : NNReal)
    (hfund : ∀ᵐ rs ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩,
      ResourceViable R (fun _=>0) (fun k=>(rs k).transaction.expenditure)) :
    Summable (fun k=>∫ rs,recordHealth i (rs k) ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩) :=
  summable_of_sum_range_le (fun _k=>integral_nonneg (fun _rs=>recordHealth_nonneg i _))
    (actual_prefix_health_bound i noise m epsilon he hepos hcpos pi h o hx hp R hfund)

private theorem health_series {n : ℕ} (i : Fin n) (mu : Measure (ℕ→ModeRecord n)) [IsFiniteMeasure mu]
    (hs : Summable (fun k=>∫ rs,recordHealth i (rs k) ∂mu)) :
    Integrable (fun rs=>∑' k,recordHealth i (rs k)) mu ∧
      ∀ᵐ rs ∂mu,Summable (fun k=>recordHealth i (rs k)) := by
  let F (k : ℕ) (rs : ℕ→ModeRecord n):=recordHealth i (rs k)
  have hi (k : ℕ) : Integrable (F k) mu :=recordHealth_integrable i mu k
  let X (k : ℕ) : Lp ℝ 1 mu :=(hi k).toL1 (F k)
  have hn (k : ℕ) : ‖X k‖=∫ rs,F k rs ∂mu := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [(hi k).coeFn_toL1] with rs hr
    rw [hr,Real.norm_of_nonneg (recordHealth_nonneg i _)]
  have hns : Summable (fun k=>‖X k‖) :=by simpa only [hn] using hs
  have hne : ∑' k,‖X k‖ₑ≠⊤ :=by simpa only [← ofReal_norm] using hns.tsum_ofReal_ne_top
  have ha:=Lp.hasSum_coeFn_tsum hne
  have heq : ∀ᵐ rs ∂mu,∀ k,X k rs=F k rs :=ae_all_iff.mpr (fun k=>(hi k).coeFn_toL1)
  have hh : ∀ᵐ rs ∂mu,HasSum (fun k=>F k rs) ((∑' k,X k) rs) :=by
    filter_upwards [ha,heq] with rs hr he
    simpa only [he] using hr
  constructor
  · apply (L1.integrable_coeFn (∑' k,X k)).congr
    filter_upwards [hh] with rs hr using hr.tsum_eq.symm
  · exact hh.mono (fun rs hr=>hr.summable)

/-- The actual undiscounted total number of legitimate post-transactions is
integrable, and is finite on one common full-measure event. -/
theorem actual_health_time_integrable {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (hepos : 0<epsilon) (hcpos : 0 < m.writeCost)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) {t : ℕ} (h : pi.Memory t) (o : Organism n)
    (hx : o.physical=pi.current h) (hp : o.program=m.goal) (R : NNReal)
    (hfund : ∀ᵐ rs ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩,
      ResourceViable R (fun _=>0) (fun k=>(rs k).transaction.expenditure)) :
    Integrable (fun rs=>∑' k,recordHealth i (rs k)) (recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩) ∧
      ∀ᵐ rs ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩,Summable (fun k=>recordHealth i (rs k)) :=
  health_series i _ (actual_expected_health_summable i noise m epsilon he hepos hcpos pi h o hx hp R hfund)

/-- No original fine causal policy can maintain legitimate post-transactions
forever, provided THAT policy actually obeys the finite stock/zero-income
P6 budget. This includes epsilon=1 and makes no universal affordability claim. -/
theorem actual_eventually_never_legitimate {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (hepos : 0<epsilon) (hcpos : 0 < m.writeCost)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) {t : ℕ} (h : pi.Memory t) (o : Organism n)
    (hx : o.physical=pi.current h) (hp : o.program=m.goal) (R : NNReal)
    (hfund : ∀ᵐ rs ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩,
      ResourceViable R (fun _=>0) (fun k=>(rs k).transaction.expenditure)) :
    ∀ᵐ rs ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩,
      ∃ N,∀ k≥N,¬Legitimate i (rs k).transaction.parentAfter := by
  filter_upwards [(actual_health_time_integrable i noise m epsilon he hepos hcpos pi h o hx hp R hfund).2] with rs hr
  have ht:=hr.tendsto_atTop_zero
  have hh : ∀ᶠ k in atTop,recordHealth i (rs k)<1/2 :=ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N,hN⟩:=eventually_atTop.mp hh
  exact ⟨N,fun k hk hl=>by have hbad:=hN k hk; norm_num [recordHealth,hl] at hbad⟩

/-- SAME actual infinite-record occupation has the original finite-stock
bound. The initial transaction state is included separately and costs are
literal paid expenditures, not requested-write counts. -/
theorem actual_total_health_time_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (hepos : 0<epsilon) (hcpos : 0 < m.writeCost)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) {t : ℕ} (h : pi.Memory t) (o : Organism n)
    (hx : o.physical=pi.current h) (hp : o.program=m.goal) (R : NNReal)
    (hfund : ∀ᵐ rs ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩,
      ResourceViable R (fun _=>0) (fun k=>(rs k).transaction.expenditure)) :
    (epsilon : ℝ)*(health i m o.physical+
      ∫ rs,(∑' k,recordHealth i (rs k)) ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩)≤
        health i m o.physical+(R : ℝ)/(m.writeCost : ℝ) ∧
      health i m o.physical+(R : ℝ)/(m.writeCost : ℝ)≤1+(R : ℝ)/(m.writeCost : ℝ) := by
  let mu:=recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩
  have hi (k : ℕ) :=recordHealth_integrable i mu k
  have hs:=actual_expected_health_summable i noise m epsilon he hepos hcpos pi h o hx hp R hfund
  have hsn : Summable (fun k=>∫ rs,‖recordHealth i (rs k)‖ ∂mu) :=by
    simpa only [Real.norm_of_nonneg (recordHealth_nonneg i _)] using hs
  have heq:=integral_tsum_of_summable_integral_norm hi hsn
  have hb:=hs.tsum_le_of_sum_range_le (actual_prefix_health_bound i noise m epsilon he hepos hcpos pi h o hx hp R hfund)
  rw [heq] at hb
  have hh:=mul_le_mul_of_nonneg_left hb epsilon.coe_nonneg
  have heR : (epsilon : ℝ)≠0 :=ne_of_gt (by exact_mod_cast hepos)
  have hcR : (m.writeCost : ℝ)≠0 :=ne_of_gt (by exact_mod_cast hcpos)
  have hpot : (epsilon : ℝ)*maintenancePotential i m epsilon o.physical=repairChance epsilon*health i m o.physical :=by
    unfold maintenancePotential
    field_simp
  have hpR : (epsilon : ℝ)*(auxiliaryPrice epsilon m.writeCost : ℝ)=1/(m.writeCost : ℝ) :=by
    simp only [auxiliaryPrice,NNReal.coe_inv,NNReal.coe_mul]
    field_simp
  rw [mul_add,hpot,←mul_assoc,hpR] at hh
  unfold repairChance at hh
  simp only [div_eq_mul_inv,one_mul] at hh ⊢
  constructor
  · nlinarith
  · linarith [health_le_one i m o.physical]


/-- Exact source-computed undiscounted health-prefix expectation, with the
actual protected program/initial-memory alignment explicit. No discount-one
infinite model is asserted. -/
theorem actual_prefix_health_expectation {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action))
    {t : ℕ} (h : pi.Memory t) (o : Organism n) (hp : o.program=m.goal) (N : ℕ) :
    (∫ rs,prefixHealth i N rs ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩)=
      actualExpectation i noise m epsilon he pi 0 1 N h o :=by
  rw [←prefixPayoff_integral i noise m epsilon he pi h o 0 N]
  apply integral_congr_ae
  filter_upwards [prefixPayoff_health_cost i noise m epsilon he pi h o hp 0 N] with rs hr
  simpa only [NNReal.coe_zero,zero_mul,sub_zero] using hr.symm

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFiniteResourceMaintenance
