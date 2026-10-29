import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultControlModel
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointRecord
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBirthMaintenance

/-! Complete literal transaction records under the common P5 fault mode.
The same causal policy observes actions/next physical states, not the fresh mode
or birth label. A fault record marks the selected action as NOT executed, records
physical damage and has no child or controlled-action charge. All stages remain,
including faults and failed births. Birth transaction counts retain the earlier
single-lineage-address limitation; global unique child IDs are not claimed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultJointRecord
open MeasureTheory
open UEOT.V3.FiniteDiscountedControl
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterJointRecord RegisterFaultControlModel
open scoped BigOperators ENNReal
noncomputable section

structure ModeRecord (n : ℕ) where
  repairMode : Bool
  transaction : Record n

def modeRecordStep {n : ℕ} (i : Fin n) (m : Mechanism)
    (o : Organism n) (a : Action) (mode label : Bool) : ModeRecord n :=
  if mode then ⟨true, recordStep i m o a label⟩ else
    ⟨false, { parentBefore := o
              action := a
              label := label
              parentAfter := {o with physical := Function.update o.physical i (!m.goal)}
              child := none
              expenditure := 0 }⟩

@[simp] theorem step_physical {n : ℕ} (i : Fin n) (m : Mechanism)
    (o : Organism n) (a : Action) (mode label : Bool) :
    (modeRecordStep i m o a mode label).transaction.parentAfter.physical =
      modeNext i m o.physical a mode := by
  cases mode <;> rfl

@[simp] theorem step_program {n : ℕ} (i : Fin n) (m : Mechanism)
    (o : Organism n) (a : Action) (mode label : Bool) :
    (modeRecordStep i m o a mode label).transaction.parentAfter.program = o.program := by
  cases mode <;> rfl

@[simp] theorem step_history {n : ℕ} (i : Fin n) (m : Mechanism)
    (o : Organism n) (a : Action) (mode label : Bool) :
    (modeRecordStep i m o a mode label).transaction.parentAfter.history = o.history := by
  cases mode <;> rfl

theorem step_payoff {n : ℕ} (i : Fin n) (m : Mechanism) (price : NNReal)
    (o : Organism n) (a : Action) (mode label : Bool) (hp : o.program = m.goal) :
    payoff price (modeRecordStep i m o a mode label).transaction =
      modePayoff i m price o.physical a mode label := by
  cases mode with
  | false => simp [modeRecordStep, payoff, childCount, modePayoff]
  | true =>
      change payoff price (recordStep i m o a label) = _
      rw [record_payoff_eq i m price o a label hp]
      change _ = childCount (outcome i m o.physical a label) - (price : ℝ) * cost m a
      unfold outcome
      by_cases h : update i o.physical a i = m.goal <;> simp [h, childCount]

@[reducible] def Tape : ℕ → Type
  | 0 => Unit
  | k+1 => Action × Bool × Bool × Tape k

@[reducible] instance tapeFintype : (k : ℕ) → Fintype (Tape k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k+1 => by
    letI := tapeFintype k
    exact inferInstanceAs (Fintype (Action × Bool × Bool × Tape k))

variable {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
variable (epsilon : NNReal) (he : epsilon ≤ 1)
variable (pi : CausalPolicy.{0,0,0} (State n) (fun _ => Action))

def records : (k : ℕ) → {t : ℕ} → pi.Memory t → Organism n → Tape k → List (ModeRecord n)
  | 0, _, _, _, _ => []
  | k+1, _, h, o, (a,mode,label,rest) =>
      let r := modeRecordStep i m o a mode label
      r :: records k (pi.advance h a r.transaction.parentAfter.physical) r.transaction.parentAfter rest

def weight : (k : ℕ) → {t : ℕ} → pi.Memory t → Organism n → Tape k → ℝ
  | 0, _, _, _, _ => 1
  | k+1, _, h, o, (a,mode,label,rest) =>
      let r := modeRecordStep i m o a mode label
      pi.actionProb h a * (modeLaw epsilon he mode).toReal * (noise label).toReal *
        weight k (pi.advance h a r.transaction.parentAfter.physical) r.transaction.parentAfter rest

private theorem pmf_sum_real (q : PMF Bool) : ∑ b, (q b).toReal = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe q)
  rw [tsum_fintype, ENNReal.toReal_sum (fun b _ => PMF.apply_ne_top _ b)] at h
  simpa using h

theorem weight_nonneg : ∀ (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) (w : Tape k),
    0 ≤ weight i noise m epsilon he pi k h o w := by
  intro k
  induction k with
  | zero => intros; exact zero_le_one
  | succ k ih =>
      rintro t h o ⟨a,mode,label,rest⟩
      exact mul_nonneg (mul_nonneg (mul_nonneg (pi.actionProb_nonneg h a)
        ENNReal.toReal_nonneg) ENNReal.toReal_nonneg) (ih _ _ _)

theorem weight_sum_one : ∀ (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n),
    ∑ w : Tape k, weight i noise m epsilon he pi k h o w = 1 := by
  intro k
  induction k with
  | zero => intros; simp [Tape, weight]
  | succ k ih =>
      intro t h o
      simp only [Tape, Fintype.sum_prod_type, weight]
      simp_rw [← Finset.mul_sum, ih, mul_one]
      simp_rw [← Finset.mul_sum, pmf_sum_real, mul_one]
      simp_rw [← Finset.mul_sum, pmf_sum_real, mul_one]
      exact pi.actionProb_sum_one h

def tapeLaw (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) : PMF (Tape k) :=
  FiniteProbabilityRow.ofRealRow (weight i noise m epsilon he pi k h o)
    (weight_nonneg i noise m epsilon he pi k h o) (weight_sum_one i noise m epsilon he pi k h o)

def recordLaw (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) : PMF (List (ModeRecord n)) :=
  (tapeLaw i noise m epsilon he pi k h o).map (records i m pi k h o)

def discountedPayoff {n : ℕ} (price : NNReal) (d : ℝ) : List (ModeRecord n) → ℝ
  | [] => 0
  | r :: rs => payoff price r.transaction + d * discountedPayoff price d rs

def actualExpectation (price : NNReal) (d : ℝ) (k : ℕ)
    {t : ℕ} (h : pi.Memory t) (o : Organism n) : ℝ :=
  ∑ w : Tape k, (tapeLaw i noise m epsilon he pi k h o w).toReal *
    discountedPayoff price d (records i m pi k h o w)

private theorem weighted_affine {S : Type*} [Fintype S] (p : S → ℝ)
    (hm : ∑ w, p w = 1) (c d : ℝ) (v : S → ℝ) :
    (∑ w, p w * (c + d * v w)) = c + d * ∑ w, p w * v w := by
  calc
    _ = (∑ w, p w) * c + d * (∑ w, p w * v w) := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = _ := by rw [hm, one_mul]

/-- Exact first-step decomposition of the actual complete transaction law. -/
theorem actualExpectation_succ (price : NNReal) (d : ℝ)
    (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) :
    actualExpectation i noise m epsilon he pi price d (k+1) h o =
      ∑ a, ∑ mode, ∑ label,
        pi.actionProb h a * (modeLaw epsilon he mode).toReal * (noise label).toReal *
          (payoff price (modeRecordStep i m o a mode label).transaction + d *
            actualExpectation i noise m epsilon he pi price d k
              (pi.advance h a (modeRecordStep i m o a mode label).transaction.parentAfter.physical)
              (modeRecordStep i m o a mode label).transaction.parentAfter) := by
  classical
  simp only [actualExpectation, tapeLaw, FiniteProbabilityRow.ofRealRow_apply_toReal]
  change (∑ w : Action × Bool × Bool × Tape k, _) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro mode _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro label _
  simp only [records, discountedPayoff, weight]
  let C := pi.actionProb h a * (modeLaw epsilon he mode).toReal * (noise label).toReal
  let next := (modeRecordStep i m o a mode label).transaction.parentAfter
  let W := weight i noise m epsilon he pi k (pi.advance h a next.physical) next
  let V := fun w => discountedPayoff price d (records i m pi k (pi.advance h a next.physical) next w)
  let c := payoff price (modeRecordStep i m o a mode label).transaction
  change (∑ w : Tape k, C * W w * (c + d * V w)) = C * (c + d * ∑ w, W w * V w)
  calc
    _ = C * (∑ w : Tape k, W w * (c + d * V w)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = _ := by rw [weighted_affine W (weight_sum_one i noise m epsilon he pi k _ _)]

/-- Expectation of the actual mode-aware record equals the SAME policy's
value for the new environmental-fault model; no fault-free law is substituted. -/
theorem actualExpectation_eq_truncatedValue (price : NNReal) (d : ℝ)
    (hd : 0 < d ∧ d < 1) :
    ∀ (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n),
      o.physical = pi.current h → o.program = m.goal →
      actualExpectation i noise m epsilon he pi price d k h o =
        pi.truncatedValue (RegisterFaultControlModel.model i noise m price epsilon he d hd) k h := by
  intro k
  induction k with
  | zero =>
      intro t h o hx hp
      simp [actualExpectation, tapeLaw, records, discountedPayoff, CausalPolicy.truncatedValue]
  | succ k ih =>
      intro t h o hx hp
      rw [actualExpectation_succ, CausalPolicy.truncatedValue_succ]
      apply Finset.sum_congr rfl
      intro a _
      have ht : ∀ mode label,
          actualExpectation i noise m epsilon he pi price d k
            (pi.advance h a (modeRecordStep i m o a mode label).transaction.parentAfter.physical)
            (modeRecordStep i m o a mode label).transaction.parentAfter =
          pi.truncatedValue (RegisterFaultControlModel.model i noise m price epsilon he d hd) k
            (pi.advance h a (modeNext i m o.physical a mode)) := by
        intro mode label
        rw [ih (pi.advance h a (modeRecordStep i m o a mode label).transaction.parentAfter.physical)
          (modeRecordStep i m o a mode label).transaction.parentAfter
          (pi.current_advance h a _).symm (by simpa only [step_program] using hp)]
        rw [step_physical]
      simp_rw [ht, step_payoff i m price o a _ _ hp]
      let v := fun y => pi.truncatedValue (RegisterFaultControlModel.model i noise m price epsilon he d hd) k
        (pi.advance h a y)
      have hc : (∑ mode, ∑ label, (modeLaw epsilon he mode).toReal * (noise label).toReal *
          v (modeNext i m o.physical a mode)) =
          (RegisterFaultControlModel.model i noise m price epsilon he d hd).expect o.physical a v := by
        rw [model_expect_source]
        simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, pmf_sum_real, one_mul]
        rw [Fintype.sum_bool]
        simp [modeLaw, FiniteProbabilityRow.ofRealRow_apply_toReal, modeProbability, modeNext]
      have hsum : (∑ mode, ∑ label, pi.actionProb h a * (modeLaw epsilon he mode).toReal *
          (noise label).toReal * (modePayoff i m price o.physical a mode label +
            d * v (modeNext i m o.physical a mode))) =
          pi.actionProb h a * (expectedModePayoff i noise m price epsilon he o.physical a +
            d * (∑ mode, ∑ label, (modeLaw epsilon he mode).toReal * (noise label).toReal *
              v (modeNext i m o.physical a mode))) := by
        simp only [expectedModePayoff, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
        apply congrArg₂ (fun u v : ℝ => u + v)
        all_goals
          apply Finset.sum_congr rfl
          intro mode _
          apply Finset.sum_congr rfl
          intro label _
          ring
      rw [hsum, hc, hx]
      rfl

theorem records_length : ∀ (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) (w : Tape k),
    (records i m pi k h o w).length = k := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      rintro t h o ⟨a,mode,label,rest⟩
      simp only [records, List.length_cons, ih]

theorem actual_child_requires_repair {n : ℕ} (i : Fin n) (m : Mechanism)
    (o child : Organism n) (a : Action) (mode label : Bool)
    (hc : (modeRecordStep i m o a mode label).transaction.child = some child) :
    mode = true ∧ (recordStep i m o a label).child = some child := by
  cases mode with
  | false => simp [modeRecordStep] at hc
  | true => exact ⟨rfl,hc⟩

/-- Faults remain in the trace as nonexecutions, and every successful child
comes from a true executed-repair-mode transaction of the same parent. -/
theorem records_source_semantics :
    ∀ (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) (w : Tape k),
    ∀ r ∈ records i m pi k h o w,
      r.transaction.parentBefore.history = o.history ∧
      r.transaction.parentAfter.history = o.history ∧
      r.transaction.parentBefore.program = o.program ∧
      r.transaction.parentAfter.program = o.program ∧
      (r.repairMode = false → r.transaction.child = none ∧ r.transaction.expenditure = 0) ∧
      (∀ c, r.transaction.child = some c → r.repairMode = true ∧
        (lineage i).OffspringOf r.transaction.parentAfter c ∧ c.program = o.program) := by
  intro k
  induction k with
  | zero => intro t h o w r hr; cases hr
  | succ k ih =>
      rintro t h o ⟨a,mode,label,rest⟩ r hr
      simp only [records, List.mem_cons] at hr
      rcases hr with heq | hr
      · subst r
        cases mode with
        | false =>
            refine ⟨rfl,rfl,rfl,rfl,fun _ => ⟨rfl,rfl⟩,?_⟩
            intro c hc
            simp [modeRecordStep] at hc
        | true =>
            refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
            · intro hf
              cases hf
            · intro c hc
              exact ⟨rfl,(record_child_source i m o a label c hc).2⟩
      · simpa only [step_history, step_program] using
          (ih (pi.advance h a (modeRecordStep i m o a mode label).transaction.parentAfter.physical)
            (modeRecordStep i m o a mode label).transaction.parentAfter rest r hr)

/-- Actual repair then actual fault, including the failed second birth and
zero controlled charge in fault mode. Both modes occur at positive hazard. -/
theorem two_stage_repair_then_fault (noise : PMF Bool) (c price epsilon : NNReal)
    (he : epsilon ≤ 1) (d : ℝ) (history : List Bool) (label0 label1 : Bool) :
    let m : Mechanism := ⟨true,c⟩
    let pi := selectorPolicy ((substrate (0 : Fin 1)).execute true)
    let o : Organism 1 := ⟨history, fun _ => false, true⟩
    let w : Tape 2 := (some true, true, label0, none, false, label1, ())
    (tapeLaw (0 : Fin 1) noise m epsilon he pi 2 (t := 0) (fun _ => false) o w).toReal =
        repairChance epsilon * (noise label0).toReal * (epsilon : ℝ) * (noise label1).toReal ∧
      discountedPayoff price d (records 0 m pi 2 (t := 0) (fun _ => false) o w) =
        1 - (price : ℝ) * (c : ℝ) := by
  dsimp only
  constructor
  · simp [tapeLaw, FiniteProbabilityRow.ofRealRow_apply_toReal, weight, selectorPolicy,
      modeRecordStep, recordStep, modeLaw, modeProbability, execute_compiled, update]
    ring
  · simp [records, discountedPayoff, payoff, modeRecordStep, recordStep, childCount, cost, update]

/-- Registered positive-noise transaction witness, with its failure retained.
The tape uses the compiled program, hazard 1/4 and fair birth labels. -/
theorem positive_fault_transaction_witness :
    let noise := PMF.uniformOfFintype Bool
    let m : Mechanism := ⟨true,1⟩
    let pi := selectorPolicy ((substrate (0 : Fin 1)).execute true)
    let o : Organism 1 := ⟨[], fun _ => false, true⟩
    let w : Tape 2 := (some true, true, true, none, false, false, ())
    (tapeLaw (0 : Fin 1) noise m (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)) pi 2 (t := 0) (fun _ => false) o w).toReal = 3/64 ∧
      discountedPayoff (1/2) (1/2) (records 0 m pi 2 (t := 0) (fun _ => false) o w) = 1/2 := by
  have h := two_stage_repair_then_fault (PMF.uniformOfFintype Bool) 1 (1/2) (1/4)
    (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)) (1/2) [] true false
  norm_num [PMF.uniformOfFintype_apply, repairChance] at h ⊢
  exact h

/-- Literal expenditure equals the executed-mode charge on EVERY record,
including fault-mode nonexecutions. -/
theorem records_expenditure :
    ∀ (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) (w : Tape k),
    ∀ r ∈ records i m pi k h o w,
      r.transaction.expenditure = if r.repairMode then cost m r.transaction.action else 0 := by
  intro k
  induction k with
  | zero => intro t h o w r hr; cases hr
  | succ k ih =>
      rintro t h o ⟨a,mode,label,rest⟩ r hr
      simp only [records, List.mem_cons] at hr
      rcases hr with heq | hr
      · subst r
        cases mode <;> rfl
      · exact ih _ _ _ r hr

def requestedActionAt {n : ℕ} (rs : List (ModeRecord n)) (t : ℕ) : Action :=
  ((rs[t]?).map (fun r => r.transaction.action)).getD none

def executedModeAt {n : ℕ} (rs : List (ModeRecord n)) (t : ℕ) : Bool :=
  ((rs[t]?).map ModeRecord.repairMode).getD false

def recordedCostAt {n : ℕ} (rs : List (ModeRecord n)) (t : ℕ) : ℝ :=
  ((rs[t]?).map (fun r => r.transaction.expenditure)).getD 0

theorem recordedCostAt_eq (k : ℕ) {t : ℕ} (h : pi.Memory t)
    (o : Organism n) (w : Tape k) (j : ℕ) :
    recordedCostAt (records i m pi k h o w) j =
      if executedModeAt (records i m pi k h o w) j then
        cost m (requestedActionAt (records i m pi k h o w) j) else 0 := by
  cases hj : (records i m pi k h o w)[j]? with
  | none => simp [recordedCostAt, executedModeAt, hj]
  | some r =>
      have hr := records_expenditure i m pi k h o w r (List.mem_of_getElem? hj)
      simpa [recordedCostAt, executedModeAt, requestedActionAt, hj] using hr

/-- Source-derived P6 affordability applies to the ACTUAL paid-cost readout of
this same complete transaction record. Costs are padded by zero after its
finite horizon; the padding asserts no further physical experiment. -/
theorem actual_record_resource_viable (k : ℕ) {t : ℕ} (h : pi.Memory t)
    (o : Organism n) (w : Tape k) (initial supply : ℝ)
    (hi : 0 ≤ initial) (hs : (m.writeCost : ℝ) ≤ supply) :
    UEOT.V3.Compression.Objecthood.ResourceClosure.ResourceViable initial (fun _ => supply)
      (recordedCostAt (records i m pi k h o w)) := by
  have hcost : recordedCostAt (records i m pi k h o w) =
      (fun j => if executedModeAt (records i m pi k h o w) j then
        cost m (requestedActionAt (records i m pi k h o w) j) else 0) := by
    funext j
    exact recordedCostAt_eq i m pi k h o w j
  rw [hcost]
  exact RegisterResourceSource.action_schedule_resource_viable m
    (requestedActionAt (records i m pi k h o w)) (executedModeAt (records i m pi k h o w))
    initial supply hi hs

section Integral
local instance tapeMeasurableSpace (k : ℕ) : MeasurableSpace (Tape k) := ⊤
local instance tapeSingletonClass (k : ℕ) : MeasurableSingletonClass (Tape k) := ⟨fun _ => trivial⟩
local instance recordMeasurableSpace : MeasurableSpace (List (ModeRecord n)) := ⊤
local instance recordSingletonClass : MeasurableSingletonClass (List (ModeRecord n)) := ⟨fun _ => trivial⟩

theorem recorded_payoff_integrable (price : NNReal) (d : ℝ) (k : ℕ)
    {t : ℕ} (h : pi.Memory t) (o : Organism n) :
    Integrable (discountedPayoff price d) (recordLaw i noise m epsilon he pi k h o).toMeasure := by
  have hm : Measurable (records i m pi k h o) := measurable_of_finite _
  have hp : Measurable (discountedPayoff (n := n) price d) := by intro s hs; trivial
  rw [recordLaw, ← PMF.toMeasure_map _ _ hm]
  exact (integrable_map_measure hp.aestronglyMeasurable hm.aemeasurable).mpr Integrable.of_finite

theorem integral_recordLaw_eq_actualExpectation (price : NNReal) (d : ℝ) (k : ℕ)
    {t : ℕ} (h : pi.Memory t) (o : Organism n) :
    (∫ rs, discountedPayoff price d rs ∂(recordLaw i noise m epsilon he pi k h o).toMeasure) =
      actualExpectation i noise m epsilon he pi price d k h o := by
  have hm : Measurable (records i m pi k h o) := measurable_of_finite _
  have hp : Measurable (discountedPayoff (n := n) price d) := by intro s hs; trivial
  rw [recordLaw, ← PMF.toMeasure_map _ _ hm, integral_map hm.aemeasurable hp.aestronglyMeasurable,
    PMF.integral_eq_sum]
  rfl

/-- Actual full fault-mode record expectation for the SAME supplied policy. -/
theorem actual_record_integral_eq_policy_value (price : NNReal) (d : ℝ)
    (hd : 0 < d ∧ d < 1) (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n)
    (hx : o.physical = pi.current h) (hp : o.program = m.goal) :
    (∫ rs, discountedPayoff price d rs ∂(recordLaw i noise m epsilon he pi k h o).toMeasure) =
      pi.truncatedValue (RegisterFaultControlModel.model i noise m price epsilon he d hd) k h := by
  rw [integral_recordLaw_eq_actualExpectation,
    actualExpectation_eq_truncatedValue i noise m epsilon he pi price d hd k h o hx hp]

/-- Literal records of the concrete compiled program realize its original
causal-control optimum in the discounted limit under this SAME fault law. -/
theorem compiled_record_integral_tendsto_optimal (price : NNReal) (d : ℝ)
    (hd : 0 < d ∧ d < 1) (hc : (price : ℝ) * m.writeCost ≤ 1)
    (o : Organism n) (hp : o.program = m.goal) :
    let sigma := selectorPolicy ((substrate i).execute m.goal)
    let M := RegisterFaultControlModel.model i noise m price epsilon he d hd
    Filter.Tendsto (fun k => ∫ rs, discountedPayoff price d rs ∂
      (recordLaw i noise m epsilon he sigma k (t := 0) o.physical o).toMeasure)
      Filter.atTop (nhds (M.optimalValue o.physical)) := by
  dsimp only
  have hlim := CausalPolicy.truncatedValue_tendsto_infiniteValue
    (selectorPolicy ((substrate i).execute m.goal))
    (RegisterFaultControlModel.model i noise m price epsilon he d hd) (t := 0) o.physical
  have hopt := (compiled_optimal_against_all_causal.{0} i noise m price epsilon he d hd hc).1
    (t := 0) o.physical
  rw [hopt] at hlim
  apply hlim.congr'
  exact Filter.Eventually.of_forall fun k =>
    (actual_record_integral_eq_policy_value i noise m epsilon he
      (selectorPolicy ((substrate i).execute m.goal)) price d hd k (t := 0) o.physical o rfl hp).symm

end Integral

section Maintenance
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open UEOT.V3.ViabilityKernel
open RegisterFaultSource
variable [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/-- The literal successful child, without replacing it by a valid seed,
enters the SAME source-derived P5 maintenance family. Failed births remain None
in the original law; this conditional implication performs no filtering/retry. -/
theorem actual_mode_birth_enters_maintenance (o child : Organism n) (a : Action)
    (mode label : Bool) (hp : o.program = m.goal)
    (hc : (modeRecordStep i m o a mode label).transaction.child = some child) :
    let seed : OntogeneticSeed (State n) Bool := ⟨child.physical, child.program⟩
    let S := finiteJointRecurrentHomeostasisSystem
      (physical i) (target i m.goal) (target_fixed i m.goal) (certificate i m.goal)
      (substrate i) codec m.goal (compiled_dynamics_implements i m.goal)
      (fault i) epsilon he (actual_fault_envelope i m.goal)
    StaysIn (PMF.pure (assembleRepairOrganization (substrate i) codec seed)) S.carrier := by
  have hx := actual_child_requires_repair i m o child a mode label hc
  exact RegisterBirthMaintenance.actual_birth_enters_maintenance i m o child a label hp hx.2 epsilon he

end Maintenance

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultJointRecord
