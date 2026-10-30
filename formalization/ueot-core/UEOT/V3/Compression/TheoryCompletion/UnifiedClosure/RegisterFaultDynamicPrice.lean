import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionGODScale

/-!
Original promise: purpose/control ordering must follow the same actual infinite birth-minus-priced-fee source, not a one-step comparison.
Existing result: original fault-model Bellman repair certificate assumes price*writeCost<=1; its compiled value formula and actual record adapters hold without that sufficient bound.
Reduced premise: derive the complete nonnegative-price dynamic repair/idle partition from actual Q rows, then use native fixed-point/all-causal GOD and actual-program consumers.
Model/boundary: unchanged Bool active row, Option Bool actions, mode/label law, protected program and fixed discount 0<d<1; zero repair probability, free writes and threshold ties are retained.
Consumer: actual compiled repair or literal emit-none selected by registered parameters, original BellmanGOD/all-causal optimum and the same complete-record infinite integral; no new finite-data selector, sampling or resource claim.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicPrice
open UEOT.V3.FiniteDiscountedControl
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
noncomputable section

def RepairRegion (m : Mechanism) (price epsilon : NNReal) (d : ℝ) : Prop :=
  ((price : ℝ)*m.writeCost)*(1-d*repairChance epsilon)≤1

theorem repairChance_bounds (epsilon : NNReal) (he : epsilon≤1) :
    0≤repairChance epsilon ∧ repairChance epsilon≤1 := by
  constructor
  · exact sub_nonneg.mpr (by exact_mod_cast he)
  · simp [repairChance]

theorem idle_denominator_pos (epsilon : NNReal) (he : epsilon≤1) (d : ℝ)
    (hd : 0<d ∧ d<1) : 0<1-d*repairChance epsilon := by
  have hr:=repairChance_bounds epsilon he
  nlinarith [mul_nonneg hd.1.le (sub_nonneg.mpr hr.2)]

/-- The sign deciding repair is derived by rewriting the original attained
value, not installed as a new desired Bellman Q field. -/
theorem actual_bad_value_formula (m : Mechanism) (price epsilon : NNReal)
    (d : ℝ) (hd : 0<d ∧ d<1) :
    badValue m price epsilon d=
      repairChance epsilon*(1-((price : ℝ)*m.writeCost)*(1-d*repairChance epsilon))/(1-d) := by
  simp only [badValue,goodValue,repairChance]
  field_simp [ne_of_gt (sub_pos.mpr hd.2)]
  ring

private theorem repair_balance (m : Mechanism) (price epsilon : NNReal)
    (d : ℝ) (hd : 0<d ∧ d<1) :
    goodValue m price epsilon d=repairChance epsilon+
      d*(repairChance epsilon*goodValue m price epsilon d+(epsilon : ℝ)*badValue m price epsilon d) := by
  simp only [badValue,goodValue,repairChance]
  field_simp [ne_of_gt (sub_pos.mpr hd.2)]
  ring

theorem repair_value_action_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (hc : RepairRegion m price epsilon d) (x : State n) (a : Action) :
    (model i noise m price epsilon he d hd).qValue (value i m price epsilon d) x a≤value i m price epsilon d x := by
  have hr:=(repairChance_bounds epsilon he).1
  have hq : 0≤(price : ℝ)*m.writeCost:=mul_nonneg price.coe_nonneg m.writeCost.coe_nonneg
  have hgap : badValue m price epsilon d=goodValue m price epsilon d-repairChance epsilon*((price : ℝ)*m.writeCost):=rfl
  have hb : 0≤badValue m price epsilon d := by
    rw [actual_bad_value_formula m price epsilon d hd]
    exact div_nonneg (mul_nonneg hr (sub_nonneg.mpr hc)) (sub_pos.mpr hd.2).le
  have hbal:=repair_balance m price epsilon d hd
  have heq : repairChance epsilon+(epsilon : ℝ)=1 := by simp [repairChance]
  have hbad : d*badValue m price epsilon d≤badValue m price epsilon d :=
    mul_le_of_le_one_left hb hd.2.le
  rw [qValue_source]
  cases a with
  | none => by_cases hx : x i=m.goal <;> simp [value,update,cost,hx] <;> nlinarith
  | some b =>
    by_cases hb' : b=m.goal <;> by_cases hx : x i=m.goal <;>
      simp [value,update,cost,hb',hx] <;> nlinarith [mul_nonneg hr hq]

theorem repair_value_eq_optimal {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (hc : RepairRegion m price epsilon d) :
    value i m price epsilon d=(model i noise m price epsilon he d hd).optimalValue := by
  apply Model.fixedPoint_unique
  funext x
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    exact repair_value_action_bound i noise m price epsilon he d hd hc x a
  · rw [←compiled_attains_value i noise m price epsilon he d hd x]
    exact Finset.le_sup' _ (Finset.mem_univ _)

def idleGoodValue (epsilon : NNReal) (d : ℝ) : ℝ :=repairChance epsilon/(1-d*repairChance epsilon)
def idleValue {n : ℕ} (i : Fin n) (m : Mechanism) (epsilon : NNReal) (d : ℝ) (x : State n) : ℝ :=
  if x i=m.goal then idleGoodValue epsilon d else 0

private theorem idle_balance (epsilon : NNReal) (he : epsilon≤1) (d : ℝ)
    (hd : 0<d ∧ d<1) :
    idleGoodValue epsilon d=repairChance epsilon+d*repairChance epsilon*idleGoodValue epsilon d := by
  unfold idleGoodValue
  have hden : 1-repairChance epsilon*d≠0 := by nlinarith [idle_denominator_pos epsilon he d hd]
  field_simp [hden]
  ring

theorem idle_attains_value {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (x : State n) :
    (model i noise m price epsilon he d hd).qValue (idleValue i m epsilon d) x none=idleValue i m epsilon d x := by
  have hbal:=idle_balance epsilon he d hd
  rw [qValue_source]
  by_cases hx : x i=m.goal
  · simp [idleValue,update,cost,hx]
    nlinarith
  · simp [idleValue,update,cost,hx]

theorem idle_value_action_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (hc : 1≤((price : ℝ)*m.writeCost)*(1-d*repairChance epsilon)) (x : State n) (a : Action) :
    (model i noise m price epsilon he d hd).qValue (idleValue i m epsilon d) x a≤ idleValue i m epsilon d x := by
  have hr:=(repairChance_bounds epsilon he).1
  have hq : 0≤(price : ℝ)*m.writeCost:=mul_nonneg price.coe_nonneg m.writeCost.coe_nonneg
  have hg : 0≤ idleGoodValue epsilon d:=div_nonneg hr (idle_denominator_pos epsilon he d hd).le
  have hcost : idleGoodValue epsilon d≤repairChance epsilon*((price : ℝ)*m.writeCost) := by
    apply (div_le_iff₀ (idle_denominator_pos epsilon he d hd)).mpr
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hc)]
  have hbal:=idle_balance epsilon he d hd
  cases a with
  | none => exact (idle_attains_value i noise m price epsilon he d hd x).le
  | some b =>
    rw [qValue_source]
    by_cases hb : b=m.goal <;> by_cases hx : x i=m.goal <;>
      simp [idleValue,update,cost,hb,hx] <;> nlinarith [mul_nonneg hr hq]

theorem idle_value_eq_optimal {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (hc : 1≤((price : ℝ)*m.writeCost)*(1-d*repairChance epsilon)) :
    idleValue i m epsilon d=(model i noise m price epsilon he d hd).optimalValue := by
  apply Model.fixedPoint_unique
  funext x
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    exact idle_value_action_bound i noise m price epsilon he d hd hc x a
  · rw [←idle_attains_value i noise m price epsilon he d hd x]
    exact Finset.le_sup' _ (Finset.mem_univ _)

/-- Literal parameter-indexed program; these are NOT finite probe
observations. The old data-only selector and thresholds remain untouched. -/
def dynamicProgram {n : ℕ} (i : Fin n) (m : Mechanism) (price epsilon : NNReal) (d : ℝ) : Instruction n := by
  classical
  exact if RepairRegion m price epsilon d then compile i m.goal else .emit none

def dynamicValue {n : ℕ} (i : Fin n) (m : Mechanism) (price epsilon : NNReal) (d : ℝ) : State n→ℝ := by
  classical
  exact if RepairRegion m price epsilon d then value i m price epsilon d else idleValue i m epsilon d

theorem dynamic_value_eq_optimal {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) :
    dynamicValue i m price epsilon d=(model i noise m price epsilon he d hd).optimalValue := by
  unfold dynamicValue
  split_ifs with hc
  · exact repair_value_eq_optimal i noise m price epsilon he d hd hc
  · exact idle_value_eq_optimal i noise m price epsilon he d hd (le_of_lt (lt_of_not_ge hc))

theorem dynamic_program_god {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) :
    IsBellmanGODSelector (model i noise m price epsilon he d hd)
      (interpret (dynamicProgram i m price epsilon d)) := by
  intro x
  rw [mem_bellmanGODCorrespondence_iff]
  unfold dynamicProgram
  split_ifs with hc
  · rw [←repair_value_eq_optimal i noise m price epsilon he d hd hc]
    exact compiled_attains_value i noise m price epsilon he d hd x
  · rw [←idle_value_eq_optimal i noise m price epsilon he d hd (le_of_lt (lt_of_not_ge hc))]
    exact idle_attains_value i noise m price epsilon he d hd x

theorem dynamic_program_all_causal {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) :
    let M:=model i noise m price epsilon he d hd
    (∀{t : ℕ}(x : State n),(selectorPolicy (interpret (dynamicProgram i m price epsilon d))).infiniteValue M (t:=t) x=M.optimalValue x) ∧
    (∀(pi : CausalPolicy (State n) (fun _=>Action)){t : ℕ}(h : pi.Memory t),pi.infiniteValue M h≤M.optimalValue (pi.current h)) :=
  selector_optimal_against_all_causal _ _ (dynamic_program_god i noise m price epsilon he d hd)

/-- Actual policy evaluation for literal idle, at every nonnegative price. -/
theorem idle_own_value {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (x : State n) :
    (selectorPolicy (fun _ : State n=>none)).infiniteValue
      (model i noise m price epsilon he d hd) (t:=0) x=idleValue i m epsilon d x := by
  rw [selector_infiniteValue_eq_selectorValue]
  have hv : (model i noise m price epsilon he d hd).selectorBellman (fun _=>none)
      (idleValue i m epsilon d)=idleValue i m epsilon d := by
    funext y
    exact idle_attains_value i noise m price epsilon he d hd y
  exact (congrFun ((model i noise m price epsilon he d hd).selectorValue_unique _ hv) x).symm

theorem compiled_god_iff {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (hr : 0<repairChance epsilon) :
    IsBellmanGODSelector (model i noise m price epsilon he d hd) ((substrate i).execute m.goal) ↔
      RepairRegion m price epsilon d := by
  constructor
  · intro hg
    by_contra hc
    have hi:=selector_infiniteValue_eq_optimal (model i noise m price epsilon he d hd)
      ((substrate i).execute m.goal) hg (t:=0) (fun _=>!m.goal)
    rw [RegisterFaultFinitePurposeProbe.compiled_own_value,
      ←idle_value_eq_optimal i noise m price epsilon he d hd (le_of_lt (lt_of_not_ge hc))] at hi
    simp only [value,idleValue,Bool.not_eq_self,if_false] at hi
    have hb : badValue m price epsilon d<0 := by
      rw [actual_bad_value_formula m price epsilon d hd]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg hr (sub_neg.mpr (lt_of_not_ge hc))) (sub_pos.mpr hd.2)
    linarith
  · intro hc x
    rw [mem_bellmanGODCorrespondence_iff,←repair_value_eq_optimal i noise m price epsilon he d hd hc]
    exact compiled_attains_value i noise m price epsilon he d hd x

theorem idle_god_iff {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (hr : 0<repairChance epsilon) :
    IsBellmanGODSelector (model i noise m price epsilon he d hd) (fun _=>none) ↔
      1≤((price : ℝ)*m.writeCost)*(1-d*repairChance epsilon) := by
  constructor
  · intro hg
    by_contra hc
    have hlo : RepairRegion m price epsilon d:=(lt_of_not_ge hc).le
    have hi:=selector_infiniteValue_eq_optimal (model i noise m price epsilon he d hd)
      (fun _=>none) hg (t:=0) (fun _=>!m.goal)
    rw [idle_own_value,←repair_value_eq_optimal i noise m price epsilon he d hd hlo] at hi
    simp only [value,idleValue,Bool.not_eq_self,if_false] at hi
    have hb : 0<badValue m price epsilon d := by
      rw [actual_bad_value_formula m price epsilon d hd]
      exact div_pos (mul_pos hr (sub_pos.mpr (lt_of_not_ge hc))) (sub_pos.mpr hd.2)
    linarith
  · intro hc x
    rw [mem_bellmanGODCorrespondence_iff,←idle_value_eq_optimal i noise m price epsilon he d hd hc]
    exact idle_attains_value i noise m price epsilon he d hd x

/-- Threshold equality really admits BOTH distinct controllers, not a unique
repair conclusion. The theorem also retains the zero-repair-probability tie. -/
theorem threshold_tie {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (hc : ((price : ℝ)*m.writeCost)*(1-d*repairChance epsilon)=1) :
    IsBellmanGODSelector (model i noise m price epsilon he d hd) ((substrate i).execute m.goal) ∧
    IsBellmanGODSelector (model i noise m price epsilon he d hd) (fun _=>none) := by
  constructor
  · intro x
    rw [mem_bellmanGODCorrespondence_iff,←repair_value_eq_optimal i noise m price epsilon he d hd hc.le]
    exact compiled_attains_value i noise m price epsilon he d hd x
  · intro x
    rw [mem_bellmanGODCorrespondence_iff,←idle_value_eq_optimal i noise m price epsilon he d hd hc.ge]
    exact idle_attains_value i noise m price epsilon he d hd x

/-- At hazard one ALL allowed actions are weak GOD actions: reward is zero,
including paid-write requests that fault mode never executes. No recovery follows. -/
theorem total_fault_all_actions_god {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price : NNReal) (d : ℝ) (hd : 0<d ∧ d<1) (x : State n) (a : Action) :
    a∈BellmanGODCorrespondence (model i noise m price 1 (by norm_num) d hd) x := by
  have hz : (model i noise m price 1 (by norm_num) d hd).optimalValue=(fun _=>0) := by
    rw [←dynamic_value_eq_optimal i noise m price 1 (by norm_num) d hd]
    unfold dynamicValue
    split_ifs <;> funext y <;>
      simp [value,goodValue,badValue,idleValue,idleGoodValue,repairChance]
  rw [mem_bellmanGODCorrespondence_iff,hz,qValue_source]
  simp [repairChance]

/-- Free writes give an additional genuine tie: always writing the target is
optimal as well as the conditional compiler. Physical fees are still recorded. -/
theorem free_target_write_god {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (hc : (price : ℝ)*m.writeCost=0) :
    IsBellmanGODSelector (model i noise m price epsilon he d hd) (fun _=>some m.goal) := by
  have hlo : RepairRegion m price epsilon d:=by simp [RepairRegion,hc]
  intro x
  rw [mem_bellmanGODCorrespondence_iff,←repair_value_eq_optimal i noise m price epsilon he d hd hlo,qValue_source]
  have hbal:=repair_balance m price epsilon d hd
  have hgap : badValue m price epsilon d=goodValue m price epsilon d :=by simp [badValue,hc]
  rw [hgap] at hbal
  by_cases hx : x i=m.goal <;> simp [value,update,cost,hx,hc,hgap] <;> nlinarith

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicPrice
