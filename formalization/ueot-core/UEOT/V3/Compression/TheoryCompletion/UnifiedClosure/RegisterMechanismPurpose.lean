import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRepairHistory
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C6PurposeMechanism
import UEOT.V3.FiniteDiscountedGreedy
import UEOT.V3.FiniteDiscountedSelector

/-! # Registered reproductive evaluation from the register mechanism
The evaluation contract counts living births minus a registered price times
literal write cost. A living birth requires the actual post-action register to
meet its inherited program target. Cost and target are mechanism parameters;
the price and discount are independent, fixed evaluation choices. Exact probe
laws below are mathematical observations, not finite-data estimation claims.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismPurpose
open Set MeasureTheory
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open UEOT.V3.FiniteDiscountedControl
open RegisterRepairSource RegisterRepairHistory
open scoped BigOperators
noncomputable section

structure Mechanism where
  goal : Bool
  writeCost : NNReal

def cost (m : Mechanism) : Action → ℝ
  | none => 0
  | some _ => m.writeCost

/-- A child is actually produced only after a physically successful action.
The birth itself uses the same interpreter and literal program-copy event. -/
def outcome {n : ℕ} (i : Fin n) (m : Mechanism) (x : State n) (a : Action)
    (label : Bool) : Option (Organism n) :=
  if update i x a i = m.goal then
    some (birthEvent i label ⟨[], update i x a, m.goal⟩)
  else none

def childCount {n : ℕ} : Option (Organism n) → ℝ
  | none => 0
  | some _ => 1

def expectedChildren {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (m : Mechanism) (x : State n) (a : Action) : ℝ :=
  ∑ label, (noise label).toReal * childCount (outcome i m x a label)

/-- The reproduction mean is derived from the actual source, not supplied as
an arbitrary numerical objective. -/
theorem expectedChildren_eq {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (m : Mechanism) (x : State n) (a : Action) :
    expectedChildren i noise m x a = if update i x a i = m.goal then 1 else 0 := by
  classical
  have hs : ∑ label, (noise label).toReal = 1 := by
    have h := congrArg ENNReal.toReal (PMF.tsum_coe noise)
    rw [tsum_fintype, ENNReal.toReal_sum (fun label _ => PMF.apply_ne_top _ label)] at h
    simpa using h
  by_cases h : update i x a i = m.goal
  · simpa only [expectedChildren, outcome, if_pos h, childCount, mul_one] using hs
  · simp [expectedChildren, outcome, childCount, h]

/-- Literal one-step registered payoff. The price is not inferred from physics. -/
def stage {n : ℕ} (i : Fin n) (noise : PMF Bool) (price : NNReal)
    (m : Mechanism) (x : State n) (a : Action) : ℝ :=
  expectedChildren i noise m x a - (price : ℝ) * cost m a

/-- The finite control model is built from actual physical rows and the
registered outcome accounting. It has no free reward field. -/
def model {n : ℕ} (i : Fin n) (noise : PMF Bool) (price : NNReal)
    (discount : ℝ) (hd : 0 < discount ∧ discount < 1) (m : Mechanism) :
    Model (State n) (fun _ => Action) := by
  classical
  exact {
    transition := fun x a y => if update i x a = y then 1 else 0
    reward := stage i noise price m
    rewardBound := 1 + (price : ℝ) * (m.writeCost : ℝ)
    discount := discount
    transition_nonneg := by intros; split_ifs <;> norm_num
    transition_sum_one := by intro x a; simp
    reward_abs_le := by
      intro x a
      rw [stage, expectedChildren_eq]
      have hp := price.coe_nonneg
      have hc := m.writeCost.coe_nonneg
      cases a <;> simp only [cost] <;> split_ifs <;> rw [abs_le] <;> constructor <;> nlinarith
    discount_pos := hd.1
    discount_lt_one := hd.2 }

/-- The model row is the original allowed-action physical PMF, pointwise. -/
theorem model_transition_eq_physical {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) (m : Mechanism)
    (x : State n) (a : Action) (y : State n) :
    (model i noise price d hd m).transition x a y = (physical i x a y).toReal := by
  classical
  simp only [model, physical, PMF.pure_apply]
  split_ifs <;> simp_all

/-- Expected continuation is the actual deterministic physical successor. -/
theorem model_expect_eq_update {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) (m : Mechanism)
    (v : State n → ℝ) (x : State n) (a : Action) :
    (model i noise price d hd m).expect x a v = v (update i x a) := by
  classical
  simp [Model.expect, model]

/-- Actual causal deployment includes its own initial memory state. -/
abbrev Deployment (n : ℕ) := Σ pi : CausalPolicy.{0,0,0} (State n) (fun _ => Action), pi.Memory 0

def objective {n : ℕ} (i : Fin n) (noise : PMF Bool) (price : NNReal)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (T : ℕ) (m : Mechanism) :
    NumericalObjective (Deployment n) :=
  fun run => run.1.truncatedValue (model i noise price d hd m) T run.2

/-- Allowed probes: write false, count births; write true, count births; measure
literal write expenditure. No selector/purpose answer is an observation field. -/
def observe {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) : ℝ × ℝ × ℝ :=
  (expectedChildren i noise m (fun _ => false) (some false),
   expectedChildren i noise m (fun _ => false) (some true), cost m (some false))

theorem observe_injective {n : ℕ} (i : Fin n) (noise : PMF Bool) :
    Function.Injective (observe i noise) := by
  intro m k h
  have hgoal : m.goal = k.goal := by
    have hf := congrArg Prod.fst h
    simp only [observe, expectedChildren_eq, update] at hf
    cases hm : m.goal <;> cases hk : k.goal <;> simp_all
  have hc : m.writeCost = k.writeCost := by
    have hw := congrArg (fun r : ℝ × ℝ × ℝ => r.2.2) h
    exact NNReal.coe_injective hw
  cases m
  cases k
  simp_all

/-- C6's faithfulness premise is proved for this mechanism/experiment class. -/
theorem registered_mechanism_faithful {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) (T : ℕ) :
    MechanismTeleologicalFaithfulness (observe i noise) (objective i noise price d hd T) := by
  intro m k h
  have he := observe_injective i noise h
  subst k
  intro p q
  rfl

/-- Actual downstream teleological-class consumer, with no `hfaith` input. -/
theorem registered_observation_identifies_purpose {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) (T : ℕ)
    (m k : Mechanism) (h : observe i noise m = observe i noise k) :
    TeleologicalObjectiveClass (objective i noise price d hd T m) =
      TeleologicalObjectiveClass (objective i noise price d hd T k) :=
  mechanismObservation_identifies_teleologicalClass (observe i noise)
    (objective i noise price d hd T) (registered_mechanism_faithful i noise price d hd T) h

/-- Bellman uses the same actual child-count/cost payoff and physical update. -/
theorem registered_greedy_equation {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) (m : Mechanism) (x : State n) :
    let M := model i noise price d hd m
    stage i noise price m x (M.greedyAction x) +
      d * M.optimalValue (update i x (M.greedyAction x)) = M.optimalValue x := by
  dsimp only
  have h := (model i noise price d hd m).greedyAction_spec x
  simp only [Model.qValue, model_expect_eq_update] at h
  exact h

/-- The same source model supplies the original full causal-control consumer. -/
theorem registered_causal_optimality {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) (m : Mechanism) :
    let M := model i noise price d hd m
    (∀ (pi : CausalPolicy (State n) (fun _ => Action)) {t : ℕ} (h : pi.Memory t),
      pi.infiniteValue M h ≤ M.optimalValue (pi.current h)) ∧
    (∀ {t : ℕ} (x : State n),
      (greedyPolicy M).infiniteValue M (t := t) x = M.optimalValue x) :=
  p_ctl_01_causal_optimality (model i noise price d hd m)

def constantRun {n : ℕ} (a : Action) (x : State n) : Deployment n :=
  ⟨selectorPolicy (fun _ => a), x⟩

@[simp] theorem one_step_constant {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) (m : Mechanism)
    (a : Action) (x : State n) :
    objective i noise price d hd 1 m (constantRun a x) = stage i noise price m x a := by
  change (selectorPolicy (fun _ : State n => a)).truncatedValue
    (model i noise price d hd m) 1 x = _
  rw [selector_truncatedValue_succ]
  change stage i noise price m x a + d *
    (∑ y, (model i noise price d hd m).transition x a y * (0 : ℝ)) = _
  simp

/-- Raw physical transitions and cost readings omit the living-birth feedback.
Two actual inherited target programs then give opposite policy rankings. -/
theorem physical_cost_observations_insufficient (noise : PMF Bool) :
    let m : Mechanism := ⟨false, 1⟩
    let k : Mechanism := ⟨true, 1⟩
    (physical (0 : Fin 1), cost m) = (physical 0, cost k) ∧
    ¬ PolicyOrderingEquivalent
      (objective (0 : Fin 1) noise 0 (1/2) (by norm_num) 1 m)
      (objective (0 : Fin 1) noise 0 (1/2) (by norm_num) 1 k) := by
  dsimp only
  refine ⟨rfl, ?_⟩
  intro h
  have hc := h (constantRun (some true) (fun _ => false))
    (constantRun none (fun _ => false))
  simp only [InducedPreference, one_step_constant, stage, expectedChildren_eq] at hc
  norm_num [update, cost] at hc

/-- A proper target and an actual outside-to-target write coexist with a
strictly positive nonconstant write cost. -/
theorem nonconstant_cost_witness :
    let m : Mechanism := ⟨true, 1⟩
    cost m none = 0 ∧ cost m (some true) = 1 ∧
      (∃ x : State 1, x ∉ target 0 m.goal ∧
        update 0 x (some true) ∈ target 0 m.goal) := by
  refine ⟨rfl, rfl, fun _ => false, ?_, ?_⟩ <;> simp [target, update]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismPurpose
