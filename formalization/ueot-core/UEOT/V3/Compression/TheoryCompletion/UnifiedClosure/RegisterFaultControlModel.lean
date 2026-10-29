import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultControlSource
import UEOT.V3.FiniteDiscountedApproxQuotient

/-! Registered control on the SAME environmental-fault physical source as P5.
The mode is sampled before the action is executed: repair mode executes that
allowed action and its birth/cost outcome; fault mode damages the retained
target, produces no birth and charges no controlled-action write. This is a
new source objective; the old fault-free path expectation is not transported.
Priced-write cost at most one is a sufficient regime, not a necessity claim.
At hazard one the control objective is zero; no homeostasis is inferred.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultControlModel
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.Objecthood UEOT.V3.Compression.Objecthood.JointHomeostasis
open RegisterRepairSource RegisterMechanismPurpose RegisterFaultControlSource
open scoped BigOperators ENNReal
noncomputable section

def repairChance (epsilon : NNReal) : ℝ := 1 - (epsilon : ℝ)

def modeProbability (epsilon : NNReal) (mode : Bool) : ℝ :=
  if mode then repairChance epsilon else (epsilon : ℝ)

def modeLaw (epsilon : NNReal) (he : epsilon ≤ 1) : PMF Bool :=
  FiniteProbabilityRow.ofRealRow (modeProbability epsilon)
    (by intro mode; cases mode <;> simp [modeProbability, repairChance]; exact_mod_cast he)
    (by simp [modeProbability, repairChance])

/-- An actual mode outcome, counting births only in controlled-execution mode. -/
def modePayoff {n : ℕ} (i : Fin n) (m : Mechanism) (price : NNReal)
    (x : State n) (a : Action) (mode label : Bool) : ℝ :=
  if mode then childCount (outcome i m x a label) - (price : ℝ) * cost m a else 0

def expectedModePayoff {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon ≤ 1) (x : State n) (a : Action) : ℝ :=
  ∑ mode, ∑ label, (modeLaw epsilon he mode).toReal * (noise label).toReal *
    modePayoff i m price x a mode label

/-- Source mode/label expectation is derived rather than provided as reward. -/
theorem expectedModePayoff_eq {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon ≤ 1) (x : State n) (a : Action) :
    expectedModePayoff i noise m price epsilon he x a =
      repairChance epsilon * stage i noise price m x a := by
  have hn : ∑ label, (noise label).toReal = 1 := by
    have h := congrArg ENNReal.toReal (PMF.tsum_coe noise)
    rw [tsum_fintype, ENNReal.toReal_sum (fun label _ => PMF.apply_ne_top _ label)] at h
    simpa using h
  have hn' : (noise true).toReal + (noise false).toReal = 1 := by simpa using hn
  simp only [expectedModePayoff, modeLaw, FiniteProbabilityRow.ofRealRow_apply_toReal]
  simp [modeProbability, modePayoff, stage, expectedChildren, mul_sub,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hn', mul_assoc]

/-- Actual physical transition in each mode. -/
def modeNext {n : ℕ} (i : Fin n) (m : Mechanism) (x : State n) (a : Action) (mode : Bool) : State n :=
  if mode then update i x a else Function.update x i (!m.goal)

def model {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon ≤ 1) (d : ℝ) (hd : 0 < d ∧ d < 1) :
    Model (State n) (fun _ => Action) := by
  classical
  have he' : (epsilon : ℝ) ≤ 1 := by exact_mod_cast he
  have hr : 0 ≤ repairChance epsilon := sub_nonneg.mpr he'
  have hr1 : repairChance epsilon ≤ 1 := by simp [repairChance]
  exact {
    transition := fun x a y => repairChance epsilon * (if update i x a = y then 1 else 0) +
      (epsilon : ℝ) * (if Function.update x i (!m.goal) = y then 1 else 0)
    reward := expectedModePayoff i noise m price epsilon he
    rewardBound := 1 + (price : ℝ) * m.writeCost
    discount := d
    transition_nonneg := by intros; positivity
    transition_sum_one := by intro x a; simp [Finset.sum_add_distrib, repairChance]
    reward_abs_le := by
      intro x a
      rw [expectedModePayoff_eq, abs_mul, abs_of_nonneg hr]
      have hb : 0 ≤ 1 + (price : ℝ) * m.writeCost := by positivity
      have hh := (RegisterMechanismPurpose.model i noise price d hd m).reward_abs_le x a
      change |stage i noise price m x a| ≤ 1 + (price : ℝ) * m.writeCost at hh
      exact (mul_le_mul_of_nonneg_left hh hr).trans (mul_le_of_le_one_left hb hr1)
    discount_pos := hd.1
    discount_lt_one := hd.2 }

/-- The new control model uses exactly the P5 controlled physical source. -/
theorem model_transition_eq_physicalSource {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (m : Mechanism) (price epsilon : NNReal) (he : epsilon ≤ 1)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (x : State n) (a : Action) (y : State n) :
    (model i noise m price epsilon he d hd).transition x a y =
      (physicalSource i m epsilon he x a y).toReal := by
  classical
  have he' : (epsilon : ℝ) ≤ 1 := by exact_mod_cast he
  change repairChance epsilon * (if update i x a = y then 1 else 0) +
    (epsilon : ℝ) * (if Function.update x i (!m.goal) = y then 1 else 0) = _
  rw [physicalSource, recurrentFaultMix_apply,
    ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (PMF.apply_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (PMF.apply_ne_top _ _)), ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [ENNReal.coe_toReal, NNReal.coe_sub he, NNReal.coe_one]
  have hp : (physical i x a y).toReal = (if update i x a = y then 1 else 0) :=
    (RegisterMechanismPurpose.model_transition_eq_physical i noise price d hd m x a y).symm
  have hf : (PMF.pure (Function.update x i (!m.goal)) y).toReal =
      (if Function.update x i (!m.goal) = y then 1 else 0) := by
    exact (RegisterMechanismPurpose.model_transition_eq_physical i noise price d hd m
        (Function.update x i (!m.goal)) none y).symm
  rw [hp, hf]
  rfl

/-- PMF-level identity, retaining actual full physical rows. -/
theorem model_row_eq_physicalSource {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (m : Mechanism) (price epsilon : NNReal) (he : epsilon ≤ 1)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (x : State n) (a : Action) :
    (model i noise m price epsilon he d hd).transitionPMF x a =
      physicalSource i m epsilon he x a := by
  apply PMF.ext
  intro y
  rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top ((model i noise m price epsilon he d hd).transitionPMF x a) y),
    ← ENNReal.ofReal_toReal (PMF.apply_ne_top (physicalSource i m epsilon he x a) y)]
  rw [Model.transitionPMF_apply_toReal, model_transition_eq_physicalSource]

/-- The declared primitive mode draw realizes the SAME physical P5 shadow.
Thus the reward and physical mixture use one common environmental mode law. -/
theorem modeLaw_next_eq_physicalSource {n : ℕ} (i : Fin n) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (x : State n) (a : Action) :
    (modeLaw epsilon he).map (modeNext i m x a) = physicalSource i m epsilon he x a := by
  classical
  have hr : ENNReal.ofReal (repairChance epsilon) = ((1-epsilon : NNReal) : ℝ≥0∞) := by
    have hc : ((1-epsilon : NNReal) : ℝ) = 1 - (epsilon : ℝ) := by
      simpa only [NNReal.coe_one] using NNReal.coe_sub he
    rw [repairChance, ← hc]
    simp
  apply PMF.ext
  intro y
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp [modeLaw, FiniteProbabilityRow.ofRealRow, modeProbability, modeNext,
    physicalSource, recurrentFaultMix_apply, physical, PMF.pure_apply, hr]

theorem model_expect_source {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (m : Mechanism) (price epsilon : NNReal) (he : epsilon ≤ 1)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (v : State n → ℝ) (x : State n) (a : Action) :
    (model i noise m price epsilon he d hd).expect x a v =
      repairChance epsilon * v (update i x a) +
        (epsilon : ℝ) * v (Function.update x i (!m.goal)) := by
  classical
  simp [Model.expect, model, add_mul, Finset.sum_add_distrib]

def goodValue (m : Mechanism) (price epsilon : NNReal) (d : ℝ) : ℝ :=
  repairChance epsilon * (1 - d * (epsilon : ℝ) * ((price : ℝ) * m.writeCost)) / (1-d)

def badValue (m : Mechanism) (price epsilon : NNReal) (d : ℝ) : ℝ :=
  goodValue m price epsilon d - repairChance epsilon * ((price : ℝ) * m.writeCost)

def value {n : ℕ} (i : Fin n) (m : Mechanism) (price epsilon : NNReal) (d : ℝ) (x : State n) : ℝ :=
  if x i = m.goal then goodValue m price epsilon d else badValue m price epsilon d

private theorem balance (m : Mechanism) (price epsilon : NNReal) (d : ℝ)
    (hd : 0 < d ∧ d < 1) :
    goodValue m price epsilon d = repairChance epsilon +
      d * (repairChance epsilon * goodValue m price epsilon d +
        (epsilon : ℝ) * badValue m price epsilon d) := by
  simp only [badValue, goodValue, repairChance]
  field_simp [ne_of_gt (sub_pos.mpr hd.2)]
  ring

private theorem badValue_nonneg (m : Mechanism) (price epsilon : NNReal) (he : epsilon ≤ 1)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (hc : (price : ℝ) * m.writeCost ≤ 1) :
    0 ≤ badValue m price epsilon d := by
  have hr : 0 ≤ repairChance epsilon := by unfold repairChance; exact sub_nonneg.mpr (by exact_mod_cast he)
  have hq : 0 ≤ (price : ℝ) * m.writeCost := mul_nonneg price.coe_nonneg m.writeCost.coe_nonneg
  have hb : badValue m price epsilon d =
      repairChance epsilon * ((1 - (price : ℝ) * m.writeCost) +
        d * repairChance epsilon * ((price : ℝ) * m.writeCost)) / (1-d) := by
    simp only [badValue, goodValue, repairChance]
    field_simp [ne_of_gt (sub_pos.mpr hd.2)]
    ring
  rw [hb]
  exact div_nonneg (mul_nonneg hr (add_nonneg (sub_nonneg.mpr hc) (mul_nonneg (mul_nonneg hd.1.le hr) hq))) (by linarith)

theorem qValue_source {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon ≤ 1) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (v : State n → ℝ) (x : State n) (a : Action) :
    (model i noise m price epsilon he d hd).qValue v x a =
      repairChance epsilon * ((if update i x a i = m.goal then 1 else 0) - (price : ℝ) * cost m a) +
        d * (repairChance epsilon * v (update i x a) + (epsilon : ℝ) * v (Function.update x i (!m.goal))) := by
  rw [Model.qValue, model_expect_source]
  change expectedModePayoff i noise m price epsilon he x a + _ = _
  rw [expectedModePayoff_eq, stage, expectedChildren_eq]
  rfl

/-- Every allowed action is dominated by the analytic value in the stated
priced-write regime. No action is added to evade the environmental hazard. -/
theorem value_action_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon ≤ 1) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (hc : (price : ℝ) * m.writeCost ≤ 1) (x : State n) (a : Action) :
    (model i noise m price epsilon he d hd).qValue (value i m price epsilon d) x a ≤
      value i m price epsilon d x := by
  have hr : 0 ≤ repairChance epsilon := by unfold repairChance; exact sub_nonneg.mpr (by exact_mod_cast he)
  have hq : 0 ≤ (price : ℝ) * m.writeCost := mul_nonneg price.coe_nonneg m.writeCost.coe_nonneg
  have hgap : badValue m price epsilon d = goodValue m price epsilon d -
      repairChance epsilon * ((price : ℝ) * m.writeCost) := rfl
  have hb := badValue_nonneg m price epsilon he d hd hc
  have hbal := balance m price epsilon d hd
  have heq : repairChance epsilon + (epsilon : ℝ) = 1 := by simp [repairChance]
  have hbad : d * badValue m price epsilon d ≤ badValue m price epsilon d :=
    mul_le_of_le_one_left hb hd.2.le
  rw [qValue_source]
  cases a with
  | none =>
      by_cases hx : x i = m.goal <;> simp [value, update, cost, hx] <;> nlinarith
  | some b =>
      by_cases hb' : b = m.goal <;> by_cases hx : x i = m.goal <;>
        simp [value, update, cost, hb', hx] <;> nlinarith [mul_nonneg hr hq]

/-- The SAME interpreted program attains the noisy-source Bellman bound. -/
theorem compiled_attains_value {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon ≤ 1) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (x : State n) :
    (model i noise m price epsilon he d hd).qValue (value i m price epsilon d) x
      ((substrate i).execute m.goal x) = value i m price epsilon d x := by
  have hbal := balance m price epsilon d hd
  have hgap : badValue m price epsilon d = goodValue m price epsilon d -
      repairChance epsilon * ((price : ℝ) * m.writeCost) := rfl
  rw [qValue_source, execute_compiled]
  by_cases hx : x i = m.goal <;> simp [value, update, cost, hx] <;> nlinarith

theorem value_eq_optimal {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon ≤ 1) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (hc : (price : ℝ) * m.writeCost ≤ 1) :
    value i m price epsilon d = (model i noise m price epsilon he d hd).optimalValue := by
  apply Model.fixedPoint_unique
  funext x
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    exact value_action_bound i noise m price epsilon he d hd hc x a
  · rw [← compiled_attains_value i noise m price epsilon he d hd x]
    exact Finset.le_sup' (fun a => (model i noise m price epsilon he d hd).qValue
      (value i m price epsilon d) x a) (Finset.mem_univ _)

/-- Original causal selector consumer applied to the literal program under
this same P5-hazard law, not the previous fault-free objective. -/
theorem compiled_optimal_against_all_causal {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (m : Mechanism) (price epsilon : NNReal) (he : epsilon ≤ 1)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (hc : (price : ℝ) * m.writeCost ≤ 1) :
    let M := model i noise m price epsilon he d hd
    (∀ {t : ℕ} (x : State n),
      (selectorPolicy ((substrate i).execute m.goal)).infiniteValue M (t := t) x = M.optimalValue x) ∧
    (∀ (pi : CausalPolicy (State n) (fun _ => Action)) {t : ℕ} (h : pi.Memory t),
      pi.infiniteValue M h ≤ M.optimalValue (pi.current h)) := by
  apply selector_optimal_against_all_causal
  intro x
  rw [← value_eq_optimal i noise m price epsilon he d hd hc]
  exact compiled_attains_value i noise m price epsilon he d hd x

/-- Explicit positive-noise values for the same two distinct physical states.
The birth-label law is arbitrary and does not enter the selector as an oracle. -/
theorem positive_noise_values (noise : PMF Bool) :
    let m : Mechanism := ⟨true,1⟩
    let M := model (0 : Fin 1) noise m (1/2) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1))
      (1/2) (by norm_num)
    M.optimalValue (fun _ => true) = 45/32 ∧
      M.optimalValue (fun _ => false) = 33/32 := by
  dsimp only
  have hv := value_eq_optimal (0 : Fin 1) noise (⟨true,1⟩ : Mechanism)
    (1/2) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)) (1/2) (by norm_num) (by norm_num)
  rw [← hv]
  norm_num [value, goodValue, badValue, repairChance]

section ActualP5
open MeasureTheory
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open RegisterFaultSource
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/-- The actual P5 shadow theorem is consumed at the PMF level for this SAME
compiled program and this SAME environmental hazard. -/
theorem actual_P5_row_eq_control_row (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon ≤ 1) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (s : RepairOrganizationState (State n) Action Bool)
    (hs : s ∈ finiteJointRepairCarrier (physical i) (target i m.goal) (certificate i m.goal)
      (substrate i) codec m.goal) :
    let S := finiteJointRecurrentHomeostasisSystem
      (physical i) (target i m.goal) (target_fixed i m.goal) (certificate i m.goal)
      (substrate i) codec m.goal (compiled_dynamics_implements i m.goal)
      (fault i) epsilon he (actual_fault_envelope i m.goal)
    (S.mixedKernel s).map (fun z => z.physical) =
      (model i noise m price epsilon he d hd).transitionPMF s.physical
        ((substrate i).execute m.goal s.physical) := by
  rw [model_row_eq_physicalSource]
  exact actual_P5_physical_shadow i m epsilon he s hs

end ActualP5

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultControlModel
