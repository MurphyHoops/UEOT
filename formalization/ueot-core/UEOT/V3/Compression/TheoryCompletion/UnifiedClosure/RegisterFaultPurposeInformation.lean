import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultJointRecord
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C6PurposeMechanism

/-! C6 identification from actual birth and paid-cost probe experiments when
execution hazard is UNKNOWN. Three exact means belong to declared experiment
permissions, not to a finite-data confidence certificate. Neither parameters nor
purpose answers are observations, and policy execution receives no hazard oracle.
Price, discount, horizon and founder history are fixed evaluation choices.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultPurposeInformation
open MeasureTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterJointRecord RegisterFaultControlModel RegisterFaultJointRecord
open scoped BigOperators ENNReal
noncomputable section

structure Parameter where
  mechanism : Mechanism
  epsilon : NNReal
  epsilon_lt_one : epsilon < 1

/-- Source hazard positivity follows from the declared non-total-fault family. -/
theorem repairChance_pos (theta : Parameter) : 0 < repairChance theta.epsilon := by
  unfold repairChance
  exact sub_pos.mpr (by exact_mod_cast theta.epsilon_lt_one)

/-- Actual source experiment: request a write and read the living-birth count.
The probe's parent carries the unknown source program; its answer is not passed
to the policy. Mode and label use the same laws as actual deployment. -/
def probeBirthMean {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (theta : Parameter) (bit : Bool) : ℝ :=
  ∑ mode, ∑ label,
    (modeLaw theta.epsilon theta.epsilon_lt_one.le mode).toReal * (noise label).toReal *
      childCount (modeRecordStep i theta.mechanism
        ⟨[], fun _ => false, theta.mechanism.goal⟩ (some bit) mode label).transaction.child

/-- Actual paid expenditure of the same write-false experiment. Faults preempt
execution and have zero controlled charge, as in the common record source. -/
def probePaidMean {n : ℕ} (i : Fin n) (noise : PMF Bool) (theta : Parameter) : ℝ :=
  ∑ mode, ∑ label,
    (modeLaw theta.epsilon theta.epsilon_lt_one.le mode).toReal * (noise label).toReal *
      (modeRecordStep i theta.mechanism
        ⟨[], fun _ => false, theta.mechanism.goal⟩ (some false) mode label).transaction.expenditure

private theorem noise_sum (noise : PMF Bool) :
    (noise true).toReal + (noise false).toReal = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe noise)
  rw [tsum_fintype, ENNReal.toReal_sum (fun b _ => PMF.apply_ne_top _ b)] at h
  simpa using h

/-- Probe formulas are derived from mode execution and literal birth records. -/
theorem probeBirthMean_eq {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (theta : Parameter) (bit : Bool) :
    probeBirthMean i noise theta bit =
      repairChance theta.epsilon * (if bit = theta.mechanism.goal then 1 else 0) := by
  have hn := noise_sum noise
  by_cases hb : bit = theta.mechanism.goal <;>
    simp [probeBirthMean, modeLaw, FiniteProbabilityRow.ofRealRow_apply_toReal,
      modeProbability, modeRecordStep, recordStep, childCount, update, hb,
      ← mul_add, hn, mul_assoc]

theorem probePaidMean_eq {n : ℕ} (i : Fin n) (noise : PMF Bool) (theta : Parameter) :
    probePaidMean i noise theta = repairChance theta.epsilon * (theta.mechanism.writeCost : ℝ) := by
  have hn := noise_sum noise
  simp [probePaidMean, modeLaw, FiniteProbabilityRow.ofRealRow_apply_toReal,
    modeProbability, modeRecordStep, recordStep, cost, ← add_mul, ← mul_add, hn, mul_assoc]

/-- The write probes require no extra initial-state preparation: the same
means hold at any physical/history state with this actual inherited program. -/
theorem probe_means_from_actual_parent {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (theta : Parameter) (o : Organism n) (hp : o.program = theta.mechanism.goal) (bit : Bool) :
    (∑ mode, ∑ label,
      (modeLaw theta.epsilon theta.epsilon_lt_one.le mode).toReal * (noise label).toReal *
        childCount (modeRecordStep i theta.mechanism o (some bit) mode label).transaction.child) =
      probeBirthMean i noise theta bit ∧
    (∑ mode, ∑ label,
      (modeLaw theta.epsilon theta.epsilon_lt_one.le mode).toReal * (noise label).toReal *
        (modeRecordStep i theta.mechanism o (some false) mode label).transaction.expenditure) =
      probePaidMean i noise theta := by
  constructor
  · unfold probeBirthMean
    apply Finset.sum_congr rfl
    intro mode _
    apply Finset.sum_congr rfl
    intro label _
    congr 1
    cases mode <;> by_cases hb : bit = theta.mechanism.goal <;>
      simp [modeRecordStep, recordStep, childCount, update, hp, hb]
  · unfold probePaidMean
    apply Finset.sum_congr rfl
    intro mode _
    apply Finset.sum_congr rfl
    intro label _
    cases mode <;> rfl

/-- Only three actual experiment means, not the hidden parameter tuple. -/
def observe {n : ℕ} (i : Fin n) (noise : PMF Bool) (theta : Parameter) : ℝ × ℝ × ℝ :=
  (probeBirthMean i noise theta false, probeBirthMean i noise theta true, probePaidMean i noise theta)

theorem observed_birth_sum {n : ℕ} (i : Fin n) (noise : PMF Bool) (theta : Parameter) :
    (observe i noise theta).1 + (observe i noise theta).2.1 = repairChance theta.epsilon := by
  cases hg : theta.mechanism.goal <;> simp [observe, probeBirthMean_eq, hg]

/-- Unknown hazard, inherited target and write unit are all identified by the
actual probe laws on this non-total-fault source family. -/
theorem observe_injective {n : ℕ} (i : Fin n) (noise : PMF Bool) :
    Function.Injective (observe i noise) := by
  intro theta kappa h
  have hr : repairChance theta.epsilon = repairChance kappa.epsilon := by
    rw [← observed_birth_sum i noise theta, ← observed_birth_sum i noise kappa]
    exact congrArg (fun q : ℝ × ℝ × ℝ => q.1 + q.2.1) h
  have heps : theta.epsilon = kappa.epsilon := by
    apply NNReal.coe_injective
    unfold repairChance at hr
    linarith
  have hpos := repairChance_pos kappa
  have hg : theta.mechanism.goal = kappa.mechanism.goal := by
    have hf := congrArg Prod.fst h
    simp only [observe, probeBirthMean_eq] at hf
    rw [hr] at hf
    cases ht : theta.mechanism.goal <;> cases hk : kappa.mechanism.goal <;> simp_all
  have hc : theta.mechanism.writeCost = kappa.mechanism.writeCost := by
    have hp := congrArg (fun q : ℝ × ℝ × ℝ => q.2.2) h
    change probePaidMean i noise theta = probePaidMean i noise kappa at hp
    rw [probePaidMean_eq, probePaidMean_eq, hr] at hp
    apply NNReal.coe_injective
    exact mul_left_cancel₀ (ne_of_gt hpos) hp
  rcases theta with ⟨⟨gt,ct⟩,et,het⟩
  rcases kappa with ⟨⟨gk,ck⟩,ek,hek⟩
  dsimp only at heps hg hc
  subst ek
  subst gk
  subst ck
  rfl

/-- At total environmental fault, both recorded means vanish for every
program, write unit, parent and allowed action. This case is excluded from
`Parameter`; no identification of its hidden parameters is asserted. -/
theorem total_fault_experiments_zero {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (m : Mechanism) (o : Organism n) (a : Action) :
    (∑ mode, ∑ label, (modeLaw 1 (by norm_num) mode).toReal * (noise label).toReal *
      childCount (modeRecordStep i m o a mode label).transaction.child) = 0 ∧
    (∑ mode, ∑ label, (modeLaw 1 (by norm_num) mode).toReal * (noise label).toReal *
      (modeRecordStep i m o a mode label).transaction.expenditure) = 0 := by
  simp [modeLaw, FiniteProbabilityRow.ofRealRow_apply_toReal, modeProbability,
    repairChance, modeRecordStep, recordStep, childCount]

section Objective
variable {n : ℕ}
local instance recordMeasurableSpace : MeasurableSpace (List (ModeRecord n)) := ⊤
local instance recordSingletonClass : MeasurableSingletonClass (List (ModeRecord n)) := ⟨fun _ => trivial⟩

/-- The actual full mode-aware record expectation, for the SAME deployed
causal policy/initial memory; failed births and faults are not filtered. -/
def objective (i : Fin n) (noise : PMF Bool) (history : List Bool) (price : NNReal)
    (d : ℝ) (T : ℕ) (theta : Parameter) : NumericalObjective (Deployment n) :=
  fun run => ∫ rs, RegisterFaultJointRecord.discountedPayoff price d rs ∂
    (RegisterFaultJointRecord.recordLaw i noise theta.mechanism theta.epsilon theta.epsilon_lt_one.le
      run.1 T run.2 ⟨history, run.1.current run.2, theta.mechanism.goal⟩).toMeasure

/-- Existing actual record-law theorem is genuinely consumed. -/
theorem objective_eq_actual_policy_value (i : Fin n) (noise : PMF Bool) (history : List Bool)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) (T : ℕ) (theta : Parameter) (run : Deployment n) :
    objective i noise history price d T theta run =
      run.1.truncatedValue (RegisterFaultControlModel.model i noise theta.mechanism price
        theta.epsilon theta.epsilon_lt_one.le d hd) T run.2 := by
  exact actual_record_integral_eq_policy_value i noise theta.mechanism theta.epsilon theta.epsilon_lt_one.le
    run.1 price d hd T run.2 ⟨history, run.1.current run.2, theta.mechanism.goal⟩ rfl rfl

/-- A fixed one-action deployment chosen without a parameter oracle. Its
actual record expectation is derived from the same source's mode law. -/
theorem one_step_constant_value (i : Fin n) (noise : PMF Bool) (history : List Bool)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) (theta : Parameter)
    (a : Action) (x : State n) :
    objective i noise history price d 1 theta (constantRun a x) =
      repairChance theta.epsilon *
        ((if update i x a i = theta.mechanism.goal then 1 else 0) -
          (price : ℝ) * cost theta.mechanism a) := by
  rw [objective_eq_actual_policy_value i noise history price d hd]
  change (selectorPolicy (fun _ : State n => a)).truncatedValue
    (RegisterFaultControlModel.model i noise theta.mechanism price theta.epsilon theta.epsilon_lt_one.le d hd)
    1 x = _
  rw [selector_truncatedValue_succ]
  change expectedModePayoff i noise theta.mechanism price theta.epsilon theta.epsilon_lt_one.le x a +
    d * (∑ y, (RegisterFaultControlModel.model i noise theta.mechanism price theta.epsilon
      theta.epsilon_lt_one.le d hd).transition x a y * (0 : ℝ)) = _
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  rw [expectedModePayoff_eq, stage, expectedChildren_eq]

/-- Positive hazard, positive nonconstant expenditure and nonconstant actual
policy values coexist. The two literal policies contain no true-hazard input. -/
theorem positive_noise_identification_witness (noise : PMF Bool) :
    let theta : Parameter := ⟨⟨true,1⟩,1/4,
      by exact_mod_cast (by norm_num : (1/4 : ℝ) < 1)⟩
    observe (0 : Fin 1) noise theta = (0,3/4,3/4) ∧
      objective (0 : Fin 1) noise [] (1/2) (1/2) 1 theta
        (constantRun none (fun _ => false)) = 0 ∧
      objective (0 : Fin 1) noise [] (1/2) (1/2) 1 theta
        (constantRun (some true) (fun _ => false)) = 3/8 := by
  dsimp only
  rw [one_step_constant_value (0 : Fin 1) noise [] (1/2) (1/2) (by norm_num),
    one_step_constant_value (0 : Fin 1) noise [] (1/2) (1/2) (by norm_num)]
  norm_num [observe, probeBirthMean_eq, probePaidMean_eq, repairChance, update, cost]

/-- C6's faithful-order premise follows from the actual experiments, not from
an added world field asserting the desired policy ordering. -/
theorem actual_record_mechanism_faithful (i : Fin n) (noise : PMF Bool) (history : List Bool)
    (price : NNReal) (d : ℝ) (T : ℕ) :
    MechanismTeleologicalFaithfulness (observe i noise) (objective i noise history price d T) := by
  intro theta kappa h
  have heq := observe_injective i noise h
  subst kappa
  intro p q
  rfl

/-- Original C6 teleological-class endpoint applied to the actual noisy-source
complete record objective; no hfaith or true-hazard selector input is supplied. -/
theorem observed_source_identifies_actual_purpose (i : Fin n) (noise : PMF Bool)
    (history : List Bool) (price : NNReal) (d : ℝ) (T : ℕ)
    (theta kappa : Parameter) (he : observe i noise theta = observe i noise kappa) :
    TeleologicalObjectiveClass (objective i noise history price d T theta) =
      TeleologicalObjectiveClass (objective i noise history price d T kappa) :=
  mechanismObservation_identifies_teleologicalClass (observe i noise)
    (objective i noise history price d T)
    (actual_record_mechanism_faithful i noise history price d T) he

end Objective
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultPurposeInformation
