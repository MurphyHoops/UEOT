import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ExecutableSupportControllerWitness
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.NoisyFiniteRiskOracle

/-!
# Known structural support, unknown progress probability

The two safe states are start and goal; `none` is an absorbing cemetery.
Both numerical sources have exactly the same declared support. The R1 program
is synthesized from that support, independently of the unknown parameter.
The statistical event will be failure to reach goal, rather than entering the
cemetery that the structural safety theorem already excludes.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace NoisyFiniteRiskOracleWitness

open MeasureTheory SupportViabilityClosure ExecutableSupportSynthesis
open NoisyFiniteRiskOracle
open UEOT.V3.PathError

abbrev State := Option Bool

def stateRank : State → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

private theorem stateRank_injective : Function.Injective stateRank := by decide

/-- An explicit computable order chooses representatives without a global
instance or classical enumeration. -/
abbrev stateOrder : LinearOrder State := LinearOrder.lift' stateRank stateRank_injective

local instance : LinearOrder State := stateOrder
local instance : DecidableEq State := stateOrder.toDecidableEq

def observe : Bool → State → State
  | true, x => x
  | false, none => none
  | false, some _ => some false

def relation : State → Unit → State → Prop
  | none, _, z => z = none
  | some false, _, z => z = some false ∨ z = some true
  | some true, _, z => z = some true

def certification (x : State) (_a : Unit) : Prop := x ≠ none

instance (x : State) (a : Unit) (z : State) : Decidable (relation x a z) := by
  cases x with
  | none => exact inferInstanceAs (Decidable (z = none))
  | some b =>
      cases b with
      | false => exact inferInstanceAs (Decidable (z = some false ∨ z = some true))
      | true => exact inferInstanceAs (Decidable (z = some true))

instance (x : State) (a : Unit) : Decidable (certification x a) :=
  inferInstanceAs (Decidable (x ≠ none))

def initialTable : Finset State := {some false}

def initialMass (x : State) : ℚ := if x = some false then 1 else 0

def actionOrder : List Unit := [()]

def program (detailed : Bool) : Program State State Unit :=
  buildProgram (observe detailed) relation certification initialTable actionOrder ()

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16384 in
private theorem input_check (detailed : Bool) :
    finiteMemoryCheck (observe detailed) relation certification initialTable = true := by
  cases detailed <;> decide

private theorem synthesis_returns_program (detailed : Bool) :
    synthesize (observe detailed) relation certification initialTable actionOrder () =
      some (program detailed) := by
  apply (synthesize_eq_some_iff (observe detailed) relation certification
    initialTable actionOrder () (program detailed)).mpr
  exact ⟨by decide, by decide, input_check detailed, rfl⟩

/-- A small legal record is a deterministic regression, not a random draw. -/
def quarterSamples : SampleTable State Unit 4
  | none, _, _ => none
  | some true, _, _ => some true
  | some false, _, k => if k.val = 0 then some true else some false

def eighthSamples : SampleTable State Unit 8
  | none, _, _ => none
  | some true, _, _ => some true
  | some false, _, k => if k.val = 0 then some true else some false

def missedGoal (T : ℕ) (h : CausalHistory State (Unit × State) T) : Bool :=
  decide (riskLastState T h ≠ some true)

def oracle {N : ℕ} (sample : SampleTable State Unit N) (i : ℕ) :
    UEOT.V3.Compression.TheoryCompletion.ScientificClosure.CertificationDecision :=
  noisyDecision (observe (decide (i ≠ 0))) sample (1 / 20) (1 / 8)

def computedBudget {N : ℕ} (sample : SampleTable State Unit N) (detailed : Bool) : ℚ :=
  riskBudget (program detailed) initialMass (observe detailed) (some false)
    sample (1 / 20) 2 (missedGoal 2)

def computedAccepts {N : ℕ} (sample : SampleTable State Unit N) (detailed : Bool) : Bool :=
  accepts (program detailed) initialMass (observe detailed) (some false)
    sample (1 / 20) (1 / 8) (7 / 10) 2 (missedGoal 2)

def candidateObserve (j : Fin 2) : State → State := observe (decide (j.val ≠ 0))

def candidateProgram (j : Fin 2) : Program State State Unit :=
  program (decide (j.val ≠ 0))

def computedSelection {N : ℕ} (sample : SampleTable State Unit N) : Option (Fin 2) :=
  selectCandidate candidateObserve sample (1 / 20) (1 / 8)

def computedSelectedAccepts {N : ℕ} (sample : SampleTable State Unit N) : Bool :=
  selectedAccepts candidateObserve candidateProgram initialMass (some false)
    sample (1 / 20) (1 / 8) (7 / 10) 2 (fun _ => missedGoal 2)

noncomputable section

open scoped Classical ENNReal BigOperators

local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Unit := ⊤
local instance : MeasurableSpace (Finset State) := ⊤

def parameter (theta : Bool) : ℝ := if theta then 1 / 8 else 1 / 4

private theorem parameter_pos (theta : Bool) : 0 < parameter theta := by
  cases theta <;> norm_num [parameter]

private theorem parameter_lt_one (theta : Bool) : parameter theta < 1 := by
  cases theta <;> norm_num [parameter]

def source (theta : Bool) : State → Unit → PMF State
  | none, _ => PMF.pure none
  | some false, _ =>
      (AbsorbingLeakage.kernel (parameter theta) (parameter_pos theta).le
        (parameter_lt_one theta).le false).map some
  | some true, _ => PMF.pure (some true)

def actualSource (theta : Bool) (_n : ℕ) : State → Unit → PMF State := source theta

def initialLaw : PMF State := PMF.pure (some false)

def certified (_n : ℕ) (x : State) (a : Unit) : Prop := certification x a

private theorem initial_support_exact (x : State) :
    x ∈ initialTable ↔ x ∈ initialLaw.support := by
  simp [initialTable, initialLaw, PMF.support_pure]

private theorem response_support (theta : Bool) (b : Bool) :
    b ∈ (AbsorbingLeakage.kernel (parameter theta) (parameter_pos theta).le
      (parameter_lt_one theta).le false).support := by
  rw [PMF.mem_support_iff]
  intro hz
  have heq := congrArg ENNReal.toReal hz
  rw [AbsorbingLeakage.kernel_mass] at heq
  cases theta <;> cases b <;>
    norm_num [AbsorbingLeakage.transitionMass, parameter] at heq

/-- Both unknown numerical choices realize the same structural support. -/
theorem source_support_exact (theta : Bool) (n : ℕ) (x : State) (a : Unit) (z : State) :
    z ∈ (actualSource theta n x a).support ↔ relation x a z := by
  cases x with
  | none => simp [actualSource, source, relation, PMF.support_pure]
  | some b =>
      cases b with
      | true => simp [actualSource, source, relation, PMF.support_pure]
      | false =>
          simp only [actualSource, source, PMF.mem_support_map_iff, relation]
          constructor
          · rintro ⟨b, _, rfl⟩
            cases b <;> simp
          · intro h
            rcases h with rfl | rfl
            · exact ⟨false, response_support theta false, rfl⟩
            · exact ⟨true, response_support theta true, rfl⟩

private theorem initial_safe :
    ∀ x ∈ initialLaw.support, x ∈ ExecutableSupportControllerWitness.safe := by
  intro x hx
  have heq : x = some false := by simpa [initialLaw, PMF.support_pure] using hx
  simp [heq, ExecutableSupportControllerWitness.safe]

private theorem relation_safe :
    ∀ x a, x ∈ ExecutableSupportControllerWitness.safe → certification x a →
      ∀ z, relation x a z → z ∈ ExecutableSupportControllerWitness.safe := by
  intro x a hx _ z hz
  cases x with
  | none => exact False.elim (hx rfl)
  | some b =>
      cases b with
      | false =>
          rcases hz with rfl | rfl <;> simp [ExecutableSupportControllerWitness.safe]
      | true =>
          have heq : z = some true := hz
          simp [heq, ExecutableSupportControllerWitness.safe]

/-- Structural all-time safety holds for each actual returned program and
both parameters; the statistical goal-risk certificate is a different claim. -/
theorem returned_program_all_times_safe (theta detailed : Bool) :
    FiniteMemoryPhysicalSafety.stateTrajMeasure (program detailed).toController
      initialLaw (observe detailed) (actualSource theta)
      {w | ∀ n : ℕ, w n ∈ ExecutableSupportControllerWitness.safe} = 1 := by
  exact synthesize_some_all_times_physical_safe (observe detailed) relation certification
    initialTable actionOrder () initialLaw (actualSource theta) certified (program detailed)
    (synthesis_returns_program detailed) initial_support_exact (source_support_exact theta)
    (fun _ _ _ => Iff.rfl) ExecutableSupportControllerWitness.safe initial_safe relation_safe

private theorem initial_mass_exact (x : State) :
    (initialMass x : ℝ) = (initialLaw x).toReal := by
  by_cases hx : x = some false <;> simp [initialMass, initialLaw, PMF.pure_apply, hx]

private theorem goal_envelope (detailed : Bool) :
    {h : CausalHistory State (Unit × State) 2 | missedGoal 2 h = true} ⊆
      (riskHistoryMap (observe detailed)
        (fun ax : Unit × State => (ax.1, observe detailed ax.2)) 2) ⁻¹'
          {h | missedGoal 2 h = true} := by
  intro h hh
  have hx : riskLastState 2 h ≠ some true := of_decide_eq_true hh
  have hq : observe detailed (riskLastState 2 h) ≠ some true := by
    cases detailed with
    | false => cases riskLastState 2 h <;> simp [observe]
    | true => exact hx
  change decide (riskLastState 2
    (riskHistoryMap (observe detailed)
      (fun ax : Unit × State => (ax.1, observe detailed ax.2)) 2 h) ≠ some true) = true
  simpa only [decide_eq_true_eq, risk_last_project] using hq

def actualGoalRisk (theta detailed : Bool) : ℝ :=
  (causalLaw initialLaw
    (riskMicroControlKernel (observe detailed) (actualSource theta)
      (program detailed).toController.policy) 2).toMeasure.real
        {h | missedGoal 2 h = true}

/-- The computed certificate bounds the goal risk of this very program on
the common calibration event, while its structural safety remains exact. -/
theorem computed_certificate_controls_actual_process
    (theta detailed : Bool) {N : ℕ} (hN : 0 < N)
    (sample : SampleTable State Unit N)
    (hgood : CalibrationGood (source theta) hN sample ((1 / 20 : ℚ) : ℝ))
    (haccept : computedAccepts sample detailed = true) :
    actualGoalRisk theta detailed ≤ ((7 / 10 : ℚ) : ℝ) ∧
      FiniteMemoryPhysicalSafety.stateTrajMeasure (program detailed).toController
        initialLaw (observe detailed) (actualSource theta)
        {w | ∀ n : ℕ, w n ∈ ExecutableSupportControllerWitness.safe} = 1 := by
  exact accepts_actual_risk_and_safety_on_good
    (observe detailed) relation certification initialTable actionOrder () hN
    (program detailed) (synthesis_returns_program detailed) initialMass initialLaw
    initial_mass_exact initial_support_exact (source theta)
    (source_support_exact theta 0) (some false) sample (1 / 20) (1 / 8) (7 / 10)
    hgood 2 (missedGoal 2) {h | missedGoal 2 h = true} (goal_envelope detailed)
    haccept ExecutableSupportControllerWitness.safe initial_safe relation_safe

/-- Training and deployment use the same unknown numerical model. -/
def modelJoint (theta : Bool) (N : ℕ) :
    PMF (SampleSpace State Unit N × CausalHistory State (Unit × State) 2) :=
  selectedTrainingDeployment (trainingMeasure N (source theta)).toPMF
    (fun record => computedSelection (samplesAt record))
    (selectedSourceDeployment candidateObserve candidateProgram initialLaw (source theta) () 2)

/-- This is the joint accepted-and-missed-goal event, with no conditioning
on acceptance and no assumed empirical fit or numerical budget conclusion. -/
theorem selected_model_joint_risk (theta : Bool) (N : ℕ) (hN : 0 < N) :
    (modelJoint theta N).toMeasure.real
      {z | computedSelectedAccepts (samplesAt z.1) = true ∧ missedGoal 2 z.2 = true} ≤
      min 1 (confidenceFailureBound State Unit N (1 / 20) +
        (1 - confidenceFailureBound State Unit N (1 / 20)) * ((7 / 10 : ℚ) : ℝ)) := by
  exact selected_accepts_and_failure_joint_le hN candidateObserve candidateProgram
    relation certification initialTable actionOrder ()
    (fun j => synthesis_returns_program (decide (j.val ≠ 0)))
    initialMass initialLaw initial_mass_exact initial_support_exact (source theta)
    (source_support_exact theta 0) (some false) (1 / 20) (1 / 8) (7 / 10)
    (by norm_num) (by norm_num [Set.mem_Icc]) 2 (fun _ => missedGoal 2)
    {h | missedGoal 2 h = true} (fun j => goal_envelope (decide (j.val ≠ 0)))

/-- The actual fixed allocation gives a nontrivial prospective error budget. -/
theorem registered_confidence_is_nontrivial :
    confidenceFailureBound State Unit 4096 (1 / 20) < 1 := by
  have hexp : (48 : ℝ) < Real.exp (512 / 25) := by
    have h := Real.add_one_le_exp (256 / 25 : ℝ)
    have hp := Real.exp_pos (256 / 25 : ℝ)
    have hprod := mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ Real.exp (256 / 25 : ℝ) + ((256 / 25 : ℝ) + 1) by linarith)
    have hdouble : Real.exp (512 / 25 : ℝ) =
        Real.exp (256 / 25 : ℝ) * Real.exp (256 / 25 : ℝ) := by
      rw [← Real.exp_add]
      congr 1
      norm_num
    rw [hdouble]
    nlinarith
  have hbudget : (48 : ℝ) * Real.exp (-(512 / 25 : ℝ)) < 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_lt_one (Real.exp_pos _)).mpr hexp
  have hraw : confidenceFailureBound State Unit 4096 (1 / 20) =
      min 1 ((48 : ℝ) * Real.exp (-(512 / 25 : ℝ))) := by
    norm_num [confidenceFailureBound, VariableRegisteredSamples.confidenceBudget,
      State, mul_assoc]
    congr 1
    ring
  rw [hraw]
  exact (min_le_right _ _).trans_lt hbudget

set_option backward.isDefEq.respectTransparency false in
/-- Unit action mass removes the policy from this exact two-step source
calculation. No terminal goal probability is supplied as a premise. -/
theorem actualGoalRisk_formula (theta detailed : Bool) :
    actualGoalRisk theta detailed = (1 - parameter theta) ^ 2 := by
  have hunit (p : PMF Unit) (a : Unit) : p a = 1 := by
    cases a
    simpa only [tsum_fintype, Fintype.sum_unique] using p.tsum_coe
  let K := riskMicroControlKernel (observe detailed) (actualSource theta)
    (program detailed).toController.policy
  have hstep (n : ℕ) (h : CausalHistory State (Unit × State) n) (z : State) :
      K n h ((), z) = source theta (riskLastState n h) () z := by
    change pmfExtend _ _ ((), z) = _
    rw [pmfExtend_apply, hunit, one_mul]
    rfl
  have hmass (x y z : State) :
      ((causalLaw initialLaw K 2) ((x, ((), y)), ((), z))).toReal =
        (initialLaw x).toReal * (source theta x () y).toReal *
          (source theta y () z).toReal := by
    change ((pmfExtend (causalLaw initialLaw K 1) (K 1)) ((x, ((), y)), ((), z))).toReal = _
    rw [pmfExtend_apply, hstep]
    change (((pmfExtend initialLaw (K 0)) (x, ((), y))) * source theta y () z).toReal = _
    rw [pmfExtend_apply, hstep]
    simp only [riskLastState, ENNReal.toReal_mul]
  unfold actualGoalRisk
  rw [show {h : CausalHistory State (Unit × State) 2 | missedGoal 2 h = true} =
    ((Finset.univ.filter (fun h => missedGoal 2 h = true)) : Set _) by ext h; simp]
  rw [pmfMeasureReal_eq_sum_finset, Finset.sum_filter]
  change (∑ h : (State × (Unit × State)) × (Unit × State),
    if missedGoal 2 h = true then _ else 0) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_bool,
    Fintype.sum_unique]
  simp only [missedGoal, riskLastState]
  simp only [← show K = riskMicroControlKernel (observe detailed) (actualSource theta)
    (program detailed).toController.policy from rfl, hmass]
  simp [source, initialLaw, PMF.map_apply, tsum_fintype,
    AbsorbingLeakage.transitionMass, pow_two]

/-- The prior family really contains a model above the requested risk cap. -/
theorem alternate_model_exceeds_cap (detailed : Bool) :
    ((7 / 10 : ℚ) : ℝ) < actualGoalRisk true detailed := by
  rw [actualGoalRisk_formula]
  norm_num [parameter]

/-- Even a noisy identity PASS needs the risk check: on the calibration
event the over-cap numerical source cannot obtain a deployment certificate. -/
theorem alternate_model_rejects_on_good {N : ℕ} (hN : 0 < N)
    (sample : SampleTable State Unit N)
    (hgood : CalibrationGood (source true) hN sample ((1 / 20 : ℚ) : ℝ)) :
    computedSelectedAccepts sample = false := by
  by_contra h
  have ha : computedSelectedAccepts sample = true := by simpa using h
  unfold computedSelectedAccepts selectedAccepts at ha
  cases hs : selectCandidate candidateObserve sample (1 / 20) (1 / 8) with
  | none =>
      rw [hs] at ha
      cases ha
  | some j =>
      rw [hs] at ha
      change computedAccepts sample (decide (j.val ≠ 0)) = true at ha
      exact (not_lt_of_ge (computed_certificate_controls_actual_process true
        (decide (j.val ≠ 0)) hN sample hgood ha).1)
          (alternate_model_exceeds_cap (decide (j.val ≠ 0)))

/-- Erroneous acceptance for the concrete over-cap source pays the single
common calibration-failure probability, rather than a post-selection law. -/
theorem alternate_model_acceptance_probability (N : ℕ) (hN : 0 < N) :
    (trainingMeasure N (source true)).real
      {record | computedSelectedAccepts (samplesAt record) = true} ≤
        confidenceFailureBound State Unit N (1 / 20) := by
  have hsub : {record : SampleSpace State Unit N |
      computedSelectedAccepts (samplesAt record) = true} ⊆
        {record | ¬ CalibrationGood (source true) hN (samplesAt record)
          ((1 / 20 : ℚ) : ℝ)} := by
    intro record ha hg
    have hr := alternate_model_rejects_on_good hN (samplesAt record) hg
    simp [hr] at ha
  exact (measureReal_mono hsub).trans
    (training_calibration N hN (source true) (1 / 20) (by norm_num)).2

end
end NoisyFiniteRiskOracleWitness
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
