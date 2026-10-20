import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredDeploymentRisk
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage

/-!
# A registered sampling experiment with data-dependent actual deployment

The finite product sampling law uses the true registered source rows.
A recorded sample selects between two distinct actual deployment laws.
The example proves its common-good-event risk budget and its exact joint
risk, while preserving a positive-probability record on which an all-record
small-budget premise fails.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace RegisteredSelectionWitness

open MeasureTheory ProbabilityTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open RegisteredGoodJointCheck
open scoped BigOperators Classical ENNReal

noncomputable section

local instance : MeasurableSpace Bool := ⊤

/-- The two controls have distinct genuine one-step failure chances. -/
def failureChance (a : Bool) : ℝ := if a then 1 / 4 else 1 / 8

def actualRow (a : Bool) : PMF Bool :=
  AbsorbingLeakage.kernel (failureChance a)
    (by cases a <;> norm_num [failureChance])
    (by cases a <;> norm_num [failureChance]) false

def source (_n : ℕ) (_x : Bool) (a : Bool) : PMF Bool := actualRow a

@[simp] theorem actualRow_mass (a z : Bool) :
    (actualRow a z).toReal = if z then failureChance a else 1 - failureChance a := by
  cases z <;> simp [actualRow, AbsorbingLeakage.transitionMass]

/-- No row at the state `true` is included in the training data. -/
def certified (n : ℕ) (x : Bool) (_a : Bool) : Prop := n = 0 ∧ x = false

abbrev Registered := CoverageRegisteredRow certified 1

def rowIndex (a : Bool) : Registered :=
  ⟨(⟨0, by decide⟩, a, false), by simp [certified]⟩

theorem registered_eq (j : Registered) : j = rowIndex j.1.2.1 := by
  apply Subtype.ext
  apply Prod.ext (Subsingleton.elim _ _)
  change j.1.2 = (j.1.2.1, false)
  exact Prod.ext rfl j.property.2

def registeredEquivBool : Registered ≃ Bool where
  toFun j := j.1.2.1
  invFun := rowIndex
  left_inv j := (registered_eq j).symm
  right_inv _ := rfl

@[simp] theorem registered_card : Fintype.card Registered = 2 := by
  exact (Fintype.card_congr registeredEquivBool).trans (by decide)

def registeredSource (j : Registered) : PMF Bool :=
  source j.1.1 j.1.2.2 j.1.2.1

abbrev SampleSpace := (Registered × Fin 256) → Bool

def trainingLaw : Measure SampleSpace :=
  StatisticalRiskWitness.productRowLaw registeredSource 256

instance trainingLaw_isProbability : IsProbabilityMeasure trainingLaw := by
  unfold trainingLaw
  infer_instance

def samples (j : Registered) (k : Fin 256) (ω : SampleSpace) : Bool :=
  StatisticalRiskWitness.productRowSample j k ω

theorem samples_measurable (j : Registered) (k : Fin 256) :
    Measurable (samples j k) :=
  StatisticalRiskWitness.productRowSample_measurable j k

theorem samples_independent (j : Registered) :
    iIndepFun (samples j) trainingLaw :=
  StatisticalRiskWitness.productRowSample_independent registeredSource 256 j

theorem samples_law (j : Registered) (k : Fin 256) :
    trainingLaw.map (samples j k) =
      (source j.1.1 j.1.2.2 j.1.2.1).toMeasure :=
  StatisticalRiskWitness.productRowSample_law registeredSource j k

/-- The selection rule depends on an actual registered source observation. -/
def selectedAction (ω : SampleSpace) : Bool := samples (rowIndex false) 0 ω

def empiricalRow (ω : SampleSpace) (a : Bool) : PMF Bool :=
  empiricalResponsePMF (by decide : 0 < 256) (samples (rowIndex a)) ω

def constantPolicy (a : Bool) :
    ∀ n, CausalHistory Bool (Bool × Bool) n → PMF Bool :=
  fun _ _ => PMF.pure a

def policy (ω : SampleSpace) := constantPolicy (selectedAction ω)

def reference (ω : SampleSpace) (_n : ℕ) (_x : Bool) (a : Bool) : PMF Bool :=
  empiricalRow ω a

/-- Every candidate is the empirical model and selected control encoded by
one complete record. No optimality of the selection rule is asserted. -/
def actualByAction (a : Bool) : PMF (CausalHistory Bool (Bool × Bool) 1) :=
  causalLaw (PMF.pure false) (riskMicroControlKernel id source (constantPolicy a)) 1

def actualDeployment (ω : SampleSpace) : PMF (CausalHistory Bool (Bool × Bool) 1) :=
  actualByAction (selectedAction ω)

def failure : Set (CausalHistory Bool (Bool × Bool) 1) :=
  {h | riskLastState 1 h = true}

private def oneStepLaw (row : Bool → PMF Bool) (a : Bool) :
    PMF (CausalHistory Bool (Bool × Bool) 1) :=
  causalLaw (PMF.pure false)
    (riskMacroControlKernel (fun _ _ => row) (constantPolicy a)) 1

private theorem oneStepLaw_eq_map (row : Bool → PMF Bool) (a : Bool) :
    oneStepLaw row a = (row a).map
      (fun z => ((false, (a, z)) : CausalHistory Bool (Bool × Bool) 1)) := by
  change pmfExtend (PMF.pure false) (fun _ => pmfExtend (PMF.pure a) row) = _
  unfold pmfExtend
  rw [PMF.pure_bind, PMF.pure_bind, PMF.map_comp]
  rfl

private theorem singleton_probability (p : PMF Bool) (a : Bool) :
    p.toMeasure.real {a} = (p a).toReal := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton p a (MeasurableSet.singleton a)]

private theorem oneStep_failure (row : Bool → PMF Bool) (a : Bool) :
    (oneStepLaw row a).toMeasure.real failure = (row a).toMeasure.real {true} := by
  rw [oneStepLaw_eq_map]
  have hf : Measurable (fun z : Bool =>
      ((false, (a, z)) : CausalHistory Bool (Bool × Bool) 1)) := measurable_of_finite _
  have hE : MeasurableSet failure := Set.to_countable _ |>.measurableSet
  erw [← PMF.toMeasure_map _ _ hf]
  simp only [Measure.real]
  erw [Measure.map_apply hf hE]
  rfl

/-- These are probabilities of the genuine causal deployment PMFs. -/
theorem actual_failure (a : Bool) :
    (actualByAction a).toMeasure.real failure = failureChance a := by
  change (oneStepLaw actualRow a).toMeasure.real failure = _
  rw [oneStep_failure, singleton_probability, actualRow_mass]
  rfl

/-- The actual state/action law is certified before the only transition. -/
theorem actual_occupancy_zero (ω : SampleSpace) :
    (coverageDeploymentRowLaw (PMF.pure false) id source (policy ω) 0).toMeasure.real
      {xa | ¬ certified 0 xa.1 xa.2} = 0 := by
  rw [← coverage_uncovered_indicator_expectation, coverage_rowLaw_expectation]
  change (∑ x : Bool, ((PMF.pure false) x).toReal *
    ∑ a : Bool, ((PMF.pure (selectedAction ω)) a).toReal *
      (if certified 0 x a then 0 else 1)) = 0
  simp [certified]

def Good (ω : SampleSpace) : Prop :=
  RegisteredCalibrationGood (by decide : 0 < 256) source certified 1 samples
    (fun _ => 1 / 8) ω

/-- The reference row is literally the registered empirical row. -/
theorem empirical_fit (ω : SampleSpace) (n : ℕ) (hn : n < 1)
    (x a : Bool) (hc : certified n x a) :
    tvDist ((empiricalResponsePMF (by decide : 0 < 256)
      (samples ⟨(⟨n, hn⟩, a, x), hc⟩) ω).map id).toMeasure
      (reference ω n x a).toMeasure ≤ 0 := by
  have hj : (⟨(⟨n, hn⟩, a, x), hc⟩ : Registered) = rowIndex a :=
    registered_eq _
  rw [hj, PMF.map_id]
  exact le_of_eq (tvDist_self_eq_zero (empiricalRow ω a).toMeasure)

/-- The same calibration event also controls the empirical reference's
failure probability; this is not an identification with the true risk. -/
theorem empirical_failure_on_good (ω : SampleSpace) (hg : Good ω) (a : Bool) :
    (empiricalRow ω a).toMeasure.real {true} ≤ 3 / 8 := by
  have hcal : tvDist (actualRow a).toMeasure (empiricalRow ω a).toMeasure ≤ 1 / 8 :=
    hg (rowIndex a)
  have hdiff := (tvEvent_le (actualRow a).toMeasure (empiricalRow ω a).toMeasure
    {true} (MeasurableSet.singleton true)).trans hcal
  rw [singleton_probability, actualRow_mass] at hdiff
  have hchance : failureChance a ≤ 1 / 4 := by
    cases a <;> norm_num [failureChance]
  change |failureChance a - (empiricalRow ω a).toMeasure.real {true}| ≤ (1 / 8 : ℝ) at hdiff
  have hlower := (abs_le.mp hdiff).1
  linarith

def referenceFailure (ω : SampleSpace) : ℝ :=
  (causalLaw ((PMF.pure false).map id)
    (riskMacroControlKernel (reference ω) (policy ω)) 1).toMeasure.real failure

theorem referenceFailure_eq (ω : SampleSpace) :
    referenceFailure ω = (empiricalRow ω (selectedAction ω)).toMeasure.real {true} := by
  unfold referenceFailure
  rw [PMF.map_id]
  exact oneStep_failure (empiricalRow ω) (selectedAction ω)

/-- The checked expression contains no unknown deployment occupancy. -/
def checkedBudget (ω : SampleSpace) : ℝ :=
  min 1 (referenceFailure ω +
    ∑ _n ∈ Finset.range 1, (min 1 ((1 / 8 : ℝ) + 0) +
      (1 - min 1 ((1 / 8 : ℝ) + 0)) * 0))

theorem checkedBudget_on_good (ω : SampleSpace) (hg : Good ω) :
    checkedBudget ω ≤ 1 / 2 := by
  have h := empirical_failure_on_good ω hg (selectedAction ω)
  rw [← referenceFailure_eq] at h
  have hsum : (∑ _n ∈ Finset.range 1, (min 1 ((1 / 8 : ℝ) + 0) +
      (1 - min 1 ((1 / 8 : ℝ) + 0)) * 0)) = (1 / 8 : ℝ) := by norm_num
  rw [checkedBudget, hsum]
  exact (min_le_right _ _).trans (by linarith)

/-- There are exactly two registered rows and four Boolean event tests. -/
theorem confidenceBudget_eq :
    registeredConfidenceBudget certified 1 256 (fun _ => (1 / 8 : ℝ)) =
      16 * Real.exp (-8) := by
  unfold registeredConfidenceBudget
  norm_num [registered_card, Fintype.card_finset]
  ring

theorem confidenceBudget_small :
    registeredConfidenceBudget certified 1 256 (fun _ => (1 / 8 : ℝ)) ≤ 1 / 16 := by
  rw [confidenceBudget_eq]
  have h := StatisticalRiskWitness.concrete_confidence_nonvacuous
  linarith

/-- The same good event supplies calibration, empirical fit, the actual
zero-occupancy certificate and the small selected reference budget. -/
theorem registered_selected_joint_bound :
    (selectedTrainingDeployment trainingLaw.toPMF id actualDeployment).toMeasure.real
      {z | z.2 ∈ failure} ≤ 17 / 32 := by
  have h := registered_selected_joint_failure_of_cap_on_good
    (by decide : 0 < 256) trainingLaw source certified 1 samples (fun _ => (1 / 8 : ℝ))
    samples_measurable samples_independent samples_law (by intros; norm_num)
    (id : SampleSpace → SampleSpace) (fun _ => id) (fun _ => PMF.pure false)
    reference policy (fun _ _ => 0) (fun _ _ => 0)
    (by intro ω _ n hn x a hc; exact empirical_fit ω n hn x a hc)
    (by
      intro ω _ n hn
      have hn0 : n = 0 := by omega
      subst n
      exact le_of_eq (actual_occupancy_zero ω))
    failure (fun _ => failure)
    (by
      intro _ h hh
      change riskLastState 1 h = true at hh ⊢
      exact hh)
    (1 / 2) (by norm_num)
    (by intro ω hg; exact checkedBudget_on_good ω hg)
  have hrisk :
      (selectedTrainingDeployment trainingLaw.toPMF id actualDeployment).toMeasure.real
        {z | z.2 ∈ failure} ≤
      min 1 (registeredConfidenceBudget certified 1 256 (fun _ => (1 / 8 : ℝ)) +
        (1 - registeredConfidenceBudget certified 1 256 (fun _ => (1 / 8 : ℝ))) *
          (1 / 2)) := h.2
  have hα := confidenceBudget_small
  exact hrisk.trans ((min_le_right _ _).trans (by linarith))

/-- The distribution of the selected action is an actual source marginal. -/
theorem selectedAction_law :
    trainingLaw.map selectedAction = (actualRow false).toMeasure :=
  samples_law (rowIndex false) 0

theorem selectedAction_pmf :
    trainingLaw.toPMF.map selectedAction = actualRow false := by
  have hm : (trainingLaw.toPMF.map selectedAction).toMeasure =
      (actualRow false).toMeasure := by
    rw [← PMF.toMeasure_map _ _ (measurable_of_finite _), Measure.toPMF_toMeasure]
    exact selectedAction_law
  apply PMF.ext
  intro a
  have h := congrArg (fun μ : Measure Bool => μ {a}) hm
  simpa only [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton a)] using h

theorem selection_probability (a : Bool) :
    trainingLaw.real {ω | selectedAction ω = a} =
      if a then 1 / 8 else 7 / 8 := by
  have h := congrArg (fun μ : Measure Bool => μ.real {a}) selectedAction_law
  rw [measureReal_def, Measure.map_apply (measurable_of_finite _)
    (MeasurableSet.singleton a)] at h
  change trainingLaw.real {ω | selectedAction ω = a} = _ at h
  rw [h, singleton_probability, actualRow_mass]
  cases a <;> norm_num [failureChance]

/-- The two selected actual path laws differ, not just their model names. -/
theorem actual_deployments_distinct : actualByAction false ≠ actualByAction true := by
  intro h
  have hr := congrArg (fun p : PMF (CausalHistory Bool (Bool × Bool) 1) =>
    p.toMeasure.real failure) h
  rw [actual_failure, actual_failure] at hr
  norm_num [failureChance] at hr

/-- Both deployment choices have strictly positive probability under the
actual registered training experiment. -/
theorem two_positive_deployment_choices :
    trainingLaw.real {ω | selectedAction ω = false} = 7 / 8 ∧
    trainingLaw.real {ω | selectedAction ω = true} = 1 / 8 ∧
    actualByAction false ≠ actualByAction true := by
  exact ⟨selection_probability false, selection_probability true, actual_deployments_distinct⟩

/-- The exact risk follows from the selected conditional source laws and
the actual first-sample marginal; no independent selector law is assumed. -/
theorem actual_joint_failure_exact :
    (selectedTrainingDeployment trainingLaw.toPMF id actualDeployment).toMeasure.real
      {z | z.2 ∈ failure} = 9 / 64 := by
  rw [selectedTrainingDeployment_failure_tower trainingLaw.toPMF
    (id : SampleSpace → SampleSpace) actualDeployment (fun _ => failure)]
  simp only [id_eq, actualDeployment, actual_failure]
  rw [← coverage_expectation_map trainingLaw.toPMF selectedAction failureChance]
  rw [selectedAction_pmf]
  norm_num [Fintype.sum_bool, actualRow_mass, failureChance]

def allTrue : SampleSpace := fun _ => true

@[simp] private theorem allTrue_selects_true : selectedAction allTrue = true := rfl

@[simp] theorem empiricalRow_allTrue (a : Bool) : empiricalRow allTrue a = PMF.pure true := by
  unfold empiricalRow empiricalResponsePMF
  change (PMF.uniformOfFintype (Fin 256)).map (Function.const (Fin 256) true) = _
  exact PMF.map_const _ _

/-- This actual record violates an all-record checked-budget premise. -/
theorem allTrue_checkedBudget : checkedBudget allTrue = 1 := by
  unfold checkedBudget
  rw [referenceFailure_eq, allTrue_selects_true, empiricalRow_allTrue,
    singleton_probability]
  norm_num

theorem all_record_budget_false : ¬ (∀ ω : SampleSpace, checkedBudget ω ≤ 1 / 2) := by
  intro h
  have hbad := h allTrue
  rw [allTrue_checkedBudget] at hbad
  norm_num at hbad

/-- The exceptional record is possible in the genuine finite product law. -/
theorem allTrue_positive_probability : 0 < trainingLaw.real {allTrue} := by
  have hset : ({allTrue} : Set SampleSpace) =
      Set.pi Set.univ (fun _ : Registered × Fin 256 => ({true} : Set Bool)) := by
    ext ω
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h
      subst ω
      intro i
      rfl
    · intro h
      funext i
      exact h i
  have hmass : trainingLaw {allTrue} =
      ∏ i : Registered × Fin 256, registeredSource i.1 true := by
    rw [hset]
    unfold trainingLaw StatisticalRiskWitness.productRowLaw
    rw [Measure.pi_pi]
    congr 1
    funext i
    exact PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton true)
  have hpos : 0 < trainingLaw {allTrue} := by
    rw [hmass]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i _ hz
    have hr := congrArg ENNReal.toReal hz
    change (actualRow i.1.1.2.1 true).toReal = 0 at hr
    rw [actualRow_mass] at hr
    cases ha : i.1.1.2.1 <;> norm_num [ha, failureChance] at hr
  exact ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top _ _)

/-- A bundled nonvacuous closed experiment, including the reason for the
Good-only budget interface and two genuinely different deployments. -/
theorem registered_selection_joint_witness :
    (selectedTrainingDeployment trainingLaw.toPMF id actualDeployment).toMeasure.real
        {z | z.2 ∈ failure} ≤ 17 / 32 ∧
    (17 / 32 : ℝ) < 1 ∧
    (selectedTrainingDeployment trainingLaw.toPMF id actualDeployment).toMeasure.real
        {z | z.2 ∈ failure} = 9 / 64 ∧
    trainingLaw.real {ω | selectedAction ω = false} = 7 / 8 ∧
    trainingLaw.real {ω | selectedAction ω = true} = 1 / 8 ∧
    actualByAction false ≠ actualByAction true ∧
    0 < trainingLaw.real {allTrue} ∧
    ¬ (∀ ω : SampleSpace, checkedBudget ω ≤ 1 / 2) := by
  exact ⟨registered_selected_joint_bound, by norm_num, actual_joint_failure_exact,
    selection_probability false, selection_probability true, actual_deployments_distinct,
    allTrue_positive_probability, all_record_budget_false⟩


end
end RegisteredSelectionWitness
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
