import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverage
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage

/-!
# Finite witnesses for restricted sampling and deployment coverage

The actual transition and reference PMFs are shared by both examples.
Only the common policy changes. Exact history probabilities and empirical
training losses are proved from these normalized PMFs.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators Classical

noncomputable section

universe u

namespace DeploymentCoverageWitness

local instance : MeasurableSpace Bool := ⊤

/-!
Both witnesses use the same actual controlled row and the same reference.
Only their common deployment policy changes. A transition can recover from
failure, so the event below records failure anywhere in the actual history.
-/

/-- The certified action has a small, nonzero genuine transition error. -/
def certifiedRow : PMF Bool :=
  AbsorbingLeakage.kernel (1 / 8) (by norm_num) (by norm_num) false

/-- The unregistered action fails surely, independent of the previous state. -/
def actualRow (_x : Bool) (a : Bool) : PMF Bool :=
  if a then PMF.pure true else certifiedRow

def actualKernel : ℕ → Bool → Bool → PMF Bool := fun _ => actualRow

def referenceKernel : ℕ → Bool → Bool → PMF Bool :=
  fun _ _ _ => PMF.pure false

def certified (_n : ℕ) (_x : Bool) (a : Bool) : Prop := a = false

/-- Each fixed action PMF gives one history policy used by both path laws. -/
def policy (ρ : PMF Bool) (n : ℕ)
    (_h : CausalHistory Bool (Bool × Bool) n) : PMF Bool := ρ

def actualLaw (ρ : PMF Bool) (n : ℕ) :
    PMF (CausalHistory Bool (Bool × Bool) n) :=
  causalLaw (PMF.pure false) (riskMicroControlKernel id actualKernel (policy ρ)) n

def referenceLaw (ρ : PMF Bool) (n : ℕ) :
    PMF (CausalHistory Bool (Bool × Bool) n) :=
  causalLaw ((PMF.pure false).map id) (riskMacroControlKernel referenceKernel (policy ρ)) n

def failureEvent (n : ℕ) : Set (CausalHistory Bool (Bool × Bool) n) :=
  {h | riskEverFailure (fun b : Bool => b = true) n h}

def transitionMass (a z : Bool) : ℝ :=
  if a then (if z then 1 else 0) else (if z then 1 / 8 else 7 / 8)

@[simp] theorem actualRow_mass (x a z : Bool) :
    (actualRow x a z).toReal = transitionMass a z := by
  cases a <;> cases z <;>
    norm_num [actualRow, certifiedRow, AbsorbingLeakage.transitionMass, transitionMass]

/-- Canonical PMF total variation, computed from the actual normalized rows. -/
theorem actual_row_error (n : ℕ) (x a : Bool) :
    tvDist ((actualKernel n x a).map id).toMeasure
      (referenceKernel n x a).toMeasure = if a then 1 else 1 / 8 := by
  rw [PMF.map_id, UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  cases a <;>
    norm_num [actualKernel, referenceKernel, transitionMass, Fintype.sum_bool]

theorem certified_row_error (n : ℕ) (x a : Bool) (ha : certified n x a) :
    tvDist ((actualKernel n x a).map id).toMeasure
      (referenceKernel n x a).toMeasure ≤ 1 / 8 := by
  have ha' : a = false := ha
  subst a
  rw [actual_row_error]
  norm_num

/-- For this state-independent policy the actual uncovered occupancy is its
unregistered-action probability. This is derived from the actual prefix law. -/
theorem uncovered_probability (ρ : PMF Bool) (n : ℕ) :
    (coverageDeploymentRowLaw (PMF.pure false) id actualKernel (policy ρ) n).toMeasure.real
      {xa | ¬ certified n xa.1 xa.2} = (ρ true).toReal := by
  rw [← coverage_uncovered_indicator_expectation,
    coverage_rowLaw_expectation]
  calc
    _ = ∑ h, (causalLaw (PMF.pure false)
        (riskMicroControlKernel id actualKernel (policy ρ)) n h).toReal *
          (ρ true).toReal := by
      apply Finset.sum_congr rfl
      intro h _
      congr 1
      simp [policy, certified]
    _ = _ := by rw [← Finset.sum_mul, coverage_sum_toReal, one_mul]

private theorem event_probability_eq_sum
    {S : Type u} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (p : PMF S) (E : Set S) :
    p.toMeasure.real E = ∑ s, (p s).toReal * (if s ∈ E then 1 else 0) := by
  simpa using
    (coverage_uncovered_indicator_expectation p (fun s => s ∉ E)).symm

private theorem actualLaw_one_apply (ρ : PMF Bool) (b a z : Bool) :
    actualLaw ρ 1 (b, (a, z)) =
      (PMF.pure false b) * (ρ a * actualRow b a z) := by
  let K₀ : Bool → PMF (Bool × Bool) := fun initial => pmfExtend ρ (actualRow initial)
  change pmfExtend (PMF.pure false) K₀ (b, (a, z)) = _
  rw [pmfExtend_apply]
  dsimp only [K₀]
  rw [pmfExtend_apply]

private theorem actualLaw_two_apply (ρ : PMF Bool) (b a₁ z₁ a₂ z₂ : Bool) :
    actualLaw ρ 2 ((b, (a₁, z₁)), (a₂, z₂)) =
      ((PMF.pure false b) * (ρ a₁ * actualRow b a₁ z₁)) *
        (ρ a₂ * actualRow z₁ a₂ z₂) := by
  let K₀ : Bool → PMF (Bool × Bool) := fun initial => pmfExtend ρ (actualRow initial)
  let K₁ : (Bool × (Bool × Bool)) → PMF (Bool × Bool) :=
    fun h => pmfExtend ρ (actualRow h.2.2)
  change pmfExtend (pmfExtend (PMF.pure false) K₀) K₁
    ((b, (a₁, z₁)), (a₂, z₂)) = _
  rw [pmfExtend_apply, pmfExtend_apply]
  dsimp only [K₀, K₁]
  rw [pmfExtend_apply, pmfExtend_apply]

private theorem referenceLaw_one_apply (ρ : PMF Bool) (b a z : Bool) :
    referenceLaw ρ 1 (b, (a, z)) =
      (PMF.pure false b) * (ρ a * PMF.pure false z) := by
  unfold referenceLaw
  rw [PMF.map_id]
  let K₀ : Bool → PMF (Bool × Bool) := fun _ => pmfExtend ρ (fun _ => PMF.pure false)
  change pmfExtend (PMF.pure false) K₀ (b, (a, z)) = _
  rw [pmfExtend_apply]
  dsimp only [K₀]
  rw [pmfExtend_apply]

private theorem referenceLaw_two_apply (ρ : PMF Bool) (b a₁ z₁ a₂ z₂ : Bool) :
    referenceLaw ρ 2 ((b, (a₁, z₁)), (a₂, z₂)) =
      ((PMF.pure false b) * (ρ a₁ * PMF.pure false z₁)) *
        (ρ a₂ * PMF.pure false z₂) := by
  unfold referenceLaw
  rw [PMF.map_id]
  let K₀ : Bool → PMF (Bool × Bool) := fun _ => pmfExtend ρ (fun _ => PMF.pure false)
  let K₁ : (Bool × (Bool × Bool)) → PMF (Bool × Bool) :=
    fun _ => pmfExtend ρ (fun _ => PMF.pure false)
  change pmfExtend (pmfExtend (PMF.pure false) K₀) K₁
    ((b, (a₁, z₁)), (a₂, z₂)) = _
  rw [pmfExtend_apply, pmfExtend_apply]
  dsimp only [K₀, K₁]
  rw [pmfExtend_apply, pmfExtend_apply]

theorem reference_one_step_failure (ρ : PMF Bool) :
    (referenceLaw ρ 1).toMeasure.real (failureEvent 1) = 0 := by
  rw [event_probability_eq_sum]
  apply Finset.sum_eq_zero
  intro h _
  rcases h with ⟨b, a, z⟩
  change Bool at b
  erw [referenceLaw_one_apply ρ b a z]
  have hEvent : (b, (a, z)) ∈ failureEvent 1 ↔ b = true ∨ z = true := Iff.rfl
  erw [hEvent]
  cases b <;> cases z <;> simp

theorem reference_two_step_failure (ρ : PMF Bool) :
    (referenceLaw ρ 2).toMeasure.real (failureEvent 2) = 0 := by
  rw [event_probability_eq_sum]
  apply Finset.sum_eq_zero
  intro h _
  rcases h with ⟨⟨b, a₁, z₁⟩, a₂, z₂⟩
  change Bool at b
  erw [referenceLaw_two_apply ρ b a₁ z₁ a₂ z₂]
  have hEvent : ((b, (a₁, z₁)), (a₂, z₂)) ∈ failureEvent 2 ↔
      (b = true ∨ z₁ = true) ∨ z₂ = true := Iff.rfl
  erw [hEvent]
  cases b <;> cases z₁ <;> cases z₂ <;> simp

/-! ## Restricted deployment with a nonzero uncovered probability -/

def restrictedActionLaw : PMF Bool :=
  AbsorbingLeakage.kernel (1 / 4) (by norm_num) (by norm_num) false

@[simp] theorem restrictedActionLaw_mass (a : Bool) :
    (restrictedActionLaw a).toReal = if a then 1 / 4 else 3 / 4 := by
  cases a <;>
    norm_num [restrictedActionLaw, AbsorbingLeakage.transitionMass]

theorem restricted_uncovered_probability (n : ℕ) :
    (coverageDeploymentRowLaw (PMF.pure false) id actualKernel
      (policy restrictedActionLaw) n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 1 / 4 := by
  rw [uncovered_probability, restrictedActionLaw_mass]
  norm_num

/-- The additive certificate remains nonvacuous despite incomplete coverage. -/
theorem restricted_two_step_budget :
    (∑ n ∈ Finset.range 2, ((1 / 8 : ℝ) + (1 - 1 / 8) *
      (coverageDeploymentRowLaw (PMF.pure false) id actualKernel
        (policy restrictedActionLaw) n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2})) = 11 / 16 ∧
      (11 / 16 : ℝ) < 1 := by
  simp_rw [restricted_uncovered_probability]
  norm_num [Finset.sum_range_succ]

/-- Independent exact enumeration of the same actual two-transition PMF. -/
theorem restricted_two_step_failure :
    (actualLaw restrictedActionLaw 2).toMeasure.real (failureEvent 2) = 583 / 1024 := by
  rw [event_probability_eq_sum]
  let term : ((Bool × (Bool × Bool)) × (Bool × Bool)) → ℝ := fun h =>
    (if h.1.1 = false then 1 else 0) *
      ((if h.1.2.1 then 1 / 4 else 3 / 4) * transitionMass h.1.2.1 h.1.2.2) *
      ((if h.2.1 then 1 / 4 else 3 / 4) * transitionMass h.2.1 h.2.2) *
      (if (h.1.1 = true ∨ h.1.2.2 = true) ∨ h.2.2 = true then 1 else 0)
  trans ∑ h : CausalHistory Bool (Bool × Bool) 2, term h
  · apply Finset.sum_congr rfl
    intro h _
    rcases h with ⟨⟨b, a₁, z₁⟩, a₂, z₂⟩
    change Bool at b
    erw [actualLaw_two_apply restrictedActionLaw b a₁ z₁ a₂ z₂]
    have hEvent : ((b, (a₁, z₁)), (a₂, z₂)) ∈ failureEvent 2 ↔
        (b = true ∨ z₁ = true) ∨ z₂ = true := Iff.rfl
    erw [hEvent]
    cases b <;> cases a₁ <;> cases z₁ <;> cases a₂ <;> cases z₂ <;>
      norm_num [term, ENNReal.toReal_mul, transitionMass]
  · change (∑ h : ((Bool × (Bool × Bool)) × (Bool × Bool)), term h) = (583 / 1024 : ℝ)
    norm_num [term, transitionMass, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The general coverage theorem is consumed by the actual microscopic
ever-failure event; the exact finite computation above is an independent check. -/
theorem restricted_two_step_failure_le :
    (actualLaw restrictedActionLaw 2).toMeasure.real (failureEvent 2) ≤ 11 / 16 := by
  have h := coverage_same_policy_microscopic_failure_risk
    (PMF.pure false) id actualKernel referenceKernel (policy restrictedActionLaw)
    certified (fun _ => 1 / 8) 2
    (fun n _ x a ha => certified_row_error n x a ha)
    (failureEvent 2) (failureEvent 2)
    (by
      intro h hh
      exact risk_ever_failure_envelope id (fun b : Bool => b = true)
        (fun b : Bool => b = true) (fun _ hb => hb) 2 h hh)
  change (actualLaw restrictedActionLaw 2).toMeasure.real (failureEvent 2) ≤
    min 1 ((referenceLaw restrictedActionLaw 2).toMeasure.real (failureEvent 2) + _) at h
  rw [reference_two_step_failure, restricted_two_step_budget.1] at h
  norm_num at h ⊢
  exact h

/-! ## Training row information does not control an uncovered deployment -/

/-- The training row distribution registers only the certified action. -/
def trainingRowLaw : PMF (Bool × Bool) := PMF.pure (false, false)

def trainingMeanTrueError : ℝ :=
  ∑ xa, (trainingRowLaw xa).toReal *
    tvDist ((actualKernel 0 xa.1 xa.2).map id).toMeasure
      (referenceKernel 0 xa.1 xa.2).toMeasure

/-- Even the true error averaged over the training row law is small. -/
theorem training_mean_true_error : trainingMeanTrueError = 1 / 8 := by
  unfold trainingMeanTrueError
  simp_rw [actual_row_error]
  norm_num [trainingRowLaw, Fintype.sum_prod_type, Fintype.sum_bool]

theorem uncovered_deployment_probability (n : ℕ) :
    (coverageDeploymentRowLaw (PMF.pure false) id actualKernel
      (policy (PMF.pure true)) n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 1 := by
  rw [uncovered_probability]
  simp

/-- Actual one-step deployment failure, from the same transition PMFs. -/
theorem uncovered_deployment_failure :
    (actualLaw (PMF.pure true) 1).toMeasure.real (failureEvent 1) = 1 := by
  rw [event_probability_eq_sum]
  let term : Bool × (Bool × Bool) → ℝ := fun h =>
    if h.1 = false ∧ h.2.1 = true ∧ h.2.2 = true then 1 else 0
  trans ∑ h : CausalHistory Bool (Bool × Bool) 1, term h
  · apply Finset.sum_congr rfl
    intro h _
    rcases h with ⟨b, a, z⟩
    change Bool at b
    erw [actualLaw_one_apply (PMF.pure true) b a z]
    have hEvent : (b, (a, z)) ∈ failureEvent 1 ↔ b = true ∨ z = true := Iff.rfl
    erw [hEvent]
    cases b <;> cases a <;> cases z <;>
      norm_num [term, ENNReal.toReal_mul, transitionMass]
  · change (∑ h : Bool × (Bool × Bool), term h) = 1
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num [term]

/-- Replacing the actual coverage penalty by training-average row error is false. -/
theorem training_average_does_not_bound_deployment :
    trainingMeanTrueError = 1 / 8 ∧
      ¬ ((actualLaw (PMF.pure true) 1).toMeasure.real (failureEvent 1) ≤
        (referenceLaw (PMF.pure true) 1).toMeasure.real (failureEvent 1) +
          trainingMeanTrueError) := by
  rw [training_mean_true_error, uncovered_deployment_failure, reference_one_step_failure]
  norm_num

/-- A literal one-draw training experiment is sampled from its actual source row. -/
def trainingSampleLaw : PMF Bool := actualRow false false

/-- The fitted one-sample row is a PMF; its empirical TV loss uses the same reference. -/
def empiricalLoss (z : Bool) : ℝ :=
  tvDist (PMF.pure z).toMeasure (referenceKernel 0 false false).toMeasure

theorem empirical_loss (z : Bool) : empiricalLoss z = if z then 1 else 0 := by
  unfold empiricalLoss referenceKernel
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  cases z <;> norm_num [Fintype.sum_bool]

/-- With probability 7/8 the actual training draw has exactly zero empirical
loss, while the uncovered deployment still fails with probability one. -/
theorem zero_empirical_loss_with_failed_deployment :
    trainingSampleLaw.toMeasure.real {z | empiricalLoss z = 0} = 7 / 8 ∧
      (actualLaw (PMF.pure true) 1).toMeasure.real (failureEvent 1) = 1 := by
  constructor
  · rw [event_probability_eq_sum]
    norm_num [trainingSampleLaw, empirical_loss, Fintype.sum_bool, transitionMass]
  · exact uncovered_deployment_failure

end DeploymentCoverageWitness

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
