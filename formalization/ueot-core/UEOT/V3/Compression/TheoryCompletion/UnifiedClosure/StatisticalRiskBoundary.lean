import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage
import UEOT.V3.PathError

/-!
# Pointwise calibration does not survive optimistic action selection

Both actions have the same genuine Bernoulli next-state PMF, with failure
probability 3/4. Training draws one response from each action, using a PMF
product constructed by the registered causal extension operation.

For each fixed action the empirical failure probability has absolute error
at most 1/4 with probability 3/4. Selecting an empirically safer action after
seeing both responses raises the probability of calibration failure from
1/4 to 7/16. On precisely that event, the claimed empirical-plus-1/4 upper
bound also underestimates the actual one-step risk of the selected deployment row.

This is training-time selection followed by a fixed action. It is not an
online-adaptive sampling counterexample, and it does not violate a correctly
simultaneous confidence bound. The confidence probabilities here are exact
finite-PMF calculations, not a claim that the one-sample Hoeffding bound is
nonvacuous at this radius.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary

open scoped BigOperators ENNReal
open UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl

noncomputable section

/-- Each action has the same actual next-state row; `true` denotes failure. -/
def actionRow (_a : Bool) : PMF Bool :=
  AbsorbingLeakage.kernel (3 / 4) (by norm_num) (by norm_num) false

/-- One actual sample per action. The second row does not depend on the first draw. -/
def trainingLaw : PMF (Bool × Bool) :=
  pmfExtend (actionRow false) (fun _ => actionRow true)

/-- The sample obtained for the specified action. -/
def observed (d : Bool × Bool) (a : Bool) : Bool := if a then d.2 else d.1

def empiricalFailure (d : Bool × Bool) (a : Bool) : ℝ :=
  if observed d a then 1 else 0

/-- Select the first action when its response is safe, and the second otherwise. -/
def selectedAction (d : Bool × Bool) : Bool := d.1

def actualFailure (a : Bool) : ℝ := ((actionRow a) true).toReal

/-- For this model a safe training observation is exactly the bad-calibration event. -/
def badFlag (d : Bool × Bool) (a : Bool) : Bool := !(observed d a)

def selectedBadFlag (d : Bool × Bool) : Bool := badFlag d (selectedAction d)

/-- Event probability is the mass of `true` under the actual training pushforward. -/
def trainingProbability (event : Bool × Bool → Bool) : ℝ :=
  ((trainingLaw.map event) true).toReal

private theorem actionRow_apply (a b : Bool) :
    actionRow a b = ENNReal.ofReal (if b then (3 / 4 : ℝ) else 1 / 4) := by
  cases b <;>
    norm_num [actionRow, AbsorbingLeakage.kernel,
      FiniteProbabilityRow.ofRealRow, AbsorbingLeakage.transitionMass]

/-- The actual joint sampling law factors into the two action-row masses. -/
theorem trainingLaw_mass (b c : Bool) :
    trainingLaw (b, c) = actionRow false b * actionRow true c := by
  simp [trainingLaw]

private theorem trainingProbability_expand (event : Bool × Bool → Bool) :
    trainingProbability event =
      (if event (false, false) then (1 / 16 : ℝ) else 0) +
      (if event (false, true) then (3 / 16 : ℝ) else 0) +
      (if event (true, false) then (3 / 16 : ℝ) else 0) +
      (if event (true, true) then (9 / 16 : ℝ) else 0) := by
  classical
  unfold trainingProbability
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by
    intro d _
    split_ifs
    · exact PMF.apply_ne_top trainingLaw d
    · exact ENNReal.zero_ne_top)]
  cases h00 : event (false, false) <;>
    cases h01 : event (false, true) <;>
    cases h10 : event (true, false) <;>
    cases h11 : event (true, true) <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool,
      trainingLaw_mass, actionRow_apply, ENNReal.toReal_mul,
      h00, h01, h10, h11]

/-- The deployment row is fixed by the model, even when its action was selected from data. -/
@[simp] theorem actualFailure_eq (a : Bool) : actualFailure a = 3 / 4 := by
  norm_num [actualFailure, actionRow, AbsorbingLeakage.transitionMass]

/-- The selector really minimizes empirical failure over both available actions. -/
theorem selectedAction_empirically_minimal (d : Bool × Bool) (a : Bool) :
    empiricalFailure d (selectedAction d) ≤ empiricalFailure d a := by
  rcases d with ⟨b, c⟩
  cases b <;> cases c <;> cases a <;>
    norm_num [empiricalFailure, observed, selectedAction]

/-- Connect the computed event to the actual error of the sampled estimator. -/
theorem badFlag_iff_calibration_error (d : Bool × Bool) (a : Bool) :
    badFlag d a = true ↔
      (1 / 4 : ℝ) < |empiricalFailure d a - actualFailure a| := by
  rcases d with ⟨b, c⟩
  cases b <;> cases c <;> cases a <;>
    norm_num [badFlag, observed, empiricalFailure]

/-- Each action separately has a valid exact calibration failure probability of 1/4. -/
theorem fixed_action_bad_probability (a : Bool) :
    trainingProbability (fun d => badFlag d a) = 1 / 4 := by
  rw [trainingProbability_expand]
  cases a <;> norm_num [badFlag, observed]

/-- Optimistic training-time selection has calibration failure probability 7/16. -/
theorem selected_bad_probability :
    trainingProbability selectedBadFlag = 7 / 16 := by
  rw [trainingProbability_expand]
  norm_num [selectedBadFlag, badFlag, selectedAction, observed]

/-- On exactly the selected bad event, the claimed capped risk bound is false
for the genuine deployment row selected by the observed training data. -/
theorem selected_bad_iff_false_risk_bound (d : Bool × Bool) :
    selectedBadFlag d = true ↔
      min 1 (empiricalFailure d (selectedAction d) + 1 / 4) <
        ((actionRow (selectedAction d)) true).toReal := by
  change selectedBadFlag d = true ↔
    min 1 (empiricalFailure d (selectedAction d) + 1 / 4) <
      actualFailure (selectedAction d)
  rcases d with ⟨b, c⟩
  cases b <;> cases c <;>
    norm_num [selectedBadFlag, badFlag, selectedAction, observed, empiricalFailure]

/-- The original per-action failure budget is insufficient after selecting an action. -/
theorem pointwise_confidence_not_selected_confidence :
    (∀ a, trainingProbability (fun d => badFlag d a) = 1 / 4) ∧
      ¬ trainingProbability selectedBadFlag ≤ 1 / 4 := by
  constructor
  · exact fixed_action_bad_probability
  · rw [selected_bad_probability]
    norm_num

/-- Simultaneous calibration is a pointwise certificate for every later selector;
no independence of that selector from the training data is required. -/
theorem simultaneous_calibration_protects_any_selector
    (d : Bool × Bool) (choose : (Bool × Bool) → Bool)
    (hgood : ∀ a, |empiricalFailure d a - actualFailure a| ≤ 1 / 4) :
    |empiricalFailure d (choose d) - actualFailure (choose d)| ≤ 1 / 4 ∧
      actualFailure (choose d) ≤
        min 1 (empiricalFailure d (choose d) + 1 / 4) := by
  refine ⟨hgood (choose d), ?_⟩
  apply le_min
  · rw [actualFailure_eq]
    norm_num
  · have h := (abs_le.mp (hgood (choose d))).1
    linarith

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary
