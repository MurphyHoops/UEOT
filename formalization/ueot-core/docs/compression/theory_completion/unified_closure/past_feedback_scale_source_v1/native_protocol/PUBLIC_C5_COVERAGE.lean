import UEOT
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open DualDriveFiniteNoisyCalibration DualDriveFiniteCalibrationCoverage
-- This fixture tests boundary separation (gain1, truegap1/2), not just the author's gain2/gap1 examples.
def boundary (best : Bool) : Parameters := ⟨fun _ => 1,fun a => if a=best then 1/2 else 0⟩
example (best : Bool) (N : ℕ) (hN : 0<N) (w : Raw N) (hw : w∈Good N) :
    select (sourceData (boundary best) w)=some best := by
  apply good_selects_separated _ _ hN hw (by intro i; norm_num [boundary]) best
  cases best <;> norm_num [boundary]
example (best : Bool) : select (sourceData (boundary best) registeredRaw)=some best := by
  apply good_selects_separated _ _ (by decide) registered_good
    (by intro i; norm_num [boundary]) best
  cases best <;> norm_num [boundary]
example (best : Bool) : 0 < (rawLaw registeredBudget).real
    {w | select (sourceData (boundary best) w)=some best} := by
  have h := best_accept_probability_ge (boundary best) registeredBudget (by decide)
    (by intro i; norm_num [boundary]) best (by cases best <;> norm_num [boundary])
  have hh := registered_bound_nonvacuous
  norm_num [registeredBudget] at h
  linarith
example (data : Data 0) : select data=none := zero_budget_reject data
-- The actual downstream source-calibrated ranking theorem, for BOTH orderings, uses Valid explicitly.
example (best : Bool) : select (sourceData (boundary best) registeredRaw)=some best ∧
    ∀ a : Bool, a≠best → (boundary best).latent a<(boundary best).latent best := by
  have hv : Valid (boundary best) := by
    unfold Valid
    constructor
    · intro i; norm_num [boundary]
    · constructor
      · intro a; cases a <;> cases best <;> norm_num [boundary]
      · cases best <;> norm_num [boundary]
  exact good_correct_accepts _ hv _ (by decide) registered_good
    (by intro i; norm_num [boundary]) best (by cases best <;> norm_num [boundary])
#print axioms good_selects_separated
#print axioms good_correct_accepts
#print axioms not_best_probability_le
#print axioms best_accept_probability_ge
#print axioms registered_both_worlds_useful
