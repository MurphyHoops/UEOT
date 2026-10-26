import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TotalFiniteWindow
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteWindowDoobWitness

/-!
# An actual source with a null conditional row and unsafe initial mass

The original deterministic source is false -> true -> cemetery -> cemetery.
Its initial law is uniform on all three states. Survival through one step has
mass 1/3. The safe state true has zero one-step survival, so its totalized row
can genuinely differ between two fallback choices. Both generated complete
conditional paths are nevertheless the same point mass (false,true).
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TotalFiniteWindowWitnessCheck

open MeasureTheory UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly UEOT.V3.QSDPerron
open SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open SameSourceConditionedTerminalCheck SameSourceFiniteWindowCheck FiniteWindowDoobCheck
open TotalFiniteWindowCheck
open FiniteWindowDoobWitnessCheck (State safe safeEquiv observe feedback)
open scoped BigOperators Classical

noncomputable section

local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Unit := ⊤

def successor : State → State
  | some false => some true
  | _ => none

def model : Model State (fun _ => Unit) where
  transition := fun x _ y => (PMF.pure (successor x) y).toReal
  reward := fun _ _ => 0
  rewardBound := 1
  discount := 1 / 2
  transition_nonneg := fun _ _ _ => ENNReal.toReal_nonneg
  transition_sum_one := fun x _ => coverage_sum_toReal (PMF.pure (successor x))
  reward_abs_le := by intros; norm_num
  discount_pos := by norm_num
  discount_lt_one := by norm_num

def initial : PMF State := PMF.uniformOfFintype State
def killed : Matrix safe safe ℝ :=
  killedMatrix model (liftedStationaryPolicy observe feedback) safe

private theorem sum_safe (f : safe → ℝ) :
    (∑ v : safe, f v) = f (safeEquiv false) + f (safeEquiv true) := by
  simpa [Fintype.sum_bool, add_comm] using (safeEquiv.sum_comp f).symm

private theorem initial_safe_mass (b : Bool) :
    safeInitialRow initial safe (safeEquiv b) = 1 / 3 := by
  norm_num [safeInitialRow, initial, PMF.uniformOfFintype_apply]

private theorem initial_unsafe_mass : (initial none).toReal = 1 / 3 := by
  norm_num [initial, PMF.uniformOfFintype_apply]

private theorem killed_entry (i j : Bool) :
    killed (safeEquiv i) (safeEquiv j) = if i then 0 else if j then 1 else 0 := by
  cases i <;> cases j <;>
    norm_num [killed, killedMatrix, policyMatrix, Model.policyTransition,
      liftedStationaryPolicy, observe, feedback, model, successor, safeEquiv, PMF.pure_apply]

private theorem killed_nonneg (i j : safe) : 0 ≤ killed i j :=
  killedMatrix_nonneg model (liftedStationaryPolicy observe feedback) safe i j

private theorem remaining_one (b : Bool) :
    remainingSurvival killed 1 (safeEquiv b) = if b then 0 else 1 := by
  rw [show 1 = 0 + 1 by rfl, remainingSurvival_succ, sum_safe]
  simp only [remainingSurvival_zero, mul_one, killed_entry]
  cases b <;> norm_num

private theorem survival_one :
    actualSurvivalMass model observe feedback initial safe 1 = 1 / 3 := by
  rw [actual_survival_mass_eq_initial_remaining_sum]
  change (∑ i : safe, safeInitialRow initial safe i * remainingSurvival killed 1 i) = _
  rw [sum_safe, initial_safe_mass, initial_safe_mass, remaining_one, remaining_one]
  norm_num

private theorem survival_one_pos :
    0 < actualSurvivalMass model observe feedback initial safe (1 + 0) := by
  rw [Nat.add_zero, survival_one]
  norm_num

def fallback (b : Bool) (_ : ℕ) (_ : safe) : PMF safe := PMF.pure (safeEquiv b)
def outside (b : Bool) (_ : ℕ) (_ : State) : PMF State := PMF.pure (some b)

def generated (b : Bool) : PMF (State × State) :=
  generatedAmbientPrefix model observe feedback initial safe 1 survival_one_pos
    (fallback b) (outside b) 1

private def conditioned : PMF (State × State) :=
  actualConditionedPrefix model observe feedback initial safe 1 0 survival_one_pos

private theorem conditioned_eq_pure :
    conditioned = PMF.pure ((some false, some true) : State × State) := by
  apply PMF.ext
  intro h
  rcases h with ⟨x, y⟩
  cases x with
  | none =>
      have hz : conditioned (none, y) = 0 :=
        actual_conditioned_prefix_eq_zero_of_not_survives model observe feedback initial
          safe 1 0 survival_one_pos (none, y) (fun hs => hs.1 rfl)
      rw [hz]
      simp [PMF.pure_apply]
  | some b =>
      cases y with
      | none =>
          have hz : conditioned (some b, none) = 0 :=
            actual_conditioned_prefix_eq_zero_of_not_survives model observe feedback initial
              safe 1 0 survival_one_pos (some b, none) (fun hs => hs.2 rfl)
          rw [hz]
          simp [PMF.pure_apply]
      | some c =>
          apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
            (PMF.apply_ne_top _ _)).mp
          have hc := actual_conditioned_safe_path_mass model observe feedback initial safe
            1 survival_one_pos (safeEquiv b, safeEquiv c)
          change (conditioned (some b, some c)).toReal =
            (safeInitialRow initial safe (safeEquiv b) *
              killed (safeEquiv b) (safeEquiv c)) /
                actualSurvivalMass model observe feedback initial safe 1 at hc
          rw [initial_safe_mass, killed_entry, survival_one] at hc
          cases b <;> cases c <;> norm_num [PMF.pure_apply] at hc ⊢ <;> exact hc

private theorem generated_eq_pure (b : Bool) :
    generated b = PMF.pure ((some false, some true) : State × State) := by
  have hs := generated_ambient_eq_actual model observe feedback initial safe
    1 0 survival_one_pos (fallback b) (outside b)
  exact hs.trans conditioned_eq_pure

private theorem null_rows_differ :
    totalWindowRow killed killed_nonneg (fallback false) 0 (safeEquiv true) ≠
      totalWindowRow killed killed_nonneg (fallback true) 0 (safeEquiv true) := by
  have hnull : ¬ 0 < remainingSurvival killed (0 + 1) (safeEquiv true) := by
    rw [remaining_one]
    norm_num
  simp only [totalWindowRow, dif_neg hnull, fallback]
  intro heq
  have ha := congrArg (fun p : PMF safe => p (safeEquiv false)) heq
  norm_num [PMF.pure_apply, safeEquiv] at ha

/-- Nonvacuous original-source witness: the conditioned event is positive,
one safe row is null, the two total rows differ there, but both complete
generated path laws coincide with the same actual point-mass path. -/
theorem null_row_actual_source_witness :
    (initial none).toReal = 1 / 3 ∧
    actualSurvivalMass model observe feedback initial safe 1 = 1 / 3 ∧
    remainingSurvival killed 1 (safeEquiv true) = 0 ∧
    totalWindowRow killed killed_nonneg (fallback false) 0 (safeEquiv true) ≠
      totalWindowRow killed killed_nonneg (fallback true) 0 (safeEquiv true) ∧
    generated false = PMF.pure ((some false, some true) : State × State) ∧
    generated true = PMF.pure ((some false, some true) : State × State) := by
  exact ⟨initial_unsafe_mass, survival_one, remaining_one true, null_rows_differ,
    generated_eq_pure false, generated_eq_pure true⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TotalFiniteWindowWitnessCheck
