import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteWindowDoob
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceQSDBinding

/-!
# A three-state source separates finite-window conditioning from fixed Doob paths

The original controlled model has two safe states and one absorbing cemetery.
Its actual killed matrix, original initial law, QSD relation and positive right
vector all feed the same-source path APIs. Exact rational arithmetic gives
TV = 1/4 at horizon one, despite the genuine left QSD.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteWindowDoobWitnessCheck

open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open UEOT.V3.QSDPerron
open SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open SameSourceConditionedTerminalCheck SameSourceQSDBindingCheck
open SameSourceFiniteWindowCheck FiniteWindowDoobCheck
open UEOT.V3.Compression.PositiveEigenstructure (RightEigenData colApply)
open scoped BigOperators Classical

noncomputable section

abbrev State := Option Bool
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Unit := ⊤

/-- `none` is the cemetery; `some false` and `some true` are the safe states. -/
def safe : Set State := {x | x ≠ none}

def safeEquiv : Bool ≃ safe where
  toFun b := ⟨some b, by simp [safe]⟩
  invFun v := match v with
    | ⟨none, h⟩ => False.elim (h rfl)
    | ⟨some b, _⟩ => b
  left_inv b := rfl
  right_inv v := by
    rcases v with ⟨_ | b, h⟩
    · exact False.elim (h rfl)
    · rfl

private theorem sum_safe (f : safe → ℝ) :
    (∑ v : safe, f v) = f (safeEquiv false) + f (safeEquiv true) := by
  simpa [Fintype.sum_bool, add_comm] using (safeEquiv.sum_comp f).symm

/-- A complete stochastic matrix on the original three states. -/
def transition : State → Unit → State → ℝ
  | none, _, none => 1
  | none, _, some _ => 0
  | some false, _, none => 1 / 4
  | some false, _, some _ => 3 / 8
  | some true, _, none => 3 / 4
  | some true, _, some _ => 1 / 8

def model : Model State (fun _ => Unit) where
  transition := transition
  reward := fun _ _ => 0
  rewardBound := 1
  discount := 1 / 2
  transition_nonneg := by
    intro x a y
    fin_cases x <;> fin_cases y <;> norm_num [transition]
  transition_sum_one := by
    intro x a
    fin_cases x <;> norm_num [transition, Fintype.sum_option, Fintype.sum_bool]
  reward_abs_le := by intros; norm_num
  discount_pos := by norm_num
  discount_lt_one := by norm_num

def observe (_ : State) : Unit := ()
def feedback (_ : Unit) : PMF Unit := PMF.pure ()
def safeLaw : PMF safe := (PMF.uniformOfFintype Bool).map safeEquiv
/-- The original initial PMF, with no cemetery mass. -/
def initial : PMF State := safeLaw.map Subtype.val
/-- This is the restriction of the actual feedback-induced model matrix. -/
def killed : Matrix safe safe ℝ :=
  killedMatrix model (liftedStationaryPolicy observe feedback) safe

@[simp] theorem safeLaw_mass (b : Bool) :
    (safeLaw (safeEquiv b)).toReal = 1 / 2 := by
  unfold safeLaw
  rw [pmf_map_injective_atom safeEquiv safeEquiv.injective]
  norm_num [PMF.uniformOfFintype_apply]

@[simp] theorem initial_safe_mass (b : Bool) :
    safeInitialRow initial safe (safeEquiv b) = 1 / 2 := by
  change safeInitialRow (safeLaw.map Subtype.val) safe (safeEquiv b) = _
  rw [safeInitialRow_map_subtype]
  exact safeLaw_mass b

@[simp] theorem killed_entry (i j : Bool) :
    killed (safeEquiv i) (safeEquiv j) = if i then 1 / 8 else 3 / 8 := by
  cases i <;> cases j <;>
    norm_num [killed, killedMatrix, policyMatrix, Model.policyTransition,
      liftedStationaryPolicy, observe, feedback, model, transition, safeEquiv]

/-- The uniform safe law really is a left QSD of this source, with rho = 1/2. -/
theorem source_left_qsd (j : safe) :
    rowApply (fun i => (safeLaw i).toReal) killed j = (1 / 2) * (safeLaw j).toReal := by
  rcases safeEquiv.surjective j with ⟨b, rfl⟩
  unfold rowApply
  rw [sum_safe]
  simp only [safeLaw_mass, killed_entry]
  norm_num

/-- Actual original survival, inherited from the same-source QSD identity. -/
theorem actual_survival (T : ℕ) :
    actualSurvivalMass model observe feedback initial safe T = (1 / 2) ^ T := by
  exact actual_qsd_survival_mass model observe feedback safe safeLaw (1 / 2)
    source_left_qsd T

private theorem actual_survival_one_pos :
    0 < actualSurvivalMass model observe feedback initial safe (1 + 0) := by
  rw [actual_survival]
  norm_num

/-- Right data normalized so that the actual initial pairing is one. -/
def rightVector (i : safe) : ℝ := if safeEquiv.symm i then 1 / 2 else 3 / 2

def rightData : RightEigenData killed where
  scale := 1 / 2
  vector := rightVector
  scale_pos := by norm_num
  vector_pos := by
    intro i
    rcases safeEquiv.surjective i with ⟨b, rfl⟩
    cases b <;> norm_num [rightVector, safeEquiv]
  eigen := by
    intro i
    rcases safeEquiv.surjective i with ⟨b, rfl⟩
    unfold colApply
    rw [sum_safe]
    cases b <;> norm_num [killed_entry, rightVector, safeEquiv]

@[simp] theorem actual_initial_pairing :
    initialPairing (safeInitialRow initial safe) rightData.vector = 1 := by
  unfold initialPairing
  rw [sum_safe]
  norm_num [initial_safe_mass, rightData, rightVector, safeEquiv]

private theorem initial_pairing_pos :
    0 < initialPairing (safeInitialRow initial safe) rightData.vector := by
  rw [actual_initial_pairing]
  norm_num

/-- The real original path law conditioned on survival through time one. -/
def conditionedPair : PMF (State × State) :=
  actualConditionedPrefix model observe feedback initial safe 1 0 actual_survival_one_pos

private theorem killed_nonneg (i j : safe) : 0 ≤ killed i j :=
  killedMatrix_nonneg model (liftedStationaryPolicy observe feedback) safe i j

/-- The actual Doob PMF path uses this same killed matrix and original initial row. -/
def safeDoobPair : PMF (safe × safe) :=
  doobPathLaw rightData
    killed_nonneg
    (safeInitialRow initial safe) (safeInitialRow_nonneg initial safe)
    initial_pairing_pos 1

def embedPair (h : safe × safe) : State × State := (h.1.val, h.2.val)
def doobPair : PMF (State × State) := safeDoobPair.map embedPair

private theorem embedPair_injective : Function.Injective embedPair := by
  intro h g heq
  exact Prod.ext (Subtype.ext (congrArg Prod.fst heq))
    (Subtype.ext (congrArg Prod.snd heq))

/-- Conditional pair rows are (3/8,3/8) and (1/8,1/8). -/
theorem conditioned_safe_atom (i j : Bool) :
    (conditionedPair (some i, some j)).toReal = if i then 1 / 8 else 3 / 8 := by
  have h := actual_conditioned_safe_path_mass model observe feedback initial safe
    1 actual_survival_one_pos (safeEquiv i, safeEquiv j)
  change (conditionedPair (some i, some j)).toReal = _ at h
  rw [actual_survival] at h
  simpa [matrixPathWeight, currentState, initial_safe_mass, killed_entry,
    killed, safeEquiv] using h

/-- Doob pair rows are (9/16,3/16) and (3/16,1/16). -/
theorem doob_safe_atom (i j : Bool) :
    (doobPair (some i, some j)).toReal =
      (if i then 1 / 4 else 3 / 4) * (if j then 1 / 4 else 3 / 4) := by
  change ((safeDoobPair.map embedPair) (embedPair (safeEquiv i, safeEquiv j))).toReal = _
  rw [pmf_map_injective_atom embedPair embedPair_injective]
  unfold safeDoobPair
  rw [doob_path_atom]
  cases i <;> cases j <;>
    norm_num [matrixPathWeight, currentState, initial_safe_mass, killed_entry,
      actual_initial_pairing, rightData, rightVector, safeEquiv]

@[simp] theorem doob_cemetery_left (y : State) : doobPair (none, y) = 0 := by
  unfold doobPair
  rw [PMF.map_apply]
  apply tsum_eq_zero
  intro h
  apply if_neg
  intro heq
  exact h.1.property (congrArg Prod.fst heq)

@[simp] theorem doob_cemetery_right (x : State) : doobPair (x, none) = 0 := by
  unfold doobPair
  rw [PMF.map_apply]
  apply tsum_eq_zero
  intro h
  apply if_neg
  intro heq
  exact h.2.property (congrArg Prod.snd heq)

@[simp] theorem conditioned_cemetery_left (y : State) : conditionedPair (none, y) = 0 := by
  apply actual_conditioned_prefix_eq_zero_of_not_survives model observe feedback initial
    safe 1 0 actual_survival_one_pos (none, y)
  simp [stateSurvives, safe]

@[simp] theorem conditioned_cemetery_right (x : State) : conditionedPair (x, none) = 0 := by
  apply actual_conditioned_prefix_eq_zero_of_not_survives model observe feedback initial
    safe 1 0 actual_survival_one_pos (x, none)
  simp [stateSurvives, safe]

/-- A genuine left QSD does not identify the complete finite-window conditional
path with the stationary Doob path, even with its natural tilted initial law. -/
theorem actual_conditioned_doob_tv :
    tvDist conditionedPair.toMeasure doobPair.toMeasure = 1 / 4 := by
  rw [tvDist_eq_one_sub_pmfCommonMass]
  simp only [pmfCommonMass, Fintype.sum_prod_type, Fintype.sum_option,
    Fintype.sum_bool, conditioned_cemetery_left, conditioned_cemetery_right,
    doob_cemetery_left, doob_cemetery_right, conditioned_safe_atom, doob_safe_atom]
  norm_num

/-- Nonidentity is witnessed in the original three-state experiment. -/
theorem actual_conditioned_ne_doob : conditionedPair ≠ doobPair := by
  intro h
  have htv := actual_conditioned_doob_tv
  rw [h, tvDist_self_eq_zero] at htv
  norm_num at htv

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteWindowDoobWitnessCheck
