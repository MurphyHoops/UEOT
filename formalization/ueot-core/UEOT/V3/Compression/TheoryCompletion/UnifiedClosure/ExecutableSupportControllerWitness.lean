import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ExecutableSupportController

/-!
# Executable synthesis with a real failure state

This extends the existing hidden Boolean flip with an explicit absorbing failure
state. A matching action flips the safe Boolean state; a mismatched action fails.
The observation is constant, so correct behavior needs the synthesized memory.
The safe set is proper. Initialization, action selection and update are actual
finite computations; the probability model below interprets that same table.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace ExecutableSupportControllerWitness

open MeasureTheory UEOT.V3.PathError SupportViabilityClosure
open ExecutableSupportSynthesis

/-- The same constant observation is executable, even outside safe states. -/
def observe (_x : Option Bool) : Unit := ()

/-- A correct action advances the hidden phase; an incorrect one is fatal. -/
def nextState : Option Bool → Bool → Option Bool
  | none, _ => none
  | some b, a => if a = b then some (!b) else none

def relation (x : Option Bool) (a : Bool) (z : Option Bool) : Prop :=
  z = nextState x a

def certification (x : Option Bool) (a : Bool) : Prop := x = some a

instance (x : Option Bool) (a : Bool) (z : Option Bool) :
    Decidable (relation x a z) := inferInstanceAs (Decidable (z = nextState x a))

instance (x : Option Bool) (a : Bool) : Decidable (certification x a) :=
  inferInstanceAs (Decidable (x = some a))

def initialTable : Finset (Option Bool) := {some false}

def mixedTable : Finset (Option Bool) := {some false, some true}

def actionOrder : List Bool := [false, true]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16384 in
/-- These are the real existing checker computations, not source-support guesses. -/
theorem finite_input_checks :
    finiteMemoryCheck observe relation certification initialTable = true ∧
      finiteMemoryCheck observe relation certification mixedTable = false := by
  decide

/-- A concrete executable output, with its initialization, action and update. -/
def program : Program (Option Bool) Unit Bool :=
  buildProgram observe relation certification initialTable actionOrder false

theorem synthesis_returns_program :
    synthesize observe relation certification initialTable actionOrder false =
      some program := by
  apply (synthesize_eq_some_iff observe relation certification
    initialTable actionOrder false program).mpr
  exact ⟨by decide, by decide, finite_input_checks.1, rfl⟩

/-- Ambiguous source phase, incomplete actions and empty initial data are rejected. -/
theorem synthesis_rejections :
    (synthesize observe relation certification mixedTable actionOrder false).isSome = false ∧
      (synthesize observe relation certification initialTable [false] false).isSome = false ∧
      (synthesize observe relation certification (∅ : Finset (Option Bool))
        actionOrder false).isSome = false := by
  decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16384 in
/-- The runtime action sequence comes from its computed memory, not a clock. -/
theorem computed_flip_steps :
    program.initialMemory () = {some false} ∧
      program.action {some false} = false ∧
      program.update {some false} false () = {some true} ∧
      program.action {some true} = true ∧
      program.update {some true} true () = {some false} := by
  decide

private theorem empty_memory_uses_fallback :
    selectedAction observe relation certification actionOrder true
      (∅ : Finset (Option Bool)) = true := by
  decide

def freeRelation (_x : Unit) (_a : Bool) (_z : Unit) : Prop := True

def freeCertification (_x : Unit) (_a : Bool) : Prop := True

instance (x : Unit) (a : Bool) (z : Unit) : Decidable (freeRelation x a z) :=
  isTrue trivial

instance (x : Unit) (a : Bool) : Decidable (freeCertification x a) :=
  isTrue trivial

/-- When both actions win, only the explicitly supplied order fixes the output. -/
theorem action_order_is_effective :
    selectedAction (fun _ : Unit => ()) freeRelation freeCertification
        [false, true] false ({()} : Finset Unit) = false ∧
      selectedAction (fun _ : Unit => ()) freeRelation freeCertification
        [true, false] false ({()} : Finset Unit) = true := by
  decide

noncomputable section

open UEOT.V3.FiniteDiscountedControl UEOT.V3.QSDPerron
open FiniteMemoryRealization SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open scoped Classical BigOperators

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSpace (Finset (Option Bool)) := ⊤

def initialLaw : PMF (Option Bool) := PMF.pure (some false)

def source (_n : ℕ) (x : Option Bool) (a : Bool) : PMF (Option Bool) :=
  PMF.pure (nextState x a)

def certified (_n : ℕ) (x : Option Bool) (a : Bool) : Prop := certification x a

def safe : Set (Option Bool) := {x | x ≠ none}

theorem initial_support_exact (x : Option Bool) :
    x ∈ initialTable ↔ x ∈ initialLaw.support := by
  simp [initialTable, initialLaw, PMF.support_pure]

theorem source_support_exact (n : ℕ) (x : Option Bool) (a : Bool) (z : Option Bool) :
    z ∈ (source n x a).support ↔ relation x a z := by
  simp [source, relation, PMF.support_pure]

theorem safe_is_nonempty_proper : safe.Nonempty ∧ safe ≠ Set.univ := by
  constructor
  · exact ⟨some false, by simp [safe]⟩
  · intro h
    have hn : (none : Option Bool) ∈ safe := h ▸ Set.mem_univ none
    exact hn rfl

theorem initial_safe : ∀ x ∈ initialLaw.support, x ∈ safe := by
  intro x hx
  have heq : x = some false := by simpa [initialLaw, PMF.support_pure] using hx
  simp [heq, safe]

theorem certified_transition_safe :
    ∀ n x a, x ∈ safe → certified n x a →
      ∀ z ∈ (source n x a).support, z ∈ safe := by
  intro n x a _ hcert z hz
  have hx : x = some a := hcert
  subst x
  have hz' : z = some (!a) := by simpa [source, nextState, PMF.support_pure] using hz
  simp [hz', safe]

/-- The actual returned program has zero uncertified occupancy at every time. -/
theorem returned_program_zero_uncovered :
    ∀ n, (coverageDeploymentRowLaw initialLaw observe source
      program.toController.policy n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 0 := by
  exact synthesize_some_zero_uncovered observe relation certification
    initialTable actionOrder false initialLaw source certified program
    synthesis_returns_program initial_support_exact source_support_exact
    (fun _ _ _ => Iff.rfl)

/-- Physical safety is nonvacuous: the same executable program avoids the
proper failure state in its own actual infinite trajectory law. -/
theorem returned_program_all_times_safe :
    FiniteMemoryPhysicalSafety.stateTrajMeasure program.toController
      initialLaw observe source {ω | ∀ n : ℕ, ω n ∈ safe} = 1 := by
  apply synthesize_some_all_times_physical_safe observe relation certification
    initialTable actionOrder false initialLaw source certified program
    synthesis_returns_program initial_support_exact source_support_exact
    (fun _ _ _ => Iff.rfl) safe initial_safe
  intro x a hx hc z hz
  exact certified_transition_safe 0 x a hx hc z ((source_support_exact 0 x a z).mpr hz)

/-- The numerical model interprets exactly the same runtime next-state function.
Its reward is zero and is unused by the safety and survival conclusions. -/
def model : Model (Option Bool) (fun _ => Bool) where
  transition := fun x a z => (source 0 x a z).toReal
  reward := fun _ _ => 0
  rewardBound := 0
  discount := 1 / 2
  transition_nonneg := fun _ _ _ => ENNReal.toReal_nonneg
  transition_sum_one := fun x a => coverage_sum_toReal (source 0 x a)
  reward_abs_le := by intros; simp
  discount_pos := by norm_num
  discount_lt_one := by norm_num

theorem model_support_exact (x : Option Bool) (a : Bool) (z : Option Bool) :
    z ∈ (model.transitionPMF x a).support ↔ relation x a z := by
  have heq : model.transitionPMF x a = source 0 x a := by
    apply PMF.ext
    intro y
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    rw [Model.transitionPMF_apply_toReal]
    rfl
  rw [heq]
  exact source_support_exact 0 x a z

noncomputable local instance pairDecidableEq :
    DecidableEq (Option Bool × Finset (Option Bool)) := Classical.decEq _

/-- The same synthesized program and the same numerical source have unit
killed survival mass at every horizon, with the proper safe set retained. -/
theorem actual_killed_mass_one (n : ℕ) :
    ∑ v : (Prod.fst ⁻¹' safe : Set (Option Bool × Finset (Option Bool))),
      rowApply (safeInitialRow (augmentedInitial program.toController initialLaw observe)
        (Prod.fst ⁻¹' safe))
        ((killedMatrix
          (HomogeneousMemorySurvival.augmentedModel model program.toController observe)
          (liftedStationaryPolicy Prod.snd program.toController.action)
          (Prod.fst ⁻¹' safe)) ^ n) v = 1 := by
  apply synthesize_some_killed_mass_one observe relation certification initialTable
    actionOrder false initialLaw model certified program synthesis_returns_program
    initial_support_exact model_support_exact (fun _ _ _ => Iff.rfl) safe initial_safe
  intro x a hx hc z hz
  exact certified_transition_safe 0 x a hx hc z ((source_support_exact 0 x a z).mpr hz)

def mixedLaw : PMF (Option Bool) := (PMF.uniformOfFintype Bool).map some

private theorem mixed_support_exact (x : Option Bool) :
    x ∈ mixedTable ↔ x ∈ mixedLaw.support := by
  cases x with
  | none => simp [mixedTable, mixedLaw]
  | some b => cases b <;> simp [mixedTable, mixedLaw]

/-- With the same source and both safe phases initially possible, no complete
causal policy can certify every row. Synthesis rejection is a real boundary. -/
theorem mixed_initial_has_no_all_times_policy :
    ¬ ∃ π : ∀ n, CausalHistory Unit (Bool × Unit) n → PMF Bool,
      ∀ n, (coverageDeploymentRowLaw mixedLaw observe source π n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 0 := by
  rintro ⟨π, hzero⟩
  have haccept := (synthesize_isSome_iff_exists_all_times_policy
    observe relation certification mixedTable actionOrder false mixedLaw source certified
    (by decide) mixed_support_exact source_support_exact (fun _ _ _ => Iff.rfl)).mpr
      ⟨π, hzero⟩
  rw [synthesis_rejections.1] at haccept
  cases haccept

end

end ExecutableSupportControllerWitness
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
