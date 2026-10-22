import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPhysicalSafety

/-!
# Actual-source witnesses for the two physical safety premises

The state is Boolean, the observation is constant, and the controller has
one memory and one action. The safe set is the proper, nonempty set {false}.
Every row is certified, so every original deployment row has zero uncertified
occupancy, regardless of the initial state and successor chosen below.

Starting at false and returning false is physically safe at all times.
Returning true instead preserves initial safety but makes actual safety at
time one, hence at all times, have probability zero. Starting at true and
returning false preserves certified transition closure but makes actual
safety at time zero, hence at all times, have probability zero.

The masses are obtained through the proved actual coordinate-law identity.
No event mass, path agreement, or safety conclusion is stipulated as data.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace FiniteMemorySafetyWitness

open MeasureTheory UEOT.V3.PathError SupportViabilityClosure
open FiniteMemoryPhysicalSafety
open scoped Classical

noncomputable section

local instance : MeasurableSpace Bool := ⊤

def observe (_x : Bool) : Unit := ()

def controller : FiniteMemoryController Unit Unit Unit where
  initialMemory := fun _ => ()
  action := fun _ => PMF.pure ()
  update := fun _ _ _ => ()

def source (next : Bool) (_n : ℕ) (_x : Bool) (_a : Unit) : PMF Bool :=
  PMF.pure next

def certified (_n : ℕ) (_x : Bool) (_a : Unit) : Prop := True

def safe : Set Bool := {false}

/-- The physical set is proper and nonempty. -/
theorem safe_is_proper_nonempty : safe.Nonempty ∧ safe ≠ Set.univ := by
  constructor
  · exact ⟨false, rfl⟩
  · intro h
    have ht : true ∈ safe := by
      rw [h]
      exact Set.mem_univ true
    change (true : Bool) = false at ht
    cases ht

/-- Zero uncertified occupancy holds in every actual deployment row of
every source in this family, independently of its physical behavior. -/
theorem all_rows_zero_uncovered (initial next : Bool) (n : ℕ) :
    (coverageDeploymentRowLaw (PMF.pure initial) observe (source next)
      controller.policy n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 0 := by
  apply (zero_uncovered_iff_support_certified
    (PMF.pure initial) observe (source next) controller.policy certified n).mpr
  intro _ _ _ _ _ _
  trivial

theorem initial_false_safe :
    ∀ x ∈ (PMF.pure false : PMF Bool).support, x ∈ safe := by
  intro x hx
  simpa only [PMF.support_pure, safe] using hx

/-- Returning false satisfies the actual certified-support closure
independently of the original initial state. -/
theorem source_false_preserves_safe :
    ∀ n x a, x ∈ safe → certified n x a →
      ∀ z ∈ (source false n x a).support, z ∈ safe := by
  intro n x a _ _ z hz
  simpa only [source, PMF.support_pure, safe] using hz

/-- A nonempty actual source with a proper safe set satisfies the positive
physical-safety endpoint, using both physical premises. -/
theorem safe_source_all_times_mass_one :
    stateTrajMeasure controller (PMF.pure false) observe (source false)
      {ω | ∀ n : ℕ, ω n ∈ safe} = 1 := by
  exact controller_all_times_physical_safe controller (PMF.pure false)
    observe (source false) certified safe initial_false_safe
    source_false_preserves_safe (all_rows_zero_uncovered false false)

/-- With the same safe initial state and zero uncertified occupancy,
changing the actual successor to true makes time-one physical safety zero. -/
theorem unsafe_transition_time_one_mass_zero :
    stateTrajMeasure controller (PMF.pure false) observe (source true)
      {ω | ω 1 ∈ safe} = 0 := by
  rw [stateTrajMeasure_coordinate_mass]
  let p : PMF (CausalHistory Bool (Unit × Bool) 1) :=
    microLaw (PMF.pure false) observe (source true) controller.policy 1
  change p.toMeasure {h | riskLastState 1 h ∈ safe} = 0
  apply (p.toMeasure_apply_eq_zero_iff (Set.toFinite _).measurableSet).mpr
  apply Set.disjoint_left.mpr
  rintro ⟨x, a, z⟩ hh hs
  have hparts := (mem_microLaw_succ_support_iff (PMF.pure false)
    observe (source true) controller.policy 0 x a z).mp hh
  have hz : z = true := by
    simpa only [source, PMF.support_pure, Set.mem_singleton_iff] using hparts.2.2
  change z = false at hs
  cases hz.symm.trans hs

private theorem all_times_mass_le_coordinate
    (initial next : Bool) (n : ℕ) :
    stateTrajMeasure controller (PMF.pure initial) observe (source next)
        {ω | ∀ k : ℕ, ω k ∈ safe} ≤
      stateTrajMeasure controller (PMF.pure initial) observe (source next)
        {ω | ω n ∈ safe} :=
  measure_mono (fun _ h => h n)

/-- Initial physical safety and zero uncertified occupancy do not imply
all-times physical safety without certified transition closure. -/
theorem unsafe_transition_all_times_mass_zero :
    stateTrajMeasure controller (PMF.pure false) observe (source true)
      {ω | ∀ n : ℕ, ω n ∈ safe} = 0 := by
  apply le_antisymm _ zero_le
  calc
    _ ≤ stateTrajMeasure controller (PMF.pure false) observe (source true)
        {ω | ω 1 ∈ safe} := all_times_mass_le_coordinate false true 1
    _ = 0 := unsafe_transition_time_one_mass_zero

/-- Keeping certified transition closure and zero uncertified occupancy,
an unsafe original initial state gives time-zero physical safety zero. -/
theorem unsafe_initial_time_zero_mass_zero :
    stateTrajMeasure controller (PMF.pure true) observe (source false)
      {ω | ω 0 ∈ safe} = 0 := by
  rw [stateTrajMeasure_coordinate_mass]
  change (PMF.pure true : PMF Bool).toMeasure safe = 0
  apply ((PMF.pure true : PMF Bool).toMeasure_apply_eq_zero_iff
    (Set.toFinite safe).measurableSet).mpr
  apply Set.disjoint_left.mpr
  intro x hx hs
  have hxtrue : x = true := by
    simpa only [PMF.support_pure, Set.mem_singleton_iff] using hx
  change x = false at hs
  cases hxtrue.symm.trans hs

/-- Certified transitions may immediately repair the state, but they do
not erase failure at time zero from the original all-times event. -/
theorem unsafe_initial_all_times_mass_zero :
    stateTrajMeasure controller (PMF.pure true) observe (source false)
      {ω | ∀ n : ℕ, ω n ∈ safe} = 0 := by
  apply le_antisymm _ zero_le
  calc
    _ ≤ stateTrajMeasure controller (PMF.pure true) observe (source false)
        {ω | ω 0 ∈ safe} := all_times_mass_le_coordinate true false 0
    _ = 0 := unsafe_initial_time_zero_mass_zero

end
end FiniteMemorySafetyWitness
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
