import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPolicy
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourcePolicyPathBridge

/-!
# Two states of memory strictly improve constant-observation control

The source starts at `false` and flips its Boolean state after every action.
The observation is constant, and a row is certified exactly when its action
equals the current state. A homogeneous Boolean-memory controller certifies
every actual row. For every fixed randomized current-observation feedback,
the actual uncertified occupancies at times zero and one sum to one.

The memory update is a fixed Boolean function, not access to an unbounded
external clock. All probabilities below use the existing actual source
deployment row law, with the same initial law and transition sequence.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace FiniteMemorySeparation

open MeasureTheory UEOT.V3.PathError SupportViabilityClosure
open scoped BigOperators Classical

noncomputable section

local instance : MeasurableSpace Bool := ⊤

def initial : PMF Bool := PMF.pure false

def observe (_x : Bool) : Unit := ()

def source (_n : ℕ) (x _a : Bool) : PMF Bool := PMF.pure (!x)

def certified (_n : ℕ) (x a : Bool) : Prop := a = x

/-- A complete autonomous controller with exactly two possible memories.
Its update and action have no time or complete-history argument. -/
def flipController : FiniteMemoryController Bool Unit Bool where
  initialMemory := fun _ => false
  action := PMF.pure
  update := fun m _ _ => !m

/-- In this deterministic source, every complete observed record has the
singleton source trace prescribed by the controller's recursive memory.
In particular this is true on the actual positive-mass records. -/
theorem trace_support_eq_memory_singleton :
    ∀ n (h : CausalHistory Unit (Bool × Unit) n),
      traceSupport initial observe source n h =
        {flipController.memory n h} := by
  intro n
  induction n with
  | zero =>
      intro h
      change Unit at h
      have hh : h = () := Subsingleton.elim _ _
      subst h
      ext x
      simp [traceSupport, initialSupport, initial, observe,
        flipController, FiniteMemoryController.memory, PMF.support_pure]
  | succ n ih =>
      rintro ⟨h, a, y⟩
      have hy : y = () := Subsingleton.elim _ _
      subst y
      change successorSupport observe source n
          (traceSupport initial observe source n h) a () =
        {!(flipController.memory n h)}
      rw [ih h]
      ext x
      simp [successorSupport, source, observe, PMF.support_pure]

/-- This concrete two-memory controller has zero uncertified occupancy at
every time under its own actual source experiment. -/
theorem flip_controller_zero_uncovered (n : ℕ) :
    (coverageDeploymentRowLaw initial observe source
      flipController.policy n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 0 := by
  apply (zero_uncovered_iff_support_certified
    initial observe source flipController.policy certified n).mpr
  intro h _hh a ha x hx
  have haeq : a = flipController.memory n h := by
    change a ∈ (PMF.pure (flipController.memory n h)).support at ha
    simpa only [PMF.support_pure, Set.mem_singleton_iff] using ha
  have hxeq : x = flipController.memory n h := by
    rw [trace_support_eq_memory_singleton] at hx
    exact hx
  exact haeq.trans hxeq.symm

/-- One fixed action PMF at every complete observation history. This is
exactly the current-observation stationary feedback class for `Unit`. -/
def stationaryPolicy (ρ : PMF Bool) (n : ℕ)
    (_h : CausalHistory Unit (Bool × Unit) n) : PMF Bool := ρ

private theorem stationary_uncovered_of_supported_state
    (ρ : PMF Bool) (n : ℕ) (x : Bool)
    (hstate : ∀ h ∈ (microLaw initial observe source (stationaryPolicy ρ) n).support,
      riskLastState n h = x) :
    (coverageDeploymentRowLaw initial observe source
      (stationaryPolicy ρ) n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = (ρ (!x)).toReal := by
  rw [← coverage_uncovered_indicator_expectation,
    coverage_rowLaw_expectation]
  calc
    _ = ∑ h, (microLaw initial observe source (stationaryPolicy ρ) n h).toReal *
        (ρ (!x)).toReal := by
      apply Finset.sum_congr rfl
      intro h _
      by_cases hh : h ∈ (microLaw initial observe source (stationaryPolicy ρ) n).support
      · have hlast := hstate h hh
        cases x <;> simp [stationaryPolicy, certified, hlast, Fintype.sum_bool]
      · have hz : microLaw initial observe source (stationaryPolicy ρ) n h = 0 := by
          by_contra hne
          exact hh ((PMF.mem_support_iff _ _).mpr hne)
        simp only [hz, ENNReal.zero_toReal, zero_mul]
    _ = _ := by
      rw [← Finset.sum_mul, coverage_sum_toReal, one_mul]

/-- At time zero the source state is `false`, so only action `true` is
uncertified. The mass is computed in the actual deployed row law. -/
theorem stationary_uncovered_zero (ρ : PMF Bool) :
    (coverageDeploymentRowLaw initial observe source
      (stationaryPolicy ρ) 0).toMeasure.real
        {xa | ¬ certified 0 xa.1 xa.2} = (ρ true).toReal := by
  apply stationary_uncovered_of_supported_state ρ 0 false
  intro h hh
  change h ∈ (PMF.pure false).support at hh
  change h = false
  simpa only [PMF.support_pure, Set.mem_singleton_iff] using hh

/-- At time one the same source is at `true`, independently of both
randomized actions, so the uncertified mass is now the action-`false` mass. -/
theorem stationary_uncovered_one (ρ : PMF Bool) :
    (coverageDeploymentRowLaw initial observe source
      (stationaryPolicy ρ) 1).toMeasure.real
        {xa | ¬ certified 1 xa.1 xa.2} = (ρ false).toReal := by
  apply stationary_uncovered_of_supported_state ρ 1 true
  rintro ⟨b, a, z⟩ hh
  have hs := (mem_microLaw_succ_support_iff
    initial observe source (stationaryPolicy ρ) 0 b a z).mp hh
  have hb_support := hs.1
  change b ∈ (PMF.pure false).support at hb_support
  have hb : b = false := by
    simpa only [PMF.support_pure, Set.mem_singleton_iff] using hb_support
  have hz_support := hs.2.2
  change z ∈ (PMF.pure (!b)).support at hz_support
  have hz : z = !b := by
    simpa only [PMF.support_pure, Set.mem_singleton_iff] using hz_support
  change z = true
  simpa only [hb, Bool.not_false] using hz

/-- Randomization cannot repair the missing memory: the same fixed action
PMF incurs total uncertified occupancy exactly one in its first two rows. -/
theorem stationary_uncovered_zero_add_one (ρ : PMF Bool) :
    (coverageDeploymentRowLaw initial observe source
      (stationaryPolicy ρ) 0).toMeasure.real
        {xa | ¬ certified 0 xa.1 xa.2} +
      (coverageDeploymentRowLaw initial observe source
        (stationaryPolicy ρ) 1).toMeasure.real
          {xa | ¬ certified 1 xa.1 xa.2} = 1 := by
  rw [stationary_uncovered_zero, stationary_uncovered_one]
  simpa [Fintype.sum_bool, add_comm] using coverage_sum_toReal ρ

private theorem observation_feedback_eq_stationary
    (σ : Unit → PMF Bool) :
    SourcePolicyPathBridgeCheck.observationMarkovPolicy σ =
      stationaryPolicy (σ ()) := by
  funext n h
  change σ (riskLastState n h) = σ ()
  congr 1

/-- No time-homogeneous randomized current-observation feedback certifies
both initial rows of this source. The quantifier includes every action PMF. -/
theorem stationary_feedback_cannot_certify_two_rows
    (σ : Unit → PMF Bool) :
    ¬ ((coverageDeploymentRowLaw initial observe source
        (SourcePolicyPathBridgeCheck.observationMarkovPolicy σ) 0).toMeasure.real
          {xa | ¬ certified 0 xa.1 xa.2} = 0 ∧
      (coverageDeploymentRowLaw initial observe source
        (SourcePolicyPathBridgeCheck.observationMarkovPolicy σ) 1).toMeasure.real
          {xa | ¬ certified 1 xa.1 xa.2} = 0) := by
  rw [observation_feedback_eq_stationary]
  rintro ⟨hzero, hone⟩
  have hsum := stationary_uncovered_zero_add_one (σ ())
  rw [hzero, hone] at hsum
  norm_num at hsum

end
end FiniteMemorySeparation
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
