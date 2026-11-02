import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SafeRewardConflictWitness
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OrganizationalSufficiencyWitness
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSupportViability
import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.JointRecovery

/-!
# Same nonzero-reward source: terminal partition and two organizational clocks
P-ALG uses conflictRewardControl.micro's actual reward. Two JointRecovery ticks
restore the explicit corrupted representation and then execute its own program
through that same physical source; they are not two physical ticks.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictOrganizationalSource
open UEOT.V3.FiniteDiscountedControl UEOT.V3.FiniteStablePartition
open UEOT.V3.Compression.RecursiveSufficientState
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.ViabilityKernel UEOT.V3.PathError
open scoped BigOperators
noncomputable section
abbrev State := Bool × Bool
def M := conflictRewardControl.micro
def P (x : State) (a : Bool) : PMF State := M.transitionPMF x a
def K : Set State := conflictSurvivalRegion

def registeredModel : UEOT.V3.FiniteStablePartition.Model State Bool ℝ Bool where
  transition := fun a x y => M.transition x a y
  reward := M.reward
  output := Prod.fst
  transition_nonneg := fun a x y => M.transition_nonneg x a y
  transition_sum_one := fun a x => M.transition_sum_one x a

theorem registered_reward_actual (x : State) (a : Bool) :
    registeredModel.reward x a = M.reward x a := rfl

theorem registered_transition_actual (x y : State) (a : Bool) :
    registeredModel.transition a x y = M.transition x a y := rfl

theorem registered_reward_nonzero : registeredModel.reward (true,false) false = 1 := rfl

theorem initial_relation (x y : State) :
    (initialSetoid registeredModel).r x y ↔ x.1 = y.1 := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun _ => rfl⟩

theorem initial_stable : Stable registeredModel (initialSetoid registeredModel) := by
  intro x y h a z
  rfl

theorem terminal_eq_initial : terminalSetoid registeredModel = initialSetoid registeredModel :=
  stabilize_eq_self_of_stable registeredModel (initialSetoid registeredModel) initial_stable

theorem terminal_relation (x y : State) :
    (terminalSetoid registeredModel).r x y ↔ x.1 = y.1 := by
  rw [terminal_eq_initial]
  exact initial_relation x y

/-- Registering the hidden current attribute really changes the partition,
    even with the SAME nonzero reward and physical kernel. -/
def protectedModel : UEOT.V3.FiniteStablePartition.Model State Bool ℝ State where
  transition := registeredModel.transition
  reward := registeredModel.reward
  output := id
  transition_nonneg := registeredModel.transition_nonneg
  transition_sum_one := registeredModel.transition_sum_one

theorem protected_initial_stable : Stable protectedModel (initialSetoid protectedModel) := by
  intro x y h a z
  rfl

theorem protected_terminal_relation (x y : State) :
    (terminalSetoid protectedModel).r x y ↔ x = y := by
  have he : terminalSetoid protectedModel = initialSetoid protectedModel :=
    stabilize_eq_self_of_stable protectedModel (initialSetoid protectedModel) protected_initial_stable
  rw [he]
  constructor
  · exact fun h => h.1
  · intro h; subst y; exact ⟨rfl, fun _ => rfl⟩

theorem protected_hidden_cannot_merge :
    ¬ (terminalSetoid protectedModel).r (true,false) (true,true) := by
  rw [protected_terminal_relation]
  decide

/-- The reachable subtype actually used by conflictRewardControl, not a new macro. -/
def reachableBoolEquiv : ReachableState (fun x : State => x.1) ≃ Bool where
  toFun := Subtype.val
  invFun := fun b => ⟨b, ⟨(b,false), rfl⟩⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => rfl

theorem actual_macro_read (x : State) :
    reachableBoolEquiv (conflictRewardControl.f x) = x.1 := rfl

theorem transition_real (x y : State) (a : Bool) :
    (P x a y).toReal = if y.1 = a then (1/2 : ℝ) else 0 := by
  rw [P, Model.transitionPMF_apply_toReal]
  rfl

theorem transition_support (x y : State) (a : Bool) :
    y ∈ (P x a).support ↔ y.1 = a := by
  have hz : P x a y = 0 ↔ (P x a y).toReal = 0 := by
    constructor
    · intro h; simp [h]
    · intro h
      apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) ENNReal.zero_ne_top).mp
      simpa using h
  rw [PMF.mem_support_iff, ne_eq, hz, transition_real]
  by_cases h : y.1 = a <;> simp [h]

theorem true_action_support (x : State) : (P x true).support = K := by
  ext y
  rw [transition_support]
  rfl

theorem false_action_support (x : State) : (P x false).support = Kᶜ := by
  ext y
  rw [transition_support]
  rcases y with ⟨b,u⟩
  cases b <;> simp [K, conflictSurvivalRegion]

/-- The program is independent of the hidden bit that the source resamples. -/
def substrate : TrustedRepairSubstrate Bool State Bool where
  execute := fun r _ => r

def corrupt (x : State) (controller : State → Bool) (i : Fin 3) (bad : Bool) :
    JointRepairState (X := State) (A := Bool) (Program := Bool) where
  physical := x
  controller := controller
  repairProgram := replaceProgramReplica i bad (tripleProgramEncode true)
  mode := .restoreProgram

def jointStep := jointRepairKernel substrate P

theorem first_tick_restores (x : State) (controller : State → Bool) (i : Fin 3) (bad : Bool) :
    jointStep (corrupt x controller i bad) = PMF.pure (restoredJointState substrate true x) :=
  jointRepairKernel_singleReplica_restore substrate P x controller true bad i

theorem first_tick_physical_unchanged (x : State) (controller : State → Bool) (i : Fin 3) (bad : Bool) :
    (jointStep (corrupt x controller i bad)).map JointRepairState.physical = PMF.pure x := by
  rw [first_tick_restores]
  rw [PMF.pure_map]
  rfl

theorem second_tick_actual_source (x : State) (controller : State → Bool) (i : Fin 3) (bad : Bool) :
    (jointStep (corrupt x controller i bad)).bind jointStep =
      (P x true).map (restoredJointState substrate true) := by
  rw [first_tick_restores, PMF.pure_bind]
  exact jointRepairKernel_restored substrate P true x

theorem two_tick_physical_source (x : State) (controller : State → Bool) (i : Fin 3) (bad : Bool) :
    ((jointStep (corrupt x controller i bad)).bind jointStep).map JointRepairState.physical =
      P x true := by
  rw [second_tick_actual_source, PMF.map_comp]
  change (P x true).map id = P x true
  exact PMF.map_id _

theorem true_program_valid : RepairProgramValid substrate P K true := by
  intro x hx y hy
  change y ∈ (P x true).support at hy
  rw [true_action_support] at hy
  exact hy

theorem two_tick_recovered (x : State) (controller : State → Bool) (i : Fin 3) (bad : Bool) :
    StaysIn ((jointStep (corrupt x controller i bad)).bind jointStep)
      (RecoveredJointTarget substrate K true) := by
  rw [second_tick_actual_source]
  intro s hs
  rcases (PMF.mem_support_map_iff _ _ _).mp hs with ⟨y, hy, rfl⟩
  exact ⟨y, (true_action_support x ▸ hy), rfl⟩

theorem damaged_not_safe_after_restore (u : Bool) (controller : State → Bool) (i : Fin 3) (bad : Bool) :
    ¬ StaysIn ((jointStep (corrupt (false,u) controller i bad)).map JointRepairState.physical) K := by
  rw [first_tick_physical_unchanged]
  intro h
  have hbad := h (by simp : (false,u) ∈ (PMF.pure (false,u)).support)
  simp [K, conflictSurvivalRegion] at hbad

namespace Posterior
open SupportViabilityClosure

def initial : PMF State := PMF.pure (true,false)
def source (_ : ℕ) := P
abbrev ObservedPolicy := ∀ n, CausalHistory Bool (Bool × Bool) n → PMF Bool

theorem initial_true_support :
    traceSupport initial Prod.fst source 0 true = {(true,false)} := by
  ext ⟨b,u⟩
  cases b <;> cases u <;> simp [traceSupport, initialSupport, initial]

theorem positive_successor_fiber (π : ObservedPolicy) (n : ℕ)
    (g : CausalHistory Bool (Bool × Bool) n) (a y : Bool)
    (hg : (g,(a,y)) ∈ (coarseLaw initial Prod.fst source π (n+1)).support) :
    successorSupport Prod.fst source n (traceSupport initial Prod.fst source n g) a y =
      {x : State | x.1 = y} := by
  obtain ⟨_,_,z,hz⟩ :=
    (mem_coarseLaw_succ_support_iff initial Prod.fst source π n g a y).mp hg
  rcases hz with ⟨hzy,w,hw,hzw⟩
  have hza : z.1 = a := (transition_support w z a).mp hzw
  have hya : y = a := hzy.symm.trans hza
  ext x
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx,w,hw,?_⟩
    exact (transition_support w x a).mpr (hx.trans hya)

/-- At every positive time and positive history, this is the support of
    the actual existing posterior, not a freely supplied conditional law. -/
theorem actual_posterior_support (π : ObservedPolicy) (n : ℕ)
    (g : CausalHistory Bool (Bool × Bool) n) (a y : Bool)
    (hg : (g,(a,y)) ∈ (coarseLaw initial Prod.fst source π (n+1)).support) :
    (PosteriorSupportCoverageCheck.fiberTerminalPosterior
      (microLaw initial Prod.fst source π (n+1))
      (projectHistory Prod.fst (n+1)) (riskLastState (n+1)) (g,(a,y)) hg).support =
      {x : State | x.1 = y} := by
  rw [← successorSupport_eq_fiberTerminalPosterior_support initial Prod.fst source π n g a y hg]
  exact positive_successor_fiber π n g a y hg
end Posterior
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictOrganizationalSource
