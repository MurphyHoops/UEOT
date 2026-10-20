import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverage
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSupportViabilityCheck

/-!
# Actual-law control and finite-support witnesses

The examples retain distinct roles: an empty common-fiber action set, a
missing-fiber occupancy obstruction, strict improvement from actual history
information, and a viable source with a covered prefix entering a dead end.
Executable checks remain outside classical proof sections and consume exact
finite data whose connection to the actual PMFs is proved.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace ObservableActionCoverageCheck

open MeasureTheory UEOT.V3.PathError
open scoped BigOperators

/-! ## Executable Bool data, before all Classical/noncomputable proof scopes

There are two hidden states and two actions but only one observation.
Each state has one certified action; the common-fiber action set is empty.
The #eval command tests the actual compiled decision data, not only a theorem
about an abstract Decidable instance. Its expected output is (0, false, false).
-/

namespace EmptyCommonAction

def observe (_x : Bool) : Unit := ()

def crossedRegistration (_n : ℕ) (x a : Bool) : Prop := x = a

instance crossedRegistrationDecidable :
    ∀ n x a, Decidable (crossedRegistration n x a) :=
  fun _ x a => inferInstanceAs (Decidable (x = a))

theorem current_fiber_is_nonempty : ∃ x : Bool, observe x = () :=
  ⟨false, rfl⟩

theorem each_state_has_a_certified_action :
    ∀ x : Bool, ∃ a : Bool, crossedRegistration 0 x a :=
  fun x => ⟨x, rfl⟩

theorem no_common_certified_action :
    ¬ ∃ a : Bool, ∀ x : Bool, crossedRegistration 0 x a := by
  rintro ⟨a, ha⟩
  have hf : false = a := ha false
  have ht : true = a := ha true
  have hbad : false = true := hf.trans ht.symm
  cases hbad

theorem fiber_mask_is_empty :
    fiberCertifiedActions observe crossedRegistration 0 () = ∅ := by
  ext a
  constructor
  · intro ha
    have hall := (mem_fiberCertifiedActions observe crossedRegistration 0 () a).mp ha
    exact False.elim (no_common_certified_action ⟨a, fun x => hall x rfl⟩)
  · simp

#eval (let mask := fiberCertifiedActions observe crossedRegistration 0 ();
  (mask.card, decide (false ∈ mask), decide (true ∈ mask)))

end EmptyCommonAction

noncomputable section
open scoped Classical

/-! ## Missing-fiber counterexample on the actual law

The hidden state is Bool and the observation and action are both Unit.
Checking the representative false certifies the unique observable action,
but deployment starts at the indistinguishable true state. The example
refutes an occupancy bound; it makes no unsound macro failure-envelope claim.
-/

namespace MissingFiber

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSpace Unit := ⊤

def observe : Bool → Unit := fun _ => ()

def source : ℕ → Bool → Unit → PMF Bool := fun _ x _ => PMF.pure x

def policy (n : ℕ) (_hc : CausalHistory Unit (Unit × Unit) n) : PMF Unit :=
  PMF.pure ()

def certified (_n : ℕ) (x : Bool) (_a : Unit) : Prop := x = false

def allowed (n : ℕ) (_hc : CausalHistory Unit (Unit × Unit) n) (_a : Unit) : Prop :=
  True

theorem representative_is_certified (n : ℕ) :
    observe false = observe true ∧ certified n false () := by
  exact ⟨rfl, rfl⟩

theorem observable_action_leakage_is_zero
    (n : ℕ) (hc : CausalHistory Unit (Unit × Unit) n) :
    (policy n hc).toMeasure.real {a | ¬ allowed n hc a} = 0 := by
  simp [allowed]

theorem actual_initial_row_law :
    coverageDeploymentRowLaw (PMF.pure true) observe source policy 0 =
      PMF.pure (true, ()) := by
  simp [coverageDeploymentRowLaw, causalLaw, policy, pmfExtend, riskLastState]
  erw [PMF.pure_bind, PMF.pure_map, PMF.pure_map]

theorem actual_uncovered_mass_is_one :
    (coverageDeploymentRowLaw (PMF.pure true) observe source policy 0).toMeasure.real
      {xa | ¬ certified 0 xa.1 xa.2} = 1 := by
  rw [actual_initial_row_law, ← coverage_uncovered_indicator_expectation]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_unique]
  norm_num [certified]

theorem checking_one_representative_does_not_bound_actual_coverage :
    (policy 0 ()).toMeasure.real {a | ¬ allowed 0 () a} = 0 ∧
      ¬ ((coverageDeploymentRowLaw (PMF.pure true) observe source policy 0).toMeasure.real
        {xa | ¬ certified 0 xa.1 xa.2} ≤ 0) := by
  constructor
  · exact observable_action_leakage_is_zero 0 ()
  · rw [actual_uncovered_mass_is_one]
    norm_num

end MissingFiber

end
end ObservableActionCoverageCheck
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace PosteriorSupportStrictWitness

open MeasureTheory UEOT.V3.PathError PosteriorSupportCoverageCheck
open scoped BigOperators Classical

noncomputable section

abbrev State := Bool × Bool
abbrev Observation := Option Bool
-- The one-step CausalHistory types reduce to these products. Exposing the
-- products keeps literal tuple proofs transparent to simplification.
abbrev MicroHistory := State × (Bool × State)
abbrev CoarseHistory := Observation × (Bool × Observation)

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSpace Observation := ⊤

def leftStart : State := (false, false)
def rightStart : State := (false, true)
def leftState : State := (true, false)
def rightState : State := (true, true)

def observe (x : State) : Observation := if x.1 then none else some x.2

/-- Both actions move an initial state to its own terminal state. At a
terminal state the matching action stays there; the other returns to its
own initial state. This is the four-state source in the frozen contract. -/
def transition (x : State) (a : Bool) : State :=
  if x.1 then (if a = x.2 then x else (false, x.2)) else (true, x.2)

def source (_n : ℕ) (x : State) (a : Bool) : PMF State :=
  PMF.pure (transition x a)

def initial : PMF State :=
  (PMF.uniformOfFintype Bool).map (fun side => (false, side))

def initialObservation : ∀ n, CausalHistory Observation (Bool × Observation) n → Observation
  | 0, h => h
  | n + 1, h => initialObservation n h.1

def rememberedAction : Observation → Bool
  | some side => side
  | none => true

/-- The first action is false. Subsequent actions remember the initial
observation. The fallback at an initially null observation is explicit. -/
def policy : ∀ n, CausalHistory Observation (Bool × Observation) n → PMF Bool
  | 0, _h => PMF.pure false
  | n + 1, h => PMF.pure (rememberedAction (initialObservation (n + 1) h))

def certified (_n : ℕ) (x : State) (a : Bool) : Prop :=
  x.1 = false ∨ a = x.2

def actualPrefix : PMF MicroHistory :=
  causalLaw initial (riskMicroControlKernel observe source policy) 1

def historyProjection : MicroHistory → CoarseHistory :=
  riskHistoryMap observe (fun ax : Bool × State => (ax.1, observe ax.2)) 1

abbrev coarsePrefix : PMF CoarseHistory := actualPrefix.map historyProjection

def leftHistory : MicroHistory := (leftStart, (false, leftState))
def rightHistory : MicroHistory := (rightStart, (false, rightState))

def leftCoarse : CoarseHistory := (some false, (false, none))
def rightCoarse : CoarseHistory := (some true, (false, none))
def nullCoarse : CoarseHistory := (none, (false, none))

/-- Only the action identified by the remembered initial observation is
allowed. In particular, the null history has no allowed action. -/
def allowed (h : CoarseHistory) (a : Bool) : Prop := some a = h.1

theorem initial_apply (phase side : Bool) :
    initial (phase, side) = if phase then 0 else (1 / 2 : ENNReal) := by
  unfold initial
  rw [PMF.map_apply, tsum_fintype]
  cases phase <;> cases side <;>
    norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply]

/-- The prefix masses are derived from the actual causal recursion. -/
theorem actualPrefix_apply (x : State) (a : Bool) (z : State) :
    actualPrefix (x, (a, z)) =
      initial x * (PMF.pure false a * PMF.pure (transition x a) z) := by
  change pmfExtend initial
    (fun x => pmfExtend (PMF.pure false) (fun a => PMF.pure (transition x a)))
      (x, (a, z)) = _
  rw [pmfExtend_apply, pmfExtend_apply]

theorem actualPrefix_support_iff (h : MicroHistory) :
    h ∈ actualPrefix.support ↔ h = leftHistory ∨ h = rightHistory := by
  rcases h with ⟨⟨phase, side⟩, a, ⟨nextPhase, nextSide⟩⟩
  erw [PMF.mem_support_iff, actualPrefix_apply, initial_apply]
  cases phase <;> cases side <;> cases a <;> cases nextPhase <;> cases nextSide <;>
    norm_num [transition, leftHistory, rightHistory,
      leftStart, rightStart, leftState, rightState]

theorem actual_prefix_masses :
    actualPrefix leftHistory = (1 / 2 : ENNReal) ∧
      actualPrefix rightHistory = (1 / 2 : ENNReal) := by
  constructor
  · change actualPrefix ((false, false), (false, (true, false))) = _
    rw [actualPrefix_apply, initial_apply]
    norm_num [transition]
  · change actualPrefix ((false, true), (false, (true, true))) = _
    rw [actualPrefix_apply, initial_apply]
    norm_num [transition]

theorem left_history_supported : leftHistory ∈ actualPrefix.support :=
  (actualPrefix_support_iff _).mpr (Or.inl rfl)

theorem right_history_supported : rightHistory ∈ actualPrefix.support :=
  (actualPrefix_support_iff _).mpr (Or.inr rfl)

theorem coarsePrefix_support_iff (h : CoarseHistory) :
    h ∈ coarsePrefix.support ↔ h = leftCoarse ∨ h = rightCoarse := by
  constructor
  · intro hh
    obtain ⟨micro, hm, heq⟩ :=
      (PMF.mem_support_map_iff historyProjection actualPrefix h).mp hh
    rcases (actualPrefix_support_iff micro).mp hm with rfl | rfl
    · exact Or.inl heq.symm
    · exact Or.inr heq.symm
  · rintro (rfl | rfl)
    · exact (PMF.mem_support_map_iff _ _ _).mpr
        ⟨leftHistory, left_history_supported, rfl⟩
    · exact (PMF.mem_support_map_iff _ _ _).mpr
        ⟨rightHistory, right_history_supported, rfl⟩

theorem left_coarse_supported : leftCoarse ∈ coarsePrefix.support :=
  (coarsePrefix_support_iff _).mpr (Or.inl rfl)

theorem right_coarse_supported : rightCoarse ∈ coarsePrefix.support :=
  (coarsePrefix_support_iff _).mpr (Or.inr rfl)

/-- These are two distinct, positive-probability histories with the same
current observation, not arbitrary representatives of a quotient class. -/
theorem two_positive_coarse_histories :
    0 < coarsePrefix leftCoarse ∧ 0 < coarsePrefix rightCoarse ∧
      leftCoarse ≠ rightCoarse ∧
      riskLastState 1 leftCoarse = riskLastState 1 rightCoarse := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · exact pos_iff_ne_zero.mpr ((PMF.mem_support_iff _ _).mp left_coarse_supported)
  · exact pos_iff_ne_zero.mpr ((PMF.mem_support_iff _ _).mp right_coarse_supported)
  · intro heq
    have hfirst := congrArg (fun h : CoarseHistory => h.1) heq
    change (some false : Option Bool) = some true at hfirst
    have hbool : (false : Bool) = true := Option.some.inj hfirst
    cases hbool

theorem left_posterior_support_iff
    (hy : leftCoarse ∈ coarsePrefix.support) (x : State) :
    x ∈ (fiberTerminalPosterior actualPrefix historyProjection
      (riskLastState 1) leftCoarse hy).support ↔ x = leftState := by
  erw [mem_fiberTerminalPosterior_support_iff]
  constructor
  · rintro ⟨h, hh, hp, hl⟩
    rcases (actualPrefix_support_iff h).mp hh with rfl | rfl
    · change leftState = x at hl
      exact hl.symm
    · have hfirst := congrArg (fun h : CoarseHistory => h.1) hp
      change (some true : Option Bool) = some false at hfirst
      have hbool : (true : Bool) = false := Option.some.inj hfirst
      cases hbool
  · intro hx
    subst x
    exact ⟨leftHistory, left_history_supported, rfl, rfl⟩

theorem right_posterior_support_iff
    (hy : rightCoarse ∈ coarsePrefix.support) (x : State) :
    x ∈ (fiberTerminalPosterior actualPrefix historyProjection
      (riskLastState 1) rightCoarse hy).support ↔ x = rightState := by
  erw [mem_fiberTerminalPosterior_support_iff]
  constructor
  · rintro ⟨h, hh, hp, hl⟩
    rcases (actualPrefix_support_iff h).mp hh with rfl | rfl
    · have hfirst := congrArg (fun h : CoarseHistory => h.1) hp
      change (some false : Option Bool) = some true at hfirst
      have hbool : (false : Bool) = true := Option.some.inj hfirst
      cases hbool
    · change rightState = x at hl
      exact hl.symm
  · intro hx
    subst x
    exact ⟨rightHistory, right_history_supported, rfl, rfl⟩

/-- The two actual terminal posterior supports are the respective singleton
supports of δ_L and δ_R, with both conditioning histories of positive mass. -/
theorem posterior_supports_are_singletons :
    (fiberTerminalPosterior actualPrefix historyProjection
      (riskLastState 1) leftCoarse left_coarse_supported).support = {leftState} ∧
    (fiberTerminalPosterior actualPrefix historyProjection
      (riskLastState 1) rightCoarse right_coarse_supported).support = {rightState} := by
  constructor
  · ext x
    exact left_posterior_support_iff left_coarse_supported x
  · ext x
    exact right_posterior_support_iff right_coarse_supported x

/-- Both conflicting current-fiber states are actually reachable. -/
theorem both_terminal_states_reachable :
    leftState ∈ (actualPrefix.map (riskLastState 1)).support ∧
      rightState ∈ (actualPrefix.map (riskLastState 1)).support := by
  constructor
  · exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨leftHistory, left_history_supported, rfl⟩
  · exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨rightHistory, right_history_supported, rfl⟩

/-- Actual occupancy is zero by direct reuse of the checked posterior
certification theorem, with the same source and policy at every interface. -/
theorem actual_uncovered_probability_zero :
    (coverageDeploymentRowLaw initial observe source policy 1).toMeasure.real
      {xa | ¬ certified 1 xa.1 xa.2} = 0 := by
  apply le_antisymm
  · apply posterior_supported_actions_bound_actual_coverage
      initial observe source policy certified 1 allowed 0
    · intro h hh a _ha ha x hx
      rcases (coarsePrefix_support_iff h).mp hh with rfl | rfl
      · have hxl := (left_posterior_support_iff hh x).mp hx
        subst x
        have ha0 : a = false := by simpa [allowed, leftCoarse] using ha
        simp [certified, leftState, ha0]
      · have hxr := (right_posterior_support_iff hh x).mp hx
        subst x
        have ha1 : a = true := by simpa [allowed, rightCoarse] using ha
        simp [certified, rightState, ha1]
    · intro h hh
      rcases (coarsePrefix_support_iff h).mp hh with rfl | rfl
      · rw [← coverage_uncovered_indicator_expectation]
        norm_num [policy, initialObservation, rememberedAction,
          allowed, leftCoarse, Fintype.sum_bool]
      · rw [← coverage_uncovered_indicator_expectation]
        norm_num [policy, initialObservation, rememberedAction,
          allowed, rightCoarse, Fintype.sum_bool]
  · exact measureReal_nonneg

/-- The whole current-observation fiber requires incompatible actions,
although posterior certification above gives zero actual uncovered mass. -/
theorem whole_current_fiber_has_no_common_action :
    ¬ ∃ a : Bool, ∀ x : State, observe x = none → certified 1 x a := by
  rintro ⟨a, ha⟩
  have hL := ha leftState rfl
  have hR := ha rightState rfl
  cases a <;> simp [certified, leftState, rightState] at hL hR

/-- The null history has no actual mass. Its policy can violate the mask
with probability one without adding a premise to the actual-support bound. -/
theorem null_history_boundary :
    coarsePrefix nullCoarse = 0 ∧
      (policy 1 nullCoarse).toMeasure.real {a | ¬ allowed nullCoarse a} = 1 := by
  constructor
  · by_contra hne
    have hm : nullCoarse ∈ coarsePrefix.support := (PMF.mem_support_iff _ _).mpr hne
    rcases (coarsePrefix_support_iff nullCoarse).mp hm with hleft | hright
    · have hfirst := congrArg (fun h : CoarseHistory => h.1) hleft
      change (none : Option Bool) = some false at hfirst
      cases hfirst
    · have hfirst := congrArg (fun h : CoarseHistory => h.1) hright
      change (none : Option Bool) = some true at hfirst
      cases hfirst
  · have hnull (a : Bool) : ¬ allowed nullCoarse a := by
      intro ha
      change (some a : Option Bool) = none at ha
      cases ha
    rw [← coverage_uncovered_indicator_expectation]
    calc
      _ = ∑ a : Bool, (policy 1 nullCoarse a).toReal := by
        apply Finset.sum_congr rfl
        intro a _
        rw [if_neg (hnull a), mul_one]
      _ = 1 := coverage_sum_toReal _


end
end PosteriorSupportStrictWitness
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace SupportViabilityClosure
namespace SafePrefixDeadend

open MeasureTheory UEOT.V3.PathError

def observe (_x : Bool) : Unit := ()

def transition (n : ℕ) (x a : Bool) : Bool :=
  if n = 0 then a else x

noncomputable def source (n : ℕ) (x a : Bool) : PMF Bool :=
  PMF.pure (transition n x a)

theorem mem_source_support_iff (n : ℕ) (x a z : Bool) :
    z ∈ (source n x a).support ↔ z = transition n x a := by
  simp [source]

/-- Executable transition-support data with no PMF-valued parameter. -/
def supportTable (n : ℕ) (x a z : Bool) : Prop :=
  z = transition n x a

instance supportTableDecidable : ∀ n x a z, Decidable (supportTable n x a z) :=
  fun n x a z => inferInstanceAs (Decidable (z = transition n x a))

/-- The computed relation is proved exact for the same actual source. -/
theorem supportTable_exact (n : ℕ) (x a z : Bool) :
    supportTable n x a z ↔ z ∈ (source n x a).support :=
  (mem_source_support_iff n x a z).symm

/-- This decision procedure computes finite Bool equality and its proof
certifies membership in the actual PMF support. It uses no sampled support. -/
instance sourceSupportDecidable :
    ∀ n x a z, Decidable (z ∈ (source n x a).support) :=
  fun n x a z =>
    if h : z = transition n x a then
      isTrue ((mem_source_support_iff n x a z).mpr h)
    else isFalse (fun hz => h ((mem_source_support_iff n x a z).mp hz))

def certified (n : ℕ) (x _a : Bool) : Prop :=
  n = 0 ∨ x = false

instance certificationDecidable : ∀ n x a, Decidable (certified n x a) :=
  fun n x _a => inferInstanceAs (Decidable (n = 0 ∨ x = false))

-- Executable finite check; expected (true, false, true), with status in the source-bound receipt.
#eval (finiteRelationViabilityCheck observe supportTable certified 0 2 (Finset.univ : Finset Bool),
  finiteRelationViabilityCheck observe supportTable certified 1 1 ({true} : Finset Bool),
  finiteRelationViabilityCheck observe supportTable certified 1 1 ({false} : Finset Bool))

private theorem initial_checker_pass :
    finiteRelationViabilityCheck observe supportTable certified 0 2 (Finset.univ : Finset Bool) = true := by
  decide

theorem deadend_checker_rejects :
    finiteRelationViabilityCheck observe supportTable certified 1 1 ({true} : Finset Bool) = false := by
  decide

private theorem good_successor_checker_pass :
    finiteRelationViabilityCheck observe supportTable certified 1 1 ({false} : Finset Bool) = true := by
  decide

noncomputable section

open scoped Classical

local instance : MeasurableSpace Bool := ⊤

def initial : PMF Bool := PMF.uniformOfFintype Bool

def fallbackPolicy : ∀ n, CausalHistory Unit (Bool × Unit) n → PMF Bool :=
  fun _ _ => PMF.pure false

def deadendPolicy : ∀ n, CausalHistory Unit (Bool × Unit) n → PMF Bool :=
  fun _ _ => PMF.pure true

def deadendHistory : CausalHistory Unit (Bool × Unit) 1 :=
  ((), (true, ()))

theorem initial_support_eq_univ (y : Unit) :
    initialSupport initial observe y = Set.univ := by
  cases y
  ext x
  simp [initialSupport, initial, observe]

/-- The Boolean decision is consumed by the exact checker theorem and then
the actual-policy existence theorem, rather than reported as a free-standing
computation about an unrelated graph. -/
theorem a_complete_zero_uncovered_policy_exists :
    ∃ π : ∀ n, CausalHistory Unit (Bool × Unit) n → PMF Bool,
      ∀ n, n < 2 →
        (coverageDeploymentRowLaw initial observe source π n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0 := by
  apply (initial_viability_iff_exists_zero_uncovered_policy
    initial observe source certified 2 fallbackPolicy).mp
  intro y _
  have hV := (finiteRelationViabilityCheck_correct
    observe supportTable source certified supportTable_exact
    2 0 (Finset.univ : Finset Bool)).mp initial_checker_pass
  simpa only [initial_support_eq_univ, Finset.coe_univ] using hV

theorem deadend_policy_first_step_covered :
    (coverageDeploymentRowLaw initial observe source deadendPolicy 0).toMeasure.real
      {xa | ¬ certified 0 xa.1 xa.2} = 0 := by
  apply (zero_uncovered_iff_support_certified
    initial observe source deadendPolicy certified 0).mpr
  intro h hh a ha x hx
  exact Or.inl rfl

theorem deadend_history_actually_supported :
    deadendHistory ∈ (coarseLaw initial observe source deadendPolicy 1).support := by
  apply (mem_coarseLaw_succ_support_iff
    initial observe source deadendPolicy 0 () true ()).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (mem_coarseLaw_zero_support_iff initial observe source deadendPolicy ()).mpr
    rw [initial_support_eq_univ]
    exact ⟨false, Set.mem_univ false⟩
  · simp [deadendPolicy]
  · refine ⟨true, rfl, false, ?_, ?_⟩
    · change false ∈ initialSupport initial observe ()
      rw [initial_support_eq_univ]
      exact Set.mem_univ false
    · apply (mem_source_support_iff 0 false true true).mpr
      rfl

theorem deadend_trace_support_eq :
    traceSupport initial observe source 1 deadendHistory = {true} := by
  change successorSupport observe source 0
    (initialSupport initial observe ()) true () = {true}
  rw [initial_support_eq_univ]
  ext x
  simp [successorSupport, observe, source, transition]

/-- No current action can certify this actually supported history, although
the first transition of the very same policy has zero uncertified mass. -/
theorem deadend_has_no_common_certified_action :
    ¬ ∃ a : Bool,
      ∀ x ∈ traceSupport initial observe source 1 deadendHistory,
        certified 1 x a := by
  rintro ⟨a, hcert⟩
  have hx : true ∈ traceSupport initial observe source 1 deadendHistory := by
    rw [deadend_trace_support_eq]
    simp
  have hc := hcert true hx
  simp [certified] at hc

theorem deadend_policy_second_step_not_covered :
    (coverageDeploymentRowLaw initial observe source deadendPolicy 1).toMeasure.real
      {xa | ¬ certified 1 xa.1 xa.2} ≠ 0 := by
  intro hzero
  have hcert := (zero_uncovered_iff_support_certified
    initial observe source deadendPolicy certified 1).mp hzero
  apply deadend_has_no_common_certified_action
  refine ⟨true, ?_⟩
  exact hcert deadendHistory deadend_history_actually_supported true
    (by simp [deadendPolicy])

/-- One source has a complete successful policy and a different covered
first-step prefix that cannot be extended. This distinguishes existence
from the earlier strong all-covered-prefix Extend condition. -/
theorem viable_source_with_a_covered_deadend :
    (∃ π : ∀ n, CausalHistory Unit (Bool × Unit) n → PMF Bool,
      ∀ n, n < 2 →
        (coverageDeploymentRowLaw initial observe source π n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0) ∧
    (coverageDeploymentRowLaw initial observe source deadendPolicy 0).toMeasure.real
      {xa | ¬ certified 0 xa.1 xa.2} = 0 ∧
    deadendHistory ∈ (coarseLaw initial observe source deadendPolicy 1).support ∧
    (¬ ∃ a : Bool,
      ∀ x ∈ traceSupport initial observe source 1 deadendHistory, certified 1 x a) :=
  ⟨a_complete_zero_uncovered_policy_exists, deadend_policy_first_step_covered,
    deadend_history_actually_supported, deadend_has_no_common_certified_action⟩


end
end SafePrefixDeadend
end SupportViabilityClosure
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
