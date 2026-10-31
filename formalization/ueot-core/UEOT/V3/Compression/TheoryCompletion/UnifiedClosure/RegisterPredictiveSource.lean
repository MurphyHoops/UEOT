import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictiveOptimalControlLift
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicPriceProgram

/-!
Original promise: the canonical predictive/control quotient must belong to the SAME actual Register process and purpose source.
Existing exact sources: actual Model.transition=physicalSource=modeLaw.map(modeNext), complete record/active-port transport and actual all-price GOD/P9.
Reduced premise: derive all-word predictive equality, true class-resolving tests and normalized control quotient/reward from THAT actual model; no supplied hresolve or quotient.
Family: finite n/i, original Option Bool actions, m/noise/price/epsilon<=1 and legal discount; pre-action active read, including epsilon=0/1 and genuine hidden-coordinate ambiguity.
Consumers: original predictiveFutureExactControlQuotient/P-QUO, current projectState/projectOrganism and original all-price GOD of THIS actual submitted/returned AST.

Prediction is for the declared pre-action active-bit observation protocol.
It does not identify protected programs, parent history or owners, discard
full-record fees/failures, or imply every hidden-reading fine policy factors.
The objective remains the original declared actual expectedModePayoff. This
is a state quotient WITHIN a fixed mechanism, not cross-mechanism physical-only
identification of goal or reward (the old C6 obstruction remains, even when
epsilon=0 gives equal physical rows). Canonical optimality is parameter-indexed
analysis, not a new finite-data learner with access to unknown parameters.
Native payoff/parent consumers retain their original protected-code/goal and
source-information premises. No finite population/global closed-wallet GOD or
new observation is introduced.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPredictiveSource
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
open RegisterActuatorScaleSource RegisterSemanticInstructionScale
universe uMemory
noncomputable section

section Source
variable {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
  (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)

/-- No independent transition field: this IS the existing actual model row. -/
def kernel : FiniteControlledStochasticKernel (State n) Action where
  mass := (model i noise m price epsilon he d hd).transition
  nonneg := (model i noise m price epsilon he d hd).transition_nonneg
  normalized := (model i noise m price epsilon he d hd).transition_sum_one

def read (x : State n) : Bool:=x i

theorem kernel_physical_source (x : State n) (a : Action) (y : State n) :
    (kernel i noise m price epsilon he d hd).mass x a y=
      (RegisterFaultControlSource.physicalSource i m epsilon he x a y).toReal :=
  model_transition_eq_physicalSource i noise m price epsilon he d hd x a y

theorem kernel_actual_mode_source (x : State n) (a : Action) (y : State n) :
    (kernel i noise m price epsilon he d hd).mass x a y=
      ((modeLaw epsilon he).map (modeNext i m x a) y).toReal :=by
  rw [modeLaw_next_eq_physicalSource]
  exact kernel_physical_source i noise m price epsilon he d hd x a y

/-- Actual primitive-mode expectation, not a hypothetical macro row. -/
private theorem expected_trace (x : State n) (a : Action) (word : List (Action×Bool)) :
    (∑z : State n,(kernel i noise m price epsilon he d hd).mass x a z *
      controlledOutputTrace (kernel i noise m price epsilon he d hd) (read i) z word)=
    repairChance epsilon * controlledOutputTrace (kernel i noise m price epsilon he d hd) (read i) (update i x a) word+
      (epsilon : ℝ) * controlledOutputTrace (kernel i noise m price epsilon he d hd) (read i)
        (Function.update x i (!m.goal)) word :=
  model_expect_source i noise m price epsilon he d hd _ x a

/-- ALL source future words forget exactly the nonobserved physical ports. -/
theorem word_equal_of_active_equal (word : List (Action×Bool)) (x y : State n) (hxy : x i=y i) :
    controlledOutputTrace (kernel i noise m price epsilon he d hd) (read i) x word=
      controlledOutputTrace (kernel i noise m price epsilon he d hd) (read i) y word :=by
  induction word generalizing x y with
  | nil=>rfl
  | cons ev rest ih=>
    rcases ev with ⟨a,b⟩
    change (if x i=b then ∑z,(kernel i noise m price epsilon he d hd).mass x a z *
      controlledOutputTrace (kernel i noise m price epsilon he d hd) (read i) z rest else 0)=
      (if y i=b then ∑z,(kernel i noise m price epsilon he d hd).mass y a z *
      controlledOutputTrace (kernel i noise m price epsilon he d hd) (read i) z rest else 0)
    by_cases hx : x i=b
    · have hy : y i=b:=hxy.symm.trans hx
      simp only [if_pos hx,if_pos hy]
      rw [expected_trace,expected_trace]
      have hu : update i x a i=update i y a i :=by cases a <;> simp [update,hxy]
      rw [ih (update i x a) (update i y a) hu,
        ih (Function.update x i (!m.goal)) (Function.update y i (!m.goal)) (by simp)]
    · have hy : y i≠b:=by simpa only [←hxy] using hx
      simp [hx,hy]

/-- Necessity uses the CURRENT pre-action emission, even at total fault.
The empty word alone does not distinguish states. -/
theorem future_eq_iff_active (x y : State n) :
    stochasticFuture (kernel i noise m price epsilon he d hd) (read i) x=
      stochasticFuture (kernel i noise m price epsilon he d hd) (read i) y ↔ x i=y i :=by
  constructor
  · intro h
    exact equal_stochastic_futures_have_equal_readout (kernel i noise m price epsilon he d hd) (read i) h none
  · intro h
    funext word
    exact word_equal_of_active_equal i noise m price epsilon he d hd word x y h

/-- Exact binding to the already used physical actuator projection. -/
theorem future_eq_iff_actual_projection (x y : State n) :
    stochasticFuture (kernel i noise m price epsilon he d hd) (read i) x=
      stochasticFuture (kernel i noise m price epsilon he d hd) (read i) y ↔ projectState i x=projectState i y :=by
  rw [future_eq_iff_active]
  exact ⟨fun h=>funext (fun _=>h),fun h=>congrFun h 0⟩

def probe (b : Bool) : List (Action×Bool):=[(none,b)]

def coefficient (c : ReachableState (stochasticFuture (kernel i noise m price epsilon he d hd) (read i)))
    (b : Bool) : ℝ:=if (Classical.choose c.property) i=b then 1 else 0

/-- Two actual one-word source responses reconstruct EVERY true class
indicator. Resolving classes is a conclusion, not an input certificate. -/
theorem actual_tests_resolve : FutureTestsResolvePredictiveClasses
    (kernel i noise m price epsilon he d hd) (read i) (probe) (coefficient i noise m price epsilon he d hd) :=by
  classical
  intro c y
  let rep : State n:=Classical.choose c.property
  have hr : stochasticFuture (kernel i noise m price epsilon he d hd) (read i) rep=c.val:=Classical.choose_spec c.property
  have hc : (stochasticFuture (kernel i noise m price epsilon he d hd) (read i) y=c.val) ↔ y i=rep i :=by
    rw [←hr]
    exact future_eq_iff_active i noise m price epsilon he d hd y rep
  change (if stochasticFuture (kernel i noise m price epsilon he d hd) (read i) y=c.val then (1 : ℝ) else 0)=
    ∑b : Bool,(if rep i=b then (1 : ℝ) else 0) *
      stochasticFuture (kernel i noise m price epsilon he d hd) (read i) y [(none,b)]
  rw [if_congr hc (by rfl) (by rfl)]
  simp_rw [one_word_trace_is_pre_transition_observation]
  cases hy : y i <;> cases hr : rep i <;> norm_num [Fintype.sum_bool,read,hy,hr]

theorem actual_predictive_lumpability :
    StrongLumpability (kernel i noise m price epsilon he d hd)
      (stochasticFuture (kernel i noise m price epsilon he d hd) (read i)) :=
  stochastic_future_tests_force_strong_lumpability _ _ _ _ (actual_tests_resolve i noise m price epsilon he d hd)

/-- Canonical reward is sourced from the ACTUAL expected payoff of this
same model; representative independence is derived below. -/
def reward (c : ReachableState (stochasticFuture (kernel i noise m price epsilon he d hd) (read i))) (a : Action) : ℝ:=
  (model i noise m price epsilon he d hd).reward (Classical.choose c.property) a

private theorem actual_reward_equal (x y : State n) (a : Action) (hxy : x i=y i) :
    (model i noise m price epsilon he d hd).reward x a=(model i noise m price epsilon he d hd).reward y a :=by
  change expectedModePayoff i noise m price epsilon he x a=expectedModePayoff i noise m price epsilon he y a
  rw [expectedModePayoff_eq,expectedModePayoff_eq]
  simp only [stage,expectedChildren_eq]
  have hu : update i x a i=update i y a i :=by cases a <;> simp [update,hxy]
  rw [hu]

theorem reward_actual_source (x : State n) (a : Action) :
    reward i noise m price epsilon he d hd
      (toReachable (stochasticFuture (kernel i noise m price epsilon he d hd) (read i)) x) a=
      (model i noise m price epsilon he d hd).reward x a :=by
  let c:=toReachable (stochasticFuture (kernel i noise m price epsilon he d hd) (read i)) x
  have hrep : stochasticFuture (kernel i noise m price epsilon he d hd) (read i) (Classical.choose c.property)=
      stochasticFuture (kernel i noise m price epsilon he d hd) (read i) x:=Classical.choose_spec c.property
  exact actual_reward_equal i noise m price epsilon he d hd _ x a
    ((future_eq_iff_active i noise m price epsilon he d hd _ x).mp hrep)

/-- Actual application of the existing canonical predictive-control factory.
The reward bound is the original model's, at EVERY nonnegative price. -/
def control :
    letI : Fintype (ReachableState (stochasticFuture (kernel i noise m price epsilon he d hd) (read i))):=Fintype.ofFinite _
    ExactControlQuotient (State n)
      (ReachableState (stochasticFuture (kernel i noise m price epsilon he d hd) (read i))) (fun _=>Action) :=by
  classical
  exact predictiveFutureExactControlQuotient
    (kernel i noise m price epsilon he d hd) (read i) probe (coefficient i noise m price epsilon he d hd)
    (actual_tests_resolve i noise m price epsilon he d hd) (reward i noise m price epsilon he d hd)
    (model i noise m price epsilon he d hd).rewardBound d
    (fun c a=>(model i noise m price epsilon he d hd).reward_abs_le _ a) hd.1 hd.2

local instance predictiveClassFintype :
    Fintype (ReachableState (stochasticFuture (kernel i noise m price epsilon he d hd) (read i))) :=
  Fintype.ofFinite _

private theorem model_data_ext (M Q : Model (State n) (fun _=>Action))
    (ht : M.transition=Q.transition) (hr : M.reward=Q.reward)
    (hb : M.rewardBound=Q.rewardBound) (hdiscount : M.discount=Q.discount) : M=Q :=by
  cases M
  cases Q
  cases ht
  cases hr
  cases hb
  cases hdiscount
  rfl

/-- Unique normalized stochastic transition on the actual canonical classes,
reconstructed from this source's two tests. -/
theorem actual_unique_normalized_quotient :
    ∃! Kbar : FiniteControlledStochasticKernel
      (ReachableState (stochasticFuture (kernel i noise m price epsilon he d hd) (read i))) Action,
      ∀x a c,Kbar.mass (toReachable (stochasticFuture (kernel i noise m price epsilon he d hd) (read i)) x) a c=
        massIntoClass (kernel i noise m price epsilon he d hd)
          (stochasticFuture (kernel i noise m price epsilon he d hd) (read i)) x a c :=
  stochastic_future_tests_have_unique_normalized_quotient _ _ _ _ (actual_tests_resolve i noise m price epsilon he d hd)

/-- The canonical predictor's control MICRO-model is literally the original
actual Register model, including reward, bound and discount. -/
theorem control_micro_eq_actual :
    (control i noise m price epsilon he d hd).micro=model i noise m price epsilon he d hd :=by
  apply model_data_ext
  · rfl
  · funext x a
    exact reward_actual_source i noise m price epsilon he d hd x a
  · rfl
  · rfl

/-- The produced canonical CONTROL fibres are exactly the existing actual
active-port fibres, not an unrelated coarsening with equal optimal values. -/
theorem control_fiber_iff_actual_projection (x y : State n) :
    (control i noise m price epsilon he d hd).f x=(control i noise m price epsilon he d hd).f y ↔
      projectState i x=projectState i y :=by
  constructor
  · intro h
    exact (future_eq_iff_actual_projection i noise m price epsilon he d hd x y).mp (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (future_eq_iff_actual_projection i noise m price epsilon he d hd x y).mpr h

/-- THIS checker-returned q executes THIS p on every actual predictive
class. Arbitrary hidden-reading p is not asserted to have this property. -/
theorem actual_synthesis_factors (p : Instruction n) (q : Instruction 1)
    (hs : synthesize i p=some q) (x y : State n)
    (hxy : (control i noise m price epsilon he d hd).f x=(control i noise m price epsilon he d hd).f y) :
    interpret p x=interpret p y :=by
  rw [←(synthesize_actual i p q hs).2 x,←(synthesize_actual i p q hs).2 y,
    (control_fiber_iff_actual_projection i noise m price epsilon he d hd x y).mp hxy]

/-- The actual returned coarse AST, read on a canonical class. This is
THIS q, not a fresh optimal policy selected from an existence proof. -/
def returnedMacro (q : Instruction 1)
    (c : ReachableState (stochasticFuture (kernel i noise m price epsilon he d hd) (read i))) : Action:=
  interpret q (projectState i (Classical.choose c.property))

/-- The concrete returned-q consumer lifts to exactly THIS p on ALL actual
fine states. Representative choice disappears by the proven source signature. -/
theorem returnedMacro_lift_is_actual_p (p : Instruction n) (q : Instruction 1)
    (hs : synthesize i p=some q) (x : State n) :
    returnedMacro i noise m price epsilon he d hd q ((control i noise m price epsilon he d hd).f x)=interpret p x :=by
  let c:=(control i noise m price epsilon he d hd).f x
  have hrep : stochasticFuture (kernel i noise m price epsilon he d hd) (read i) (Classical.choose c.property)=
      stochasticFuture (kernel i noise m price epsilon he d hd) (read i) x:=Classical.choose_spec c.property
  have hp:=(future_eq_iff_actual_projection i noise m price epsilon he d hd _ x).mp hrep
  change interpret q (projectState i (Classical.choose c.property))=interpret p x
  rw [hp]
  exact (synthesize_actual i p q hs).2 x

/-- Real application of frozen P-QUO to the canonical source quotient. -/
theorem control_exact_value (x : State n) :
    (model i noise m price epsilon he d hd).optimalValue x=
      (control i noise m price epsilon he d hd).macroModel.optimalValue
        ((control i noise m price epsilon he d hd).f x) :=by
  rw [←control_micro_eq_actual i noise m price epsilon he d hd]
  exact (control i noise m price epsilon he d hd).optimalValue_apply x

/-- The canonical macro greedy policy really is optimal in the original
Register model, against all original fine causal competitors. -/
theorem canonical_greedy_actual_optimal :
    (∀{t : ℕ} (x : State n),
      CausalPolicy.infiniteValue
        (selectorPolicy ((control i noise m price epsilon he d hd).liftSelector
          (control i noise m price epsilon he d hd).macroModel.greedyAction))
        (model i noise m price epsilon he d hd) (t:=t) x=
          (model i noise m price epsilon he d hd).optimalValue x) ∧
    (∀(pi : CausalPolicy.{0,0,uMemory} (State n) (fun _=>Action)) {t : ℕ} (h : pi.Memory t),
      CausalPolicy.infiniteValue pi (model i noise m price epsilon he d hd) h≤
        (model i noise m price epsilon he d hd).optimalValue (pi.current h)) :=by
  have hh:=ExactControlQuotient.macroGreedy_lift_optimal.{0,0,0,uMemory}
    (control i noise m price epsilon he d hd)
  simpa only [control_micro_eq_actual] using hh

/-- The canonical predictive value and existing actual single-port control
value commute at ALL nonnegative prices, not only price*cost<=1. -/
theorem canonical_value_is_actual_active_value (x : State n) :
    (control i noise m price epsilon he d hd).macroModel.optimalValue
      ((control i noise m price epsilon he d hd).f x)=
    (model (0 : Fin 1) noise m price epsilon he d hd).optimalValue (projectState i x) :=by
  rw [←control_exact_value]
  exact RegisterFaultDynamicPriceProgram.actual_optimal_value_projection i noise m price epsilon he d hd x

/-- THIS actual synthesis pair retains its original all-price GOD meaning
on the canonical predictor's same MICRO-model. No alternative p/q is chosen. -/
theorem actual_returned_god (p : Instruction n) (q : Instruction 1)
    (hs : synthesize i p=some q) :
    IsBellmanGODSelector (control i noise m price epsilon he d hd).micro (interpret p) ↔
      IsBellmanGODSelector (model (0 : Fin 1) noise m price epsilon he d hd) (interpret q) :=by
  rw [control_micro_eq_actual]
  exact RegisterFaultDynamicPriceProgram.actual_all_price_god_selector i noise m price epsilon he d hd p q hs

/-- Existing actual object/program P9 scale consumes this same predictive
model. This is a typed GOD bridge, not a new universal six-property World. -/
theorem actual_p9_god_bridge :
    PreservesGOD (RegisterInstructionGODScale.godScale i)
      (fun obj=>IsBellmanGODSelector (control i noise m price epsilon he d hd).micro (interpret obj.2.val.1))
      (fun obj=>IsBellmanGODSelector (model (0 : Fin 1) noise m price epsilon he d hd) (interpret obj.2)) :=by
  simpa only [control_micro_eq_actual] using
    RegisterFaultDynamicPriceProgram.actual_all_price_preserves_god i noise m price epsilon he d hd

end Source
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPredictiveSource
