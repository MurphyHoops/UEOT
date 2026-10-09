import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MultiScaleExactControlComposition
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ActiveHiddenOptimalControlExample
import Mathlib.Tactic

/-!
# UMC authentic three-level tower with objective-sensitive compression

Source X = four physical (visible,hidden) microstates, action Bool.
First scale X -> Y is the TWO-state future-predictive quotient of the
same non-Dirac controlled Markov source with persistent hidden memory.
Second scale Y -> Unit is valid only for a state-neutral observable reward.

This module first proves a general state-neutral finite control collapse,
then constructs a source-consistent X -> Y -> Unit exact-control tower
by the new multi-scale composition theorem. Its final discounted policy
remains optimal against MICRO causal randomized policies. A companion no-go
proves that a state-sensitive observable reward cannot be collapsed to Unit.

The two large-scale results are CONDITIONAL on the given reward contract:
no intrinsic organism purpose, multi-parent physical object or endogenous
repair program is derived.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState
open CausalPolicy

universe uY uA

/-- Any finite controlled model whose reward depends on action but NOT
source state has a genuine exact discounted control quotient to Unit.
Transition closure follows by normalization, not by an arbitrary macro
kernel assumption. This is the canonical zero-information control level. -/
noncomputable def stateNeutralControlCollapse
    {Y : Type uY} {A : Type uA}
    [Fintype Y] [Nonempty Y] [Fintype A] [Nonempty A]
    (M : Model Y (fun _ => A))
    (r : A → ℝ) (hreward : ∀ y a, M.reward y a = r a) :
    ExactControlQuotient Y PUnit.{1} (fun _ => A) := by
  classical
  refine {
    f := fun _ => PUnit.unit
    surjective := ?_
    micro := M
    macroModel := {
      transition := fun _ _ _ => 1
      reward := fun _ a => r a
      rewardBound := M.rewardBound
      discount := M.discount
      transition_nonneg := by intro _ _ _; norm_num
      transition_sum_one := by intro _ _; simp
      reward_abs_le := ?_
      discount_pos := M.discount_pos
      discount_lt_one := M.discount_lt_one
    }
    discount_eq := rfl
    reward_closed := ?_
    transition_closed := ?_
  }
  · intro z
    cases z
    exact ⟨Classical.choice (inferInstance : Nonempty Y), rfl⟩
  · intro z a
    let y := Classical.choice (inferInstance : Nonempty Y)
    calc
      |r a| = |M.reward y a| := congrArg abs (hreward y a).symm
      _ ≤ M.rewardBound := M.reward_abs_le y a
  · intro y a
    exact hreward y a
  · intro y a z
    cases z
    simpa [fiberMass] using M.transition_sum_one y a

/-- A real two-action stochastic process with hidden physical memory is
first quotiented by its future response (two predictive classes). Here
the declared purpose is to prefer action true independently of source
state, so second-scale state erasure is legitimate for this objective. -/
noncomputable def neutralRewardPredictiveControl :
    letI : Fintype (ReachableState
      (stochasticFuture activeHiddenKernel visibleRead)) := Fintype.ofFinite _
    ExactControlQuotient (Bool × Bool)
      (ReachableState (stochasticFuture activeHiddenKernel visibleRead))
      (fun _ => Bool) := by
  classical
  exact predictiveFutureExactControlQuotient
    activeHiddenKernel visibleRead activeFutureProbe
    activeIndicatorCoefficient active_future_indicator_probe_certificate
    (fun _ a => if a then 1 else 0)
    1 (1/2)
    (by intro _ a; cases a <;> norm_num)
    (by norm_num) (by norm_num)

/-- The actual middle world is EXACTLY the macro dynamics produced by
stage one, so this second leg has no independent unrelated source. -/
noncomputable def neutralRewardUpperControl :
    letI : Fintype (ReachableState
      (stochasticFuture activeHiddenKernel visibleRead)) := Fintype.ofFinite _
    ExactControlQuotient
      (ReachableState (stochasticFuture activeHiddenKernel visibleRead))
      PUnit.{1} (fun _ => Bool) := by
  classical
  letI : Fintype (ReachableState
    (stochasticFuture activeHiddenKernel visibleRead)) := Fintype.ofFinite _
  exact stateNeutralControlCollapse
    neutralRewardPredictiveControl.macroModel
    (fun a => if a then 1 else 0) (by intro c a; rfl)

/-- Two real, nontrivial different state spaces and THREE levels of models:
physical source -> future-predictive two-class model -> minimal Unit goal state.
Both quotient transitions are mathematically built from actual source. -/
noncomputable def neutralRewardThreeLevelTower :
    ExactControlQuotient (Bool × Bool) PUnit.{1} (fun _ => Bool) := by
  classical
  letI : Fintype (ReachableState
    (stochasticFuture activeHiddenKernel visibleRead)) := Fintype.ofFinite _
  exact composeExactControlQuotients
    neutralRewardPredictiveControl neutralRewardUpperControl rfl

/-- The intermediate representation DOES distinguish the two visible bits.
Thus the three-level factorization does not fake a two-layer tower by naming
a singleton two different ways. The source has four microscopic tokens. -/
theorem predictive_middle_level_has_two_distinct_states :
    toReachable (stochasticFuture activeHiddenKernel visibleRead)
      (false,false) ≠
    toReachable (stochasticFuture activeHiddenKernel visibleRead)
      (true,false) := by
  intro h
  have hv : stochasticFuture activeHiddenKernel visibleRead (false,false) =
      stochasticFuture activeHiddenKernel visibleRead (true,false) :=
    congrArg Subtype.val h
  have hobs := (active_hidden_future_eq_iff_visible _ _).mp hv
  exact Bool.false_ne_true hobs

/-- Across both nontrivial quotient arrows, exact optimal discounted
control values on all four physical microstates are still recovered from
the single ultimate macro state. Validity is relative to this declared
state-neutral objective, not an arbitrary hidden-dependent reward. -/
theorem three_level_macro_optimal_value_is_micro_optimal :
    ∀ x : Bool × Bool,
      neutralRewardThreeLevelTower.micro.optimalValue x =
      neutralRewardThreeLevelTower.macroModel.optimalValue
        (neutralRewardThreeLevelTower.f x) := by
  intro x
  exact neutralRewardThreeLevelTower.optimalValue_apply x

/-- The exact same source kernel cannot be collapsed to a singleton for
the previously registered state-sensitive visible matching objective:
micro rewards differ across two visible states, contradicting reward
fibre closure. This is a true multi-scale REJECTION control. -/
theorem state_sensitive_objective_prevents_second_scale_collapse :
    ¬ ∃ rTop : PUnit.{1} → Bool → ℝ,
      ∀ x : Bool × Bool, ∀ a : Bool,
        activeObservableReward
          (toReachable (stochasticFuture activeHiddenKernel visibleRead) x)
          a = rTop PUnit.unit a := by
  rintro ⟨rTop, h⟩
  have hf := h (false,false) false
  have ht := h (true,false) false
  rw [activeObservableReward_exact_source_readout] at hf ht
  have hcontr : (1 : ℝ) = 0 := hf.trans ht.symm
  norm_num at hcontr

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
