import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticPredictiveObservabilityBridge
import UEOT.V3.FiniteDiscountedExactQuotient
import Mathlib.Tactic

/-!
# UMC cross-layer construction — genuine prediction to exact optimal control

Source K/read gives a finite canonical future predictive quotient. Future-word
observability already DERIVES strong lumpability and unique normalized quotient
transition. We construct the actual frozen P-QUO-01 control quotient using
this SAME microscopic kernel, not a separately assumed transition closure.
Actions are shared and finite, rewards are declared bounded macro objectives,
and the discount satisfies 0 < beta < 1. We do NOT infer the objective
from mechanics; we do derive the dynamics premise of the control theorem.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState
open UEOT.V3.FiniteDiscountedControl
open CausalPolicy

universe uX uA uO uQ uI

/-- Typed bridge from the actual source stochastic kernel to the frozen
finite exact control quotient, with transition closure DERIVED by class
mass normalization. Reward fibre closure is enforced by construction,
not by a separately assumed independent source-model coincidence. -/
noncomputable def exactControlFromStochasticQuotient
    {X : Type uX} {A : Type uA} {Q : Type uQ}
    [Fintype X] [Fintype A] [Nonempty A]
    (K : FiniteControlledStochasticKernel X A)
    (q : X → Q) (hLump : StrongLumpability K q)
    (rbar : ReachableState q → A → ℝ)
    (B β : ℝ)
    (hr : ∀ c a, |rbar c a| ≤ B)
    (hβpos : 0 < β) (hβlt : β < 1) :
    letI : Fintype (ReachableState q) := Fintype.ofFinite _
    ExactControlQuotient X (ReachableState q) (fun _ => A) := by
  classical
  letI : Fintype (ReachableState q) := Fintype.ofFinite _
  let hKexists :=
    (strong_lumpability_iff_existsUnique_stochastic_quotient K q).mp hLump
  let Kbar := Classical.choose hKexists
  have hKbar : ∀ x a c,
      Kbar.mass (toReachable q x) a c = massIntoClass K q x a c :=
    (Classical.choose_spec hKexists).1
  refine {
    f := toReachable q
    surjective := toReachable_surjective q
    micro := {
      transition := fun x a y => K.mass x a y
      reward := fun x a => rbar (toReachable q x) a
      rewardBound := B
      discount := β
      transition_nonneg := K.nonneg
      transition_sum_one := K.normalized
      reward_abs_le := fun x a => hr (toReachable q x) a
      discount_pos := hβpos
      discount_lt_one := hβlt
    }
    macroModel := {
      transition := fun c a d => Kbar.mass c a d
      reward := rbar
      rewardBound := B
      discount := β
      transition_nonneg := Kbar.nonneg
      transition_sum_one := Kbar.normalized
      reward_abs_le := hr
      discount_pos := hβpos
      discount_lt_one := hβlt
    }
    discount_eq := rfl
    reward_closed := fun _ _ => rfl
    transition_closed := ?_
  }
  intro x a c
  change fiberMass (toReachable q) (fun z => K.mass x a z) c =
    Kbar.mass (toReachable q x) a c
  calc
    fiberMass (toReachable q) (fun z => K.mass x a z) c =
      massIntoClass K q x a c := by
      unfold fiberMass massIntoClass
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : toReachable q z = c
      · have hq : q z = c.1 := congrArg Subtype.val hz
        simp [hz, hq]
      · have hq : q z ≠ c.1 := by
          intro heq
          exact hz (Subtype.ext heq)
        simp [hz, hq]
    _ = Kbar.mass (toReachable q x) a c := (hKbar x a c).symm

/-- Canonical stochastic predictive quotient as a real control quotient;
source transition closure is not another independent supplied hypothesis. -/
noncomputable def predictiveFutureExactControlQuotient
    {X : Type uX} {A : Type uA} {O : Type uO} {I : Type uI}
    [Fintype X] [Fintype A] [Nonempty A]
    [DecidableEq O] [Fintype I]
    (K : FiniteControlledStochasticKernel X A)
    (read : X → O) (probe : I → List (A × O))
    (coeff : ReachableState (stochasticFuture K read) → I → ℝ)
    (hresolve : FutureTestsResolvePredictiveClasses K read probe coeff)
    (rbar : ReachableState (stochasticFuture K read) → A → ℝ)
    (B β : ℝ)
    (hr : ∀ c a, |rbar c a| ≤ B)
    (hβpos : 0 < β) (hβlt : β < 1) :
    letI : Fintype (ReachableState (stochasticFuture K read)) :=
      Fintype.ofFinite _
    ExactControlQuotient X
      (ReachableState (stochasticFuture K read)) (fun _ => A) := by
  exact exactControlFromStochasticQuotient K
    (stochasticFuture K read)
    (stochastic_future_tests_force_strong_lumpability
      K read probe coeff hresolve)
    rbar B β hr hβpos hβlt

/-- NEW cross-level consequence: observable predictions imply exact optimal
value pullback and lifted macro greedy optimality against every causal
history-dependent randomized MICRO-policy, by actual application of
the frozen P-QUO-01 theorem, not duplicate Bellman reasoning. -/
theorem future_observability_yields_micro_optimal_macro_control
    {X : Type uX} {A : Type uA} {O : Type uO} {I : Type uI}
    [Fintype X] [Fintype A] [Nonempty A]
    [DecidableEq O] [Fintype I]
    (K : FiniteControlledStochasticKernel X A)
    (read : X → O) (probe : I → List (A × O))
    (coeff : ReachableState (stochasticFuture K read) → I → ℝ)
    (hresolve : FutureTestsResolvePredictiveClasses K read probe coeff)
    (rbar : ReachableState (stochasticFuture K read) → A → ℝ)
    (B β : ℝ)
    (hr : ∀ c a, |rbar c a| ≤ B)
    (hβpos : 0 < β) (hβlt : β < 1) :
    letI : Fintype (ReachableState (stochasticFuture K read)) :=
      Fintype.ofFinite _
    let Q := predictiveFutureExactControlQuotient
      K read probe coeff hresolve rbar B β hr hβpos hβlt
    (∀ x : X,
      Q.micro.optimalValue x = Q.macroModel.optimalValue (Q.f x)) ∧
    (∀ (x : X) (a : A),
      Q.micro.qValue Q.micro.optimalValue x a =
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a) ∧
    (∀ {t : ℕ} (x : X),
      infiniteValue (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
        Q.micro (t := t) x = Q.micro.optimalValue x) ∧
    (∀ (π : CausalPolicy X (fun x => A)) {t : ℕ}
       (h : π.Memory t),
       infiniteValue π Q.micro h ≤
         Q.micro.optimalValue (π.current h)) := by
  classical
  letI : Fintype (ReachableState (stochasticFuture K read)) :=
    Fintype.ofFinite _
  exact (predictiveFutureExactControlQuotient
    K read probe coeff hresolve rbar B β hr hβpos hβlt).p_quo_01

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
