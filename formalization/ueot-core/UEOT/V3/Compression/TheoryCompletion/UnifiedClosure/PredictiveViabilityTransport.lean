import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictiveOptimalControlLift
import Mathlib.Tactic

/-!
# UMC cross-layer object-viability transport through a real prediction quotient

A finite exact control quotient (constructed from future observability of
the SAME source kernel by PredictiveOptimalControlLift) transports a
MACRO-registered viable object-region to the microprocess, provided its
predicate is a saturated macro set and all macro actions preserve it
at positive support. This is a policy-robust finite-path implication.

The required macro viability set and the support-closure property are
explicit inputs. We do NOT infer a physical biological object, provenance,
intrinsic purpose, controller repair or resource accounting.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

universe uX uY uA uO uI

/-- Fundamental source-to-macro support bound. A micro transition
probability is at most the total actual source mass into its macro class.
This follows from nonnegativity and the P-QUO block-pushforward field. -/
theorem micro_transition_mass_le_macro_class_mass
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (x z : X) (a : A) :
    Q.micro.transition x a z ≤
      Q.macroModel.transition (Q.f x) a (Q.f z) := by
  classical
  have hnonneg : ∀ y ∈ (Finset.univ : Finset X),
      0 ≤ (if Q.f y = Q.f z then
        Q.micro.transition x a y else 0) := by
    intro y _
    split_ifs
    · exact Q.micro.transition_nonneg x a y
    · exact le_refl _
  have hle : Q.micro.transition x a z ≤
      fiberMass Q.f (Q.micro.transition x a) (Q.f z) := by
    unfold fiberMass
    have h := Finset.single_le_sum (s := Finset.univ) hnonneg
      (a := z) (Finset.mem_univ z)
    simpa using h
  calc
    Q.micro.transition x a z ≤
      fiberMass Q.f (Q.micro.transition x a) (Q.f z) := hle
    _ = Q.macroModel.transition (Q.f x) a (Q.f z) :=
      Q.transition_closed x a (Q.f z)

/-- If a macro region is closed on positive support for EVERY action,
its micro preimage is automatically closed. -/
theorem macro_support_viability_lifts_to_micro
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop)
    (hclosed : ∀ c a d, safe c → ¬safe d →
      Q.macroModel.transition c a d = 0)
    (x z : X) (a : A)
    (hsafe : safe (Q.f x))
    (hpositive : 0 < Q.micro.transition x a z) :
    safe (Q.f z) := by
  by_contra hbad
  have hmacro := hclosed (Q.f x) a (Q.f z) hsafe hbad
  have hbound := micro_transition_mass_le_macro_class_mass Q x z a
  linarith

/-- Weaker and more organism-like invariant: only the chosen controller
sigma must keep the viable set closed. Dangerous other actions are allowed.
This is distinct from all-action robustness and closer to the P2 GOA
criterion that a controller maintains its own feasible region. -/
theorem macro_policy_support_viability_lifts_to_micro
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) (sigma : Y → A)
    (hclosed : ∀ c d, safe c → ¬safe d →
      Q.macroModel.transition c (sigma c) d = 0)
    (x z : X) (hsafe : safe (Q.f x))
    (hpositive : 0 < Q.micro.transition x (sigma (Q.f x)) z) :
    safe (Q.f z) := by
  by_contra hbad
  have hmacro := hclosed (Q.f x) (Q.f z) hsafe hbad
  have hbound := micro_transition_mass_le_macro_class_mass
    Q x z (sigma (Q.f x))
  linarith

/-- A concrete finite list of actions and realized microscopic successor
states. Each hop must have strictly positive probability under the ACTUAL
source dynamics, not under a fabricated unrelated macro process. -/
def PositiveRealization
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A)) :
    X → List (A × X) → Prop
  | _, [] => True
  | x, (a,z)::rest =>
      0 < Q.micro.transition x a z ∧ PositiveRealization Q z rest

/-- Last microstate of the registered action/transition path. -/
def realizedEndpoint {X : Type uX} {A : Type uA}
    (x : X) : List (A × X) → X
  | [] => x
  | (_,z)::rest => realizedEndpoint z rest

/-- All finite positive-support controlled trajectories retain a macro
object-region certificate once the actual macro transition kernel is closed
under every action. This is a genuine multi-step cross-layer consequence. -/
theorem macro_viability_survives_every_finite_micro_path
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop)
    (hclosed : ∀ c a d, safe c → ¬safe d →
      Q.macroModel.transition c a d = 0)
    (x : X) (path : List (A × X))
    (hsafe : safe (Q.f x))
    (hpath : PositiveRealization Q x path) :
    safe (Q.f (realizedEndpoint x path)) := by
  induction path generalizing x with
  | nil => exact hsafe
  | cons pair tail ih =>
      rcases pair with ⟨a,z⟩
      rcases hpath with ⟨hpositive, htail⟩
      have hz : safe (Q.f z) :=
        macro_support_viability_lifts_to_micro
          Q safe hclosed x z a hsafe hpositive
      exact ih z hz htail

/-- New UMC --> P-QUO --> operational-object bridge. The source K/read
future-word identifiability supplies the dynamical quotient, with an
additional REGISTERED macro viability property. Neither strong lumpability
nor micro safety transitions are separately supplied. -/
theorem stochastic_future_closed_region_is_micro_path_invariant
    {X : Type uX} {A : Type uA} {O : Type uO} {I : Type uI}
    [Fintype X] [Fintype A] [Nonempty A]
    [DecidableEq O] [Fintype I]
    (K : FiniteControlledStochasticKernel X A)
    (read : X → O) (probe : I → List (A × O))
    (coeff : ReachableState (stochasticFuture K read) → I → ℝ)
    (hresolve : FutureTestsResolvePredictiveClasses K read probe coeff)
    (rbar : ReachableState (stochasticFuture K read) → A → ℝ)
    (B β : ℝ) (hr : ∀ c a, |rbar c a| ≤ B)
    (hβpos : 0 < β) (hβlt : β < 1)
    (safe : ReachableState (stochasticFuture K read) → Prop)
    (hclosed :
      letI : Fintype (ReachableState (stochasticFuture K read)) :=
        Fintype.ofFinite _
      let Q := predictiveFutureExactControlQuotient
        K read probe coeff hresolve rbar B β hr hβpos hβlt
      ∀ c a d, safe c → ¬safe d →
        Q.macroModel.transition c a d = 0)
    (x : X) (path : List (A × X))
    (hstart : safe (toReachable (stochasticFuture K read) x))
    (hpath :
      letI : Fintype (ReachableState (stochasticFuture K read)) :=
        Fintype.ofFinite _
      PositiveRealization
        (predictiveFutureExactControlQuotient
          K read probe coeff hresolve rbar B β hr hβpos hβlt) x path) :
    safe (toReachable (stochasticFuture K read)
      (realizedEndpoint x path)) := by
  classical
  letI : Fintype (ReachableState (stochasticFuture K read)) :=
    Fintype.ofFinite _
  let Q := predictiveFutureExactControlQuotient
    K read probe coeff hresolve rbar B β hr hβpos hβlt
  exact macro_viability_survives_every_finite_micro_path
    Q safe hclosed x path hstart hpath

/-- Realized microscopic path under a prescribed macro stationary policy.
The choices are not arbitrary: each action is sigma of the current macro
state, while the source transition is still the real micro transition. -/
def PositivePolicyRealization
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (sigma : Y → A) : X → List X → Prop
  | _, [] => True
  | x, z::rest =>
      0 < Q.micro.transition x (sigma (Q.f x)) z ∧
        PositivePolicyRealization Q sigma z rest

def realizedPolicyEndpoint {X : Type uX}
    (x : X) : List X → X
  | [] => x
  | z::rest => realizedPolicyEndpoint z rest

/-- One registered macro controller keeps a viable object-region invariant
along ANY positive-probability finite physical path, irrespective of other
unsafe admissible actions. This is not a proof of intrinsic controller repair. -/
theorem macro_policy_viability_survives_every_finite_micro_path
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) (sigma : Y → A)
    (hclosed : ∀ c d, safe c → ¬safe d →
      Q.macroModel.transition c (sigma c) d = 0)
    (x : X) (path : List X)
    (hstart : safe (Q.f x))
    (hpath : PositivePolicyRealization Q sigma x path) :
    safe (Q.f (realizedPolicyEndpoint x path)) := by
  induction path generalizing x with
  | nil => exact hstart
  | cons z tail ih =>
      rcases hpath with ⟨hpositive, htail⟩
      have hz : safe (Q.f z) :=
        macro_policy_support_viability_lifts_to_micro
          Q safe sigma hclosed x z hstart hpositive
      exact ih z hz htail

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
