import UEOT.V3.Compression.RecursiveSufficientState
import UEOT.V3.Compression.QuotientGauge

/-!
# SISC: process-derived minimal recursive predictive state (finite words)

The state is not postulated. It is constructed from a controlled deterministic
world transition `step : X → A → X` and an observable `read : X → O` by
collecting responses to *all finite intervention words* `List A`.

This yields a canonical exact observational quotient that (a) is closed under
all declared actions and (b) is coarsest among ALL summaries that preserve
observations and have a deterministic recursive update. It is a purely
set-level controlled analogue of predictive-state/Nerode equivalence, not a
novel universal Objecthood axiom or a stochastic/measurable realization.

The construction deliberately does not assume the fibre-compatibility that
was needed as a premise in the old `RecursiveSufficientState` generic result.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.QuotientDescent
open UEOT.V3.Compression.RecursiveSufficientState
open UEOT.V3.Compression.QuotientGauge

universe uX uA uO uS

/-- Evolve the underlying process under a finite ordered action word. -/
def runInterventions {X : Type uX} {A : Type uA}
    (step : X → A → X) (x : X) : List A → X
  | [] => x
  | a :: as => runInterventions step (step x a) as

/-- The experimentally declared family of *all finite future responses*.
The empty word gives the present response. -/
def futureResponse {X : Type uX} {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) (x : X) : List A → O :=
  fun as => read (runInterventions step x as)

/-- The canonical observational-predictive state, restricted to reachable
response signatures so no unobserved or fictitious state values are added. -/
abbrev CanonicalFutureState {X : Type uX} {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) :=
  ReachableState (futureResponse step read)

/-- Every process state has an unambiguous canonical response-state label. -/
def canonicalFuture {X : Type uX} {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) :
    X → CanonicalFutureState step read :=
  toReachable (futureResponse step read)

/-- The entire future signature after action `a` is the current signature
evaluated at interventions prefixed by `a`; this is a definitional law. -/
theorem futureResponse_step
    {X : Type uX} {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) (x : X) (a : A) (as : List A) :
    futureResponse step read (step x a) as =
      futureResponse step read x (a :: as) := rfl

/-- **Automatic recursion congruence.** Two states with identical *all-future*
responses necessarily have identical all-future responses after any action.
This is proved from process execution itself, without assuming congruence. -/
theorem futureResponse_inputFiberCompatible
    {X : Type uX} {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) :
    InputFiberCompatible (futureResponse step read)
      (fun x a => futureResponse step read (step x a)) := by
  intro x y hEq a
  funext as
  change futureResponse step read x (a :: as) =
    futureResponse step read y (a :: as)
  exact congrFun hEq (a :: as)

/-- **Existence and uniqueness of the canonical action update**, derived by
M-RS/M-QD's quotient universal property. No action update was given on the
quotient or assumed to exist. -/
theorem unique_canonical_future_update
    {X : Type uX} {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) :
    ∃! update : CanonicalFutureState step read → A →
      CanonicalFutureState step read,
      ∀ x a, update (canonicalFuture step read x) a =
        canonicalFuture step read (step x a) := by
  exact existsUnique_reachableUpdate (futureResponse step read)
    (fun x a => toReachable (futureResponse step read) (step x a))
    (by
      intro x y hEq a
      apply Subtype.ext
      exact futureResponse_inputFiberCompatible step read hEq a)

/-- Two histories with the same recursive summary and present response must
agree after **every finite input word**. The induction derives, rather than
assumes, that the summary is sufficient for the entire future experiment. -/
theorem recursive_summary_predicts_all_futures
    {X : Type uX} {A : Type uA} {O : Type uO} {S : Type uS}
    (step : X → A → X) (read : X → O) (summary : X → S)
    (hread : ∀ x y, summary x = summary y → read x = read y)
    (hupdate : ∀ x y, summary x = summary y →
      ∀ a, summary (step x a) = summary (step y a))
    (x y : X) (heq : summary x = summary y) :
    futureResponse step read x = futureResponse step read y := by
  funext as
  induction as generalizing x y with
  | nil => exact hread x y heq
  | cons a as ih =>
      exact ih (step x a) (step y a) (hupdate x y heq a)

/-- The canonical *all-future state* is the **minimal sufficient recursive
state**: any other exact observation-preserving and action-closed summary
factors uniquely onto it, on the summary's actually reachable image. -/
theorem canonical_future_minimal_among_recursive_summaries
    {X : Type uX} {A : Type uA} {O : Type uO} {S : Type uS}
    (step : X → A → X) (read : X → O) (summary : X → S)
    (hread : ∀ x y, summary x = summary y → read x = read y)
    (hupdate : ∀ x y, summary x = summary y →
      ∀ a, summary (step x a) = summary (step y a)) :
    ∃! factor : ReachableState summary → CanonicalFutureState step read,
      ∀ x, factor (toReachable summary x) = canonicalFuture step read x := by
  have hcompat : FiberCompatible (toReachable summary)
      (canonicalFuture step read) := by
    intro x y heq
    apply Subtype.ext
    exact recursive_summary_predicts_all_futures
      step read summary hread hupdate x y (congrArg Subtype.val heq)
  rcases existsUnique_descend (toReachable summary)
      (canonicalFuture step read) (toReachable_surjective summary) hcompat
      with ⟨factor, hfactor, hunique⟩
  refine ⟨factor, ?_, ?_⟩
  · intro x
    exact congrFun hfactor x
  · intro other hother
    apply hunique other
    funext x
    exact hother x

/-- The immediate response is recoverable from the canonical state. -/
theorem canonical_future_contains_present_response
    {X : Type uX} {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) (x : X) :
    (canonicalFuture step read x).1 [] = read x := rfl

/-- If all future responses are equal, their current responses are equal. -/
theorem current_response_of_equal_future
    {X : Type uX} {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) {x y : X}
    (h : canonicalFuture step read x = canonicalFuture step read y) :
    read x = read y := by
  have heq := congrArg Subtype.val h
  exact congrFun heq []

/-- Two minimal exact recursive summaries of one controlled process differ
only by a unique relabeling of their reachable states. This upgrades the
universal map to gauge-invariant *object-state representation semantics*. -/
theorem exact_future_summary_unique_up_to_relabeling
    {X : Type uX} {A : Type uA} {O : Type uO} {S : Type uS}
    (step : X → A → X) (read : X → O) (summary : X → S)
    (hExact : ∀ x y, summary x = summary y ↔
      futureResponse step read x = futureResponse step read y) :
    ∃! e : ReachableState summary ≃ CanonicalFutureState step read,
      ∀ x, e (toReachable summary x) = canonicalFuture step read x := by
  have hSame : SameFibers (toReachable summary)
      (canonicalFuture step read) := by
    intro x y
    constructor
    · intro h
      apply Subtype.ext
      exact (hExact x y).mp (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact (hExact x y).mpr (congrArg Subtype.val h)
  obtain ⟨e, he, huniq⟩ :=
    (sameFibers_iff_existsUnique_equiv (toReachable summary)
      (canonicalFuture step read) (toReachable_surjective summary)
      (toReachable_surjective (futureResponse step read))).mp hSame
  refine ⟨e, ?_, ?_⟩
  · intro x
    exact congrFun he x
  · intro f hf
    apply huniq
    funext x
    exact hf x

/-- Concrete hidden-state witness: two states have the same present response,
yet an allowed one-step intervention reveals that their future signatures
differ. Thus instantaneous observational fibres need not be process-stable. -/
theorem instant_observation_can_hide_future_difference :
    ∃ (step : (Bool × Bool) → PUnit → (Bool × Bool))
      (read : (Bool × Bool) → Bool)
      (x y : Bool × Bool),
      read x = read y ∧
        futureResponse step read x ≠ futureResponse step read y := by
  let step : (Bool × Bool) → PUnit → (Bool × Bool) :=
    fun x _ => (x.2, x.2)
  let read : (Bool × Bool) → Bool := Prod.fst
  refine ⟨step, read, (false, false), (false, true), rfl, ?_⟩
  intro h
  have hword := congrFun h [PUnit.unit]
  have : false = true := by
    simpa [futureResponse, runInterventions, step, read] using hword
  exact Bool.false_ne_true this

/-- Even perfect access to *every declared finite intervention word* need not
recover the physical token, if the response interface itself does not
separate tokens. Thus the canonical quotient is predictive, not ontic. -/
theorem complete_future_response_can_merge_distinct_tokens :
    ∃ (step : Bool → PUnit → Bool) (read : Bool → PUnit),
      false ≠ true ∧
        futureResponse step read false = futureResponse step read true := by
  refine ⟨(fun x _ => x), (fun _ => PUnit.unit),
    Bool.false_ne_true, ?_⟩
  funext as
  exact Subsingleton.elim _ _

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
