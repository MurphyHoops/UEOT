import UEOT.V3.Compression.QuotientDescent
import UEOT.V3.PredictionUpdate

/-!
# Recursive sufficient state as input-parametrized quotient descent

This module tests whether a proposed M-RS / recursive-sufficient-state
generator is actually independent of M-QD.

The generic setup is:

* `C : H -> S` is the current state representation of a richer history;
* `R : H -> E -> T` is the next response after one new input `e : E`;
* equal current states should imply equal next responses for every input.

The key observation is that this is exactly fibre compatibility of the curried
map `H -> (E -> T)`.  Therefore the unique recursive update on the *reachable
state image* is a direct instance of M-QD's universal property.

This separation matters for P-PRED-03: quotient descent gives the unique update
on reachable canonical states, while the source theorem additionally builds a
jointly measurable extension on the whole ambient coordinate space.  The latter
is a domain-specific realization obligation, not part of set-level M-QD.
-/

namespace UEOT.V3.Compression.RecursiveSufficientState

open Function
open UEOT.V3.Compression.QuotientDescent
open UEOT.V3

universe uH uS uE uT uA uO uI uJ

/-- The actually reachable state image of a history representation. -/
abbrev ReachableState {H : Type uH} {S : Type uS} (C : H → S) :=
  Set.range C

/-- Every history maps canonically into the reachable-state subtype. -/
def toReachable {H : Type uH} {S : Type uS} (C : H → S) :
    H → ReachableState C :=
  fun h => ⟨C h, ⟨h, rfl⟩⟩

theorem toReachable_surjective
    {H : Type uH} {S : Type uS} (C : H → S) :
    Surjective (toReachable C) := by
  rintro ⟨s, ⟨h, rfl⟩⟩
  exact ⟨h, rfl⟩

/-- Recursive state closure: histories with the same current state produce the
same next response for every new input. -/
def InputFiberCompatible
    {H : Type uH} {S : Type uS} {E : Type uE} {T : Type uT}
    (C : H → S) (R : H → E → T) : Prop :=
  ∀ ⦃h h' : H⦄, C h = C h' → ∀ e, R h e = R h' e

/-- Input-wise recursive closure is exactly ordinary M-QD fibre compatibility
after currying the input into the codomain. -/
theorem inputFiberCompatible_iff_fiberCompatible_curried
    {H : Type uH} {S : Type uS} {E : Type uE} {T : Type uT}
    (C : H → S) (R : H → E → T) :
    InputFiberCompatible C R ↔
      FiberCompatible (toReachable C) R := by
  constructor
  · intro hcompat h h' hreach
    apply funext
    intro e
    apply hcompat
    exact congrArg Subtype.val hreach
  · intro hcompat h h' hstate e
    have hreach : toReachable C h = toReachable C h' := by
      apply Subtype.ext
      exact hstate
    exact congrFun (hcompat hreach) e

/-- Universal recursive-update property on reachable states.

No surjectivity of `C : H -> S` onto the ambient state type is assumed.  The
canonical map into `Set.range C` is surjective, so M-QD gives one and only one
update on states that can actually occur. -/
theorem existsUnique_reachableUpdate
    {H : Type uH} {S : Type uS} {E : Type uE} {T : Type uT}
    (C : H → S) (R : H → E → T)
    (hcompat : InputFiberCompatible C R) :
    ∃! U : ReachableState C → E → T,
      ∀ h e, U (toReachable C h) e = R h e := by
  have hfiber : FiberCompatible (toReachable C) R :=
    (inputFiberCompatible_iff_fiberCompatible_curried C R).mp hcompat
  rcases existsUnique_descend
      (toReachable C) R (toReachable_surjective C) hfiber with
    ⟨U, hfactor, hunique⟩
  refine ⟨U, ?_, ?_⟩
  · intro h e
    exact congrFun (congrFun hfactor h) e
  · intro V hV
    apply hunique V
    funext h
    funext e
    exact hV h e

/-- If every ambient state is reachable, recursive sufficiency gives a unique
update directly on the ambient state space.  This is the interface needed by
finite-control assembly: the control state type contains no unreachable
coordinates. -/
theorem existsUnique_ambientUpdate_of_surjective
    {H : Type uH} {S : Type uS} {E : Type uE} {T : Type uT}
    (C : H → S) (hC : Surjective C)
    (R : H → E → T)
    (hcompat : InputFiberCompatible C R) :
    ∃! U : S → E → T,
      ∀ h e, U (C h) e = R h e := by
  have hfiber : FiberCompatible C R := by
    intro h h' hstate
    apply funext
    intro e
    exact hcompat hstate e
  rcases existsUnique_descend C R hC hfiber with ⟨U, hfactor, hunique⟩
  refine ⟨U, ?_, ?_⟩
  · intro h e
    exact congrFun (congrFun hfactor h) e
  · intro V hV
    apply hunique V
    funext h
    funext e
    exact hV h e

/-- Conversely, any recursive update on the ambient state immediately implies
the fibre-compatibility obligation.  No surjectivity is needed. -/
theorem inputFiberCompatible_of_update
    {H : Type uH} {S : Type uS} {E : Type uE} {T : Type uT}
    (C : H → S) (R : H → E → T)
    (U : S → E → T)
    (hfactor : ∀ h e, U (C h) e = R h e) :
    InputFiberCompatible C R := by
  intro h h' hstate e
  calc
    R h e = U (C h) e := (hfactor h e).symm
    _ = U (C h') e := by rw [hstate]
    _ = R h' e := hfactor h' e

/-! ## P-PRED-03 adapter -/

/-- The history-level continuation-response update in P-PRED-03 is recursively
compatible with the canonical predictive state.  This is the exact set-level
obligation needed for M-QD descent on reachable canonical states.

The theorem deliberately does not claim the full P-PRED-03 endpoint: joint
measurability and extension from the reachable image to the whole ambient
coordinate space remain source-specific obligations. -/
theorem pred03_inputFiberCompatible
    {H : Type uH} {A : Type uA} {O : Type uO} {I : Type uI} {J : Type uJ}
    (cl : PredictionUpdate.RecursiveCoordinateClosure A O I J)
    (C : H → (J → ℝ))
    (jointH : H → A → O → I → ℝ)
    (obsH : H → A → O → ℝ)
    (hJoint :
      ∀ h a o i,
        jointH h a o i = C h (cl.jointIndex a o i))
    (hObs :
      ∀ h a o,
        obsH h a o = C h (cl.obsIndex a o)) :
    InputFiberCompatible C
      (fun h (ao : A × O) =>
        PredictionUpdate.historyBayesResponseVector
          jointH obsH h ao.1 ao.2) := by
  apply inputFiberCompatible_of_update C
    (fun h (ao : A × O) =>
      PredictionUpdate.historyBayesResponseVector
        jointH obsH h ao.1 ao.2)
    (fun c (ao : A × O) => PredictionUpdate.coordinateBayesUpdate cl c ao.1 ao.2)
  intro h ao
  symm
  exact PredictionUpdate.coordinateBayesUpdate_recovers_history
    cl C jointH obsH hJoint hObs h ao.1 ao.2

/-- P-PRED-03's recursive response has a unique update on the reachable
canonical-state image by M-QD alone.  The source theorem's stronger measurable
ambient extension is intentionally not hidden inside this result. -/
theorem pred03_existsUnique_reachableUpdate
    {H : Type uH} {A : Type uA} {O : Type uO} {I : Type uI} {J : Type uJ}
    (cl : PredictionUpdate.RecursiveCoordinateClosure A O I J)
    (C : H → (J → ℝ))
    (jointH : H → A → O → I → ℝ)
    (obsH : H → A → O → ℝ)
    (hJoint :
      ∀ h a o i,
        jointH h a o i = C h (cl.jointIndex a o i))
    (hObs :
      ∀ h a o,
        obsH h a o = C h (cl.obsIndex a o)) :
    ∃! U : ReachableState C → (A × O) → (I → ℝ),
      ∀ h a o,
        U (toReachable C h) (a, o) =
          PredictionUpdate.historyBayesResponseVector
            jointH obsH h a o := by
  rcases existsUnique_reachableUpdate C
      (fun h (ao : A × O) =>
        PredictionUpdate.historyBayesResponseVector
          jointH obsH h ao.1 ao.2)
      (pred03_inputFiberCompatible cl C jointH obsH hJoint hObs) with
    ⟨U, hU, huniq⟩
  refine ⟨U, ?_, ?_⟩
  · intro h a o
    exact hU h (a, o)
  · intro V hV
    apply huniq V
    intro h ao
    rcases ao with ⟨a, o⟩
    exact hV h a o

end UEOT.V3.Compression.RecursiveSufficientState
