import UEOT.V3.FiniteStablePartition

namespace UEOT.V3.FiniteStablePartition

open Finset

universe uX uA uR uO

variable {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
variable [Fintype X]

/-- Any strict refinement strictly decreases the finite number of related
ordered pairs. -/
theorem relPairs_card_lt_of_refines_ne
    {S T : Setoid X} (hST : Refines S T) (hne : S ≠ T) :
    (relPairs S).card < (relPairs T).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.2
  refine ⟨relPairs_mono hST, ?_⟩
  intro hrel
  exact hne (setoid_eq_of_relPairs_eq hrel)

/-- Every strict exact signature refinement strictly decreases the finite number
of related ordered pairs. -/
theorem relPairs_card_lt_of_refine_ne
    [Fintype A]
    (M : Model X A R O) (S : Setoid X)
    (hne : refineSetoid M S ≠ S) :
    (relPairs (refineSetoid M S)).card < (relPairs S).card :=
  relPairs_card_lt_of_refines_ne (refineSetoid_refines M S) hne

/-- Generic exact stabilization of a step equipped with an explicit natural
well-founded measure.  The recursive kernel itself has no finite-type
assumptions; all finiteness enters only when a concrete measure is supplied. -/
noncomputable def stabilizeStep
    (step : Setoid X → Setoid X)
    (measure : Setoid X → ℕ)
    (hdec : ∀ S, step S ≠ S → measure (step S) < measure S)
    (S : Setoid X) : Setoid X := by
  classical
  exact if h : step S = S then S
    else stabilizeStep step measure hdec (step S)
termination_by measure S
decreasing_by
  exact hdec S h

/-- The generic stabilization refines its starting partition whenever every
step is a refinement. -/
theorem stabilizeStep_refines
    (step : Setoid X → Setoid X)
    (measure : Setoid X → ℕ)
    (hdec : ∀ S, step S ≠ S → measure (step S) < measure S)
    (href : ∀ S, Refines (step S) S)
    (S : Setoid X) :
    Refines (stabilizeStep step measure hdec S) S := by
  classical
  unfold stabilizeStep
  split_ifs with h
  · exact Refines.refl S
  · exact (stabilizeStep_refines step measure hdec href (step S)).trans (href S)
termination_by measure S
decreasing_by
  exact hdec S h

/-- The generic stabilization terminates at a fixed point of the step. -/
theorem stabilizeStep_fixed
    (step : Setoid X → Setoid X)
    (measure : Setoid X → ℕ)
    (hdec : ∀ S, step S ≠ S → measure (step S) < measure S)
    (S : Setoid X) :
    step (stabilizeStep step measure hdec S) = stabilizeStep step measure hdec S := by
  classical
  unfold stabilizeStep
  split_ifs with h
  · exact h
  · exact stabilizeStep_fixed step measure hdec (step S)
termination_by measure S
decreasing_by
  exact hdec S h

/-- If a fixed relation `Q` is preserved by every step above it, then `Q`
refines the terminal stabilized relation.  This is the generic coarsest-fixed-
point induction principle. -/
theorem refines_stabilizeStep_of_closed
    (step : Setoid X → Setoid X)
    (measure : Setoid X → ℕ)
    (hdec : ∀ S, step S ≠ S → measure (step S) < measure S)
    (Q S : Setoid X)
    (hQS : Refines Q S)
    (hclosed : ∀ T, Refines Q T → Refines Q (step T)) :
    Refines Q (stabilizeStep step measure hdec S) := by
  classical
  unfold stabilizeStep
  split_ifs with h
  · exact hQS
  · exact refines_stabilizeStep_of_closed step measure hdec Q (step S)
      (hclosed S hQS) hclosed
termination_by measure S
decreasing_by
  exact hdec S h

/-- A fixed point is returned immediately by the generic stabilization. -/
theorem stabilizeStep_eq_self_of_fixed
    (step : Setoid X → Setoid X)
    (measure : Setoid X → ℕ)
    (hdec : ∀ S, step S ≠ S → measure (step S) < measure S)
    (S : Setoid X) (hS : step S = S) :
    stabilizeStep step measure hdec S = S := by
  classical
  unfold stabilizeStep
  simp [hS]

/-- Compatibility wrapper specializing the generic kernel to exact controlled
signature refinement.  Finiteness is used only to instantiate the explicit
relation-pair measure and its strict-descent proof. -/
noncomputable def stabilizeAux
    (M : Model X A R O) (S : Setoid X) (hA : Fintype A) : Setoid X := by
  letI : Fintype A := hA
  exact stabilizeStep
    (fun T => refineSetoid M T)
    (fun T => (relPairs T).card)
    (fun T h => relPairs_card_lt_of_refine_ne M T h)
    S

/-- Repeated exact refinement reaches a fixed point. -/
noncomputable def stabilize
    [Fintype A]
    (M : Model X A R O) (S : Setoid X) : Setoid X :=
  stabilizeAux M S (inferInstance : Fintype A)

/-- Auxiliary refinement theorem for the compatibility wrapper. -/
theorem stabilizeAux_refines
    (M : Model X A R O) (S : Setoid X) (hA : Fintype A) :
    Refines (stabilizeAux M S hA) S := by
  letI : Fintype A := hA
  unfold stabilizeAux
  exact stabilizeStep_refines
    (fun T => refineSetoid M T)
    (fun T => (relPairs T).card)
    (fun T h => relPairs_card_lt_of_refine_ne M T h)
    (fun T => refineSetoid_refines M T)
    S

/-- The terminal partition refines the starting partition. -/
theorem stabilize_refines
    [Fintype A]
    (M : Model X A R O) (S : Setoid X) :
    Refines (stabilize M S) S := by
  unfold stabilize
  exact stabilizeAux_refines M S (inferInstance : Fintype A)

/-- Auxiliary stability theorem for the compatibility wrapper. -/
theorem stabilizeAux_stable
    (M : Model X A R O) (S : Setoid X) (hA : Fintype A) :
    Stable M (stabilizeAux M S hA) := by
  letI : Fintype A := hA
  apply (refineSetoid_eq_iff_stable M (stabilizeAux M S hA)).1
  unfold stabilizeAux
  exact stabilizeStep_fixed
    (fun T => refineSetoid M T)
    (fun T => (relPairs T).card)
    (fun T h => relPairs_card_lt_of_refine_ne M T h)
    S

/-- The terminal partition is controlled-stable. -/
theorem stabilize_stable
    [Fintype A]
    (M : Model X A R O) (S : Setoid X) :
    Stable M (stabilize M S) := by
  unfold stabilize
  exact stabilizeAux_stable M S (inferInstance : Fintype A)

/-- Stable partitions are fixed immediately by the compatibility wrapper. -/
theorem stabilizeAux_eq_self_of_stable
    (M : Model X A R O) (S : Setoid X) (hA : Fintype A)
    (hS : Stable M S) :
    stabilizeAux M S hA = S := by
  letI : Fintype A := hA
  have hfix : refineSetoid M S = S :=
    (refineSetoid_eq_iff_stable M S).2 hS
  unfold stabilizeAux
  exact stabilizeStep_eq_self_of_fixed
    (fun T => refineSetoid M T)
    (fun T => (relPairs T).card)
    (fun T h => relPairs_card_lt_of_refine_ne M T h)
    S hfix

/-- Stable partitions are fixed immediately. -/
theorem stabilize_eq_self_of_stable
    [Fintype A]
    (M : Model X A R O) (S : Setoid X) (hS : Stable M S) :
    stabilize M S = S := by
  unfold stabilize
  exact stabilizeAux_eq_self_of_stable M S (inferInstance : Fintype A) hS

end UEOT.V3.FiniteStablePartition
