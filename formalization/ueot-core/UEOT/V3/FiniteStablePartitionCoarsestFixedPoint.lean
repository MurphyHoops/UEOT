import UEOT.V3.FiniteStablePartitionTermination
import UEOT.V3.FiniteStablePartitionCoarsest

namespace UEOT.V3.FiniteStablePartition

open Finset

universe uX uA uR uO

variable {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
variable [Fintype X]

/-- Frozen §28.5 induction step: every stable refinement `Q` of the current
partition `S` also refines the next exact signature refinement of `S`. -/
theorem stable_refinement_refines_refine
    [Fintype A]
    (M : Model X A R O) (Q S : Setoid X)
    (hQS : Refines Q S) (hQ : Stable M Q) :
    Refines Q (refineSetoid M S) := by
  classical
  intro x y hxy
  refine ⟨hQS hxy, ?_⟩
  intro a z
  rw [blockMass_eq_sum_blockFinset, blockMass_eq_sum_blockFinset]
  let selected : Finset (Finset X) := classBlocksInside Q S z
  have hunion : selected.biUnion id = blockFinset S z := by
    have h := unionClassBlocksInside_eq_blockFinset Q S hQS z
    simpa [selected, unionClassBlocksInside] using h
  have hsub : (selected : Set (Finset X)) ⊆ (classBlocks Q : Set (Finset X)) := by
    intro t ht
    have hinside := (mem_classBlocksInside Q S z t).1 ht
    exact hinside.1
  have hdisj : Set.PairwiseDisjoint (selected : Set (Finset X)) id := by
    intro t ht u hu htu
    exact classBlocks_pairwiseDisjoint Q (hsub ht) (hsub hu) htu
  conv_lhs =>
    rw [← hunion, Finset.sum_biUnion hdisj]
  conv_rhs =>
    rw [← hunion, Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro t ht
  have htclass : t ∈ classBlocks Q := hsub ht
  obtain ⟨w, hblock⟩ := exists_rep_of_mem_classBlocks Q htclass
  have hmass := hQ hxy a w
  rw [blockMass_eq_sum_blockFinset, blockMass_eq_sum_blockFinset] at hmass
  simpa [hblock] using hmass

/-- A stable refinement of `S` refines every partition visited by the exact
algorithm, hence the terminal fixed point. -/
theorem stable_refinement_refines_stabilizeAux
    (M : Model X A R O) (Q S : Setoid X) (hA : Fintype A)
    (hQS : Refines Q S) (hQ : Stable M Q) :
    Refines Q (stabilizeAux M S hA) := by
  letI : Fintype A := hA
  unfold stabilizeAux
  exact refines_stabilizeStep_of_closed
    (fun T => refineSetoid M T)
    (fun T => (relPairs T).card)
    (fun T h => relPairs_card_lt_of_refine_ne M T h)
    Q S hQS
    (fun T hQT => stable_refinement_refines_refine M Q T hQT hQ)

/-- A stable refinement of `S` refines every partition visited by the terminating
algorithm, hence also the terminal fixed point. -/
theorem stable_refinement_refines_stabilize
    [Fintype A]
    (M : Model X A R O) (Q S : Setoid X)
    (hQS : Refines Q S) (hQ : Stable M Q) :
    Refines Q (stabilize M S) := by
  unfold stabilize
  exact stable_refinement_refines_stabilizeAux M Q S
    (inferInstance : Fintype A) hQS hQ

/-- Terminal partition produced by frozen §28.5's exact refinement algorithm. -/
noncomputable def terminalSetoid
    [Fintype A]
    (M : Model X A R O) : Setoid X :=
  stabilize M (initialSetoid M)

/-- The terminal partition refines the source initial output/reward partition. -/
theorem terminal_refines_initial
    [Fintype A]
    (M : Model X A R O) :
    Refines (terminalSetoid M) (initialSetoid M) :=
  stabilize_refines M (initialSetoid M)

/-- The terminal partition is controlled-stable. -/
theorem terminal_stable
    [Fintype A]
    (M : Model X A R O) :
    Stable M (terminalSetoid M) :=
  stabilize_stable M (initialSetoid M)

/-- The terminal partition is the coarsest stable refinement of the initial
output/reward partition: every other stable refinement is finer than it. -/
theorem terminal_coarsest
    [Fintype A]
    (M : Model X A R O) (Q : Setoid X)
    (hQinit : Refines Q (initialSetoid M))
    (hQstable : Stable M Q) :
    Refines Q (terminalSetoid M) :=
  stable_refinement_refines_stabilize M Q (initialSetoid M) hQinit hQstable

end UEOT.V3.FiniteStablePartition
