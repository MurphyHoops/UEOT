import UEOT.V3.FiniteStablePartitionQuotientLaw

/-!
# P-ALG-01 — stochastic normalization of the finite quotient

The quotient states are the equivalence-class blocks.  This module proves that
those blocks form an exact finite partition of the source state space and that,
for every source state and every action, the transition masses to all quotient
blocks sum to one.
-/

namespace UEOT.V3.FiniteStablePartition

open Finset

universe uX uA uR uO

variable {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
variable [Fintype X] [Fintype A]

/-- Finite collection of equivalence-class blocks, with all classical
relation-decidability kept internal. -/
noncomputable def quotientClassBlocks (S : Setoid X) : Finset (Finset X) := by
  classical
  exact (Finpartition.ofSetoid S).parts

/-- Quotient class blocks are pairwise disjoint. -/
theorem quotientClassBlocks_pairwiseDisjoint (S : Setoid X) :
    Set.PairwiseDisjoint (quotientClassBlocks S : Set (Finset X)) id := by
  classical
  unfold quotientClassBlocks
  exact (Finpartition.ofSetoid S).disjoint

/-- Union of all quotient class blocks.  The `biUnion` decidability is kept
inside this noncomputable wrapper rather than leaking into theorem signatures. -/
noncomputable def quotientClassUnion (S : Setoid X) : Finset X := by
  classical
  exact (quotientClassBlocks S).biUnion id

/-- The quotient class blocks cover the whole finite source state space. -/
theorem quotientClassUnion_eq_univ (S : Setoid X) :
    quotientClassUnion S = (Finset.univ : Finset X) := by
  classical
  unfold quotientClassUnion
  ext y
  constructor
  · intro hy
    exact Finset.mem_univ y
  · intro hy
    let t : Finset X := (Finpartition.ofSetoid S).part y
    have ht : t ∈ quotientClassBlocks S := by
      dsimp [t]
      simpa [quotientClassBlocks] using
        (Finpartition.ofSetoid S).part_mem.2 (Finset.mem_univ y)
    have hyt : y ∈ t := by
      dsimp [t]
      exact (Finpartition.ofSetoid S).mem_part (Finset.mem_univ y)
    exact Finset.mem_biUnion.mpr ⟨t, ht, hyt⟩

/-- Summing over all quotient blocks is exactly summing over the source state
space.  This is the finite partition identity used by both normalization and
finite-horizon aggregation. -/
theorem sum_over_quotientClassBlocks
    (S : Setoid X) (f : X → ℝ) :
    (∑ t ∈ quotientClassBlocks S, ∑ y ∈ t, f y) = ∑ y : X, f y := by
  classical
  have hdisj := quotientClassBlocks_pairwiseDisjoint S
  calc
    (∑ t ∈ quotientClassBlocks S, ∑ y ∈ t, f y)
        = ∑ y ∈ quotientClassUnion S, f y := by
            symm
            unfold quotientClassUnion
            exact Finset.sum_biUnion hdisj
    _ = ∑ y ∈ (Finset.univ : Finset X), f y := by
          rw [quotientClassUnion_eq_univ]
    _ = ∑ y : X, f y := rfl

/-- For every action and source state, transition probability mass over all
quotient blocks is exactly one.  Thus the block quotient is a genuine finite
stochastic transition law, not merely a collection of nonnegative weights. -/
theorem transition_sum_over_quotientClassBlocks
    (M : Model X A R O) (S : Setoid X) (a : A) (x : X) :
    (∑ t ∈ quotientClassBlocks S, ∑ y ∈ t, M.transition a x y) = 1 := by
  calc
    (∑ t ∈ quotientClassBlocks S, ∑ y ∈ t, M.transition a x y)
        = ∑ y : X, M.transition a x y :=
          sum_over_quotientClassBlocks S (fun y => M.transition a x y)
    _ = 1 := M.transition_sum_one a x

end UEOT.V3.FiniteStablePartition
