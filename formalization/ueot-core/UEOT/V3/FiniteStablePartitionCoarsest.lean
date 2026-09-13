import UEOT.V3.FiniteStablePartition

namespace UEOT.V3.FiniteStablePartition

open Finset

universe uX uA uR uO

variable {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
variable [Fintype X]

/-- The concrete finite block represented by `z`. -/
noncomputable def blockFinset (S : Setoid X) (z : X) : Finset X := by
  classical
  exact Finset.univ.filter (fun y => S.r y z)

@[simp] theorem mem_blockFinset (S : Setoid X) (z y : X) :
    y ∈ blockFinset S z ↔ S.r y z := by
  classical
  simp [blockFinset]

/-- `blockMass` is the ordinary finite sum over the represented block. -/
theorem blockMass_eq_sum_blockFinset
    (M : Model X A R O) (S : Setoid X) (a : A) (x z : X) :
    blockMass M S a x z = ∑ y ∈ blockFinset S z, M.transition a x y := by
  classical
  unfold blockMass blockFinset
  rw [Finset.sum_filter]

/-- The finite set of equivalence classes of `S`, with all classical
relation-decidability kept internal. -/
noncomputable def classBlocks (S : Setoid X) : Finset (Finset X) := by
  classical
  exact (Finpartition.ofSetoid S).parts

/-- Exactly those `Q`-class blocks contained in the represented `S`-block.
The filter is hidden inside a noncomputable definition so no decidability
artifact leaks into theorem statements. -/
noncomputable def classBlocksInside (Q S : Setoid X) (z : X) : Finset (Finset X) := by
  classical
  exact (classBlocks Q).filter (fun t => t ⊆ blockFinset S z)

@[simp] theorem mem_classBlocksInside
    (Q S : Setoid X) (z : X) (t : Finset X) :
    t ∈ classBlocksInside Q S z ↔
      t ∈ classBlocks Q ∧ t ⊆ blockFinset S z := by
  classical
  simp [classBlocksInside]

/-- The class blocks are pairwise disjoint. -/
theorem classBlocks_pairwiseDisjoint (S : Setoid X) :
    Set.PairwiseDisjoint (classBlocks S : Set (Finset X)) id := by
  classical
  unfold classBlocks
  exact (Finpartition.ofSetoid S).disjoint

/-- Every listed class block has a representative whose explicit block is that
class.  Representative membership is intentionally kept inside the proof so
no `DecidableEq X` artifact leaks into this theorem statement. -/
theorem exists_rep_of_mem_classBlocks
    (S : Setoid X) {t : Finset X} (ht : t ∈ classBlocks S) :
    ∃ w : X, blockFinset S w = t := by
  classical
  have ht' : t ∈ (Finpartition.ofSetoid S).parts := by
    simpa [classBlocks] using ht
  obtain ⟨w, hw⟩ := (Finpartition.ofSetoid S).nonempty_of_mem_parts ht'
  have hpart : (Finpartition.ofSetoid S).part w = t :=
    (Finpartition.ofSetoid S).part_eq_of_mem ht' hw
  refine ⟨w, ?_⟩
  rw [← hpart]
  ext y
  rw [mem_blockFinset, Finpartition.mem_part_ofSetoid_iff_rel]
  exact ⟨fun hyw => S.symm hyw, fun hwy => S.symm hwy⟩

/-- The union of the selected class blocks, with the `DecidableEq X` needed by
`Finset.biUnion` kept internal rather than leaked into public theorem types. -/
noncomputable def unionClassBlocksInside (Q S : Setoid X) (z : X) : Finset X := by
  classical
  exact (classBlocksInside Q S z).biUnion id

/-- If `Q` refines `S`, every `S`-block is the union of exactly the `Q`-class
blocks contained in it. -/
theorem unionClassBlocksInside_eq_blockFinset
    (Q S : Setoid X) (hQS : Refines Q S) (z : X) :
    unionClassBlocksInside Q S z = blockFinset S z := by
  classical
  unfold unionClassBlocksInside
  ext y
  constructor
  · intro hy
    rcases Finset.mem_biUnion.mp hy with ⟨t, ht, hyt⟩
    have hinside := (mem_classBlocksInside Q S z t).1 ht
    exact hinside.2 hyt
  · intro hy
    have hyz : S.r y z := (mem_blockFinset S z y).1 hy
    let t : Finset X := (Finpartition.ofSetoid Q).part y
    have htpart : t ∈ (Finpartition.ofSetoid Q).parts := by
      dsimp [t]
      exact (Finpartition.ofSetoid Q).part_mem.2 (Finset.mem_univ y)
    have htclass : t ∈ classBlocks Q := by
      simpa [classBlocks] using htpart
    have hyt : y ∈ t := by
      dsimp [t]
      exact (Finpartition.ofSetoid Q).mem_part (Finset.mem_univ y)
    have hsub : t ⊆ blockFinset S z := by
      intro w hw
      have hQyw : Q.r y w := by
        have hw' : w ∈ (Finpartition.ofSetoid Q).part y := by
          simpa [t] using hw
        exact (Finpartition.mem_part_ofSetoid_iff_rel).1 hw'
      have hSyw : S.r y w := hQS hQyw
      have hSwz : S.r w z := S.trans (S.symm hSyw) hyz
      exact (mem_blockFinset S z w).2 hSwz
    apply Finset.mem_biUnion.mpr
    exact ⟨t, (mem_classBlocksInside Q S z t).2 ⟨htclass, hsub⟩, hyt⟩

end UEOT.V3.FiniteStablePartition
