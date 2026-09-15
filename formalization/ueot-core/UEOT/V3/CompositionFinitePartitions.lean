import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Partition.Finpartition

/-!
# P-COMP-01 — complete finite nontrivial partition domain

The frozen Core 3 statement takes its path-integration minimum over the finite
set of all nontrivial partitions of the declared child/path coordinates.
An arbitrary user-supplied finite family is not sufficient: it could omit a
factorizing cut and thereby certify a false positive margin.

For a finite child index type `I`, Mathlib's
`Finpartition (Finset.univ : Finset I)` is the exact finite set-partition
object we need.  A partition is nontrivial when it contains at least two
blocks.  This file constructs the complete finite domain, proves its nonempty
status as soon as there are at least two children, and provides the exact
finite minimum used by the source theorem.

`DecidableEq I` is a Lean representation requirement for the finite-set
lattice and exhaustive `Finpartition` enumeration.  It does not restrict the
finite mathematical partition domain represented here.
-/

namespace UEOT.V3.CompositionFinitePartitions

noncomputable section

open Finset
open scoped ENNReal

universe uI

variable {I : Type uI} [Fintype I] [DecidableEq I]

/-- An actual partition of the complete finite child index set. -/
abbrev ChildPartition (I : Type uI) [Fintype I] [DecidableEq I] :=
  Finpartition (Finset.univ : Finset I)

/-- The frozen source excludes the one-block partition. -/
def IsNontrivialPartition (π : ChildPartition I) : Prop :=
  2 ≤ π.parts.card

/-- The complete finite family `Π_nontriv` of all nontrivial partitions. -/
noncomputable def allNontrivialPartitions
    (I : Type uI) [Fintype I] [DecidableEq I] :
    Finset (ChildPartition I) := by
  classical
  exact Finset.univ.filter IsNontrivialPartition

@[simp]
theorem mem_allNontrivialPartitions (π : ChildPartition I) :
    π ∈ allNontrivialPartitions I ↔ IsNontrivialPartition π := by
  classical
  simp [allNontrivialPartitions]

/-- A block of an actual child partition, represented by an element of its
finite set of blocks. -/
abbrev PartitionBlock (π : ChildPartition I) := ↥π.parts

/-- The actual block containing one child index. -/
def partitionBlockOf (π : ChildPartition I) (i : I) : PartitionBlock π :=
  ⟨π.part i, π.part_mem.2 (Finset.mem_univ i)⟩

/-- Every declared partition block is hit by at least one child.  Hence
`partitionBlockOf` contains no artificial/empty block labels. -/
theorem partitionBlockOf_surjective (π : ChildPartition I) :
    Function.Surjective (partitionBlockOf π) := by
  intro b
  rcases b with ⟨b, hb⟩
  obtain ⟨i, hi⟩ := π.nonempty_of_mem_parts hb
  refine ⟨i, ?_⟩
  apply Subtype.ext
  exact π.part_eq_of_mem hb hi

/-- The block-label type has exactly as many elements as the partition has
parts. -/
theorem card_partitionBlock (π : ChildPartition I) :
    Fintype.card (PartitionBlock π) = π.parts.card := by
  simp [PartitionBlock]

/-- Source nontriviality is exactly the statement that the real block type has
at least two elements. -/
theorem two_le_card_partitionBlock
    {π : ChildPartition I} (hπ : IsNontrivialPartition π) :
    2 ≤ Fintype.card (PartitionBlock π) := by
  rw [card_partitionBlock]
  exact hπ

/-- If there are at least two children, the complete nontrivial partition
family is nonempty.  The discrete partition `⊥` is a witness. -/
theorem allNontrivialPartitions_nonempty
    (hI : 2 ≤ Fintype.card I) :
    (allNontrivialPartitions I).Nonempty := by
  classical
  refine ⟨(⊥ : ChildPartition I), ?_⟩
  rw [mem_allNontrivialPartitions]
  unfold IsNontrivialPartition
  simpa [Finpartition.card_bot] using hI

/-- Exact frozen-source minimum over **all** nontrivial partitions. -/
noncomputable def exactPathIntegrationMargin
    (hI : 2 ≤ Fintype.card I)
    (Iπ : ChildPartition I → ENNReal) : ENNReal :=
  (allNontrivialPartitions I).inf'
    (allNontrivialPartitions_nonempty hI) Iπ

/-- The exact finite minimum is positive iff every nontrivial partition score
is positive. -/
theorem exactPathIntegrationMargin_pos_iff_all_pos
    (hI : 2 ≤ Fintype.card I)
    (Iπ : ChildPartition I → ENNReal) :
    0 < exactPathIntegrationMargin hI Iπ ↔
      ∀ π : ChildPartition I, IsNontrivialPartition π → 0 < Iπ π := by
  unfold exactPathIntegrationMargin
  rw [Finset.lt_inf'_iff]
  simp [mem_allNontrivialPartitions]

/-- Once the true zero set of each partition score is known, the exact source
margin is positive precisely when no nontrivial partition factorizes. -/
theorem exactPathIntegrationMargin_pos_iff_no_factorization
    (hI : 2 ≤ Fintype.card I)
    (Iπ : ChildPartition I → ENNReal)
    (factorizes : ChildPartition I → Prop)
    (hzero : ∀ π : ChildPartition I,
      IsNontrivialPartition π → (Iπ π = 0 ↔ factorizes π)) :
    0 < exactPathIntegrationMargin hI Iπ ↔
      ∀ π : ChildPartition I, IsNontrivialPartition π → ¬ factorizes π := by
  rw [exactPathIntegrationMargin_pos_iff_all_pos]
  constructor
  · intro h π hπ hfac
    exact (ne_of_gt (h π hπ)) ((hzero π hπ).2 hfac)
  · intro h π hπ
    rw [pos_iff_ne_zero]
    intro hIπ
    exact h π hπ ((hzero π hπ).1 hIπ)

end

end UEOT.V3.CompositionFinitePartitions
