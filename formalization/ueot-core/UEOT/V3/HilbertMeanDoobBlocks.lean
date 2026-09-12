import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# P-STAT-06 — canonical past / active / future blocks

For an active coordinate `i : Fin N`, the Doob decomposition splits the sample
indices into coordinates strictly before `i`, the singleton active coordinate,
and coordinates strictly after `i`. This file records the finite-set algebra
needed by the source-facing continuation construction.
-/

namespace UEOT.V3.HilbertMeanDoobBlocks

open Finset

/-- Coordinates strictly before the active index. -/
def past {N : ℕ} (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun j => j < i

/-- The singleton active coordinate. -/
def active {N : ℕ} (i : Fin N) : Finset (Fin N) :=
  {i}

/-- Coordinates strictly after the active index. -/
def future {N : ℕ} (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun j => i < j

@[simp] theorem mem_past_iff {N : ℕ} (i j : Fin N) :
    j ∈ past i ↔ j < i := by
  simp [past]

@[simp] theorem mem_active_iff {N : ℕ} (i j : Fin N) :
    j ∈ active i ↔ j = i := by
  simp [active]

@[simp] theorem mem_future_iff {N : ℕ} (i j : Fin N) :
    j ∈ future i ↔ i < j := by
  simp [future]

/-- Past and active blocks are disjoint. -/
theorem past_disjoint_active {N : ℕ} (i : Fin N) :
    Disjoint (past i) (active i) := by
  rw [Finset.disjoint_left]
  intro j hjp hja
  have hji : j < i := (mem_past_iff i j).1 hjp
  have hEq : j = i := (mem_active_iff i j).1 hja
  have : i < i := by simpa [hEq] using hji
  exact (lt_irrefl i) this

/-- Active and future blocks are disjoint. -/
theorem active_disjoint_future {N : ℕ} (i : Fin N) :
    Disjoint (active i) (future i) := by
  rw [Finset.disjoint_left]
  intro j hja hjf
  have hEq : j = i := (mem_active_iff i j).1 hja
  have hij : i < j := (mem_future_iff i j).1 hjf
  have : i < i := by simpa [hEq] using hij
  exact (lt_irrefl i) this

/-- Past and future blocks are disjoint. -/
theorem past_disjoint_future {N : ℕ} (i : Fin N) :
    Disjoint (past i) (future i) := by
  rw [Finset.disjoint_left]
  intro j hjp hjf
  have hji : j < i := (mem_past_iff i j).1 hjp
  have hij : i < j := (mem_future_iff i j).1 hjf
  exact lt_asymm hji hij

/-- Every coordinate lies either strictly before, at, or strictly after the
active index. -/
theorem past_union_active_union_future {N : ℕ} (i : Fin N) :
    past i ∪ active i ∪ future i = Finset.univ := by
  ext j
  simp only [Finset.mem_union, mem_past_iff, mem_active_iff, mem_future_iff,
    Finset.mem_univ, iff_true]
  rcases lt_trichotomy j i with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · exact Or.inl (Or.inr heq)
  · exact Or.inr hgt

/-- The revealed-through-active block is exactly past plus active. -/
def revealed {N : ℕ} (i : Fin N) : Finset (Fin N) :=
  past i ∪ active i

@[simp] theorem mem_revealed_iff {N : ℕ} (i j : Fin N) :
    j ∈ revealed i ↔ j ≤ i := by
  simp only [revealed, Finset.mem_union, mem_past_iff, mem_active_iff]
  constructor
  · intro h
    rcases h with hlt | heq
    · exact hlt.le
    · simpa [heq]
  · intro h
    exact lt_or_eq_of_le h

/-- The strict future is disjoint from everything revealed through the active
coordinate. -/
theorem revealed_disjoint_future {N : ℕ} (i : Fin N) :
    Disjoint (revealed i) (future i) := by
  rw [Finset.disjoint_left]
  intro j hjr hjf
  have hle : j ≤ i := (mem_revealed_iff i j).1 hjr
  have hlt : i < j := (mem_future_iff i j).1 hjf
  exact (not_lt_of_ge hle) hlt

end UEOT.V3.HilbertMeanDoobBlocks
