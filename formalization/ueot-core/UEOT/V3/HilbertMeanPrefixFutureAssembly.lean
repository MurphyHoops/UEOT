import UEOT.V3.HilbertMeanPrefixFiltration
import Mathlib.Tactic

/-!
# P-STAT-06 — canonical prefix/future assembly

At a genuine sample index `i : Fin N`, the revealed prefix and strict future
form a partition of all coordinates.  This module gives the canonical map that
assembles those two blocks back into a full sample vector and proves exact
reconstruction after projecting an existing sample onto the two blocks.
-/

namespace UEOT.V3.HilbertMeanPrefixFutureAssembly

open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanPrefixFiltration

universe uH

variable {H : Type uH}

/-- Assemble a revealed prefix and strict future into a full `Fin N` sample. -/
def assemblePrefixFuture {N : ℕ} (i : Fin N)
    (x : prefixBlock i.1 → H) (y : future i → H) : Fin N → H :=
  fun j =>
    if h : j.1 ≤ i.1 then
      x ⟨j, (mem_prefixBlock_iff i.1 j).2 h⟩
    else
      y ⟨j, (mem_future_iff i j).2 (Fin.lt_iff_val_lt_val.2 (Nat.lt_of_not_ge h))⟩

/-- On a revealed coordinate, assembly returns the prefix value. -/
@[simp] theorem assemblePrefixFuture_prefix
    {N : ℕ} (i : Fin N)
    (x : prefixBlock i.1 → H) (y : future i → H)
    (j : prefixBlock i.1) :
    assemblePrefixFuture i x y j.1 = x j := by
  unfold assemblePrefixFuture
  simp [(mem_prefixBlock_iff i.1 j.1).1 j.2]

/-- On a strict-future coordinate, assembly returns the future value. -/
@[simp] theorem assemblePrefixFuture_future
    {N : ℕ} (i : Fin N)
    (x : prefixBlock i.1 → H) (y : future i → H)
    (j : future i) :
    assemblePrefixFuture i x y j.1 = y j := by
  unfold assemblePrefixFuture
  have hlt : i < j.1 := (mem_future_iff i j.1).1 j.2
  have hnle : ¬ j.1.1 ≤ i.1 := by
    exact Nat.not_le_of_lt (Fin.lt_iff_val_lt_val.1 hlt)
  simp [hnle]

/-- Projecting a full sample to prefix/future blocks and reassembling recovers
the original sample definitionally at every coordinate. -/
theorem assemblePrefixFuture_blockProjections
    {N : ℕ} (i : Fin N) (ω : Fin N → H) :
    assemblePrefixFuture i
      (blockProjection (prefixBlock i.1) ω)
      (blockProjection (future i) ω) = ω := by
  funext j
  unfold assemblePrefixFuture blockProjection
  split
  · rfl
  · rfl

/-- The prefix projection of an assembled sample is exactly its prefix input. -/
theorem blockProjection_prefix_assemble
    {N : ℕ} (i : Fin N)
    (x : prefixBlock i.1 → H) (y : future i → H) :
    blockProjection (prefixBlock i.1) (assemblePrefixFuture i x y) = x := by
  funext j
  exact assemblePrefixFuture_prefix i x y j

/-- The future projection of an assembled sample is exactly its future input. -/
theorem blockProjection_future_assemble
    {N : ℕ} (i : Fin N)
    (x : prefixBlock i.1 → H) (y : future i → H) :
    blockProjection (future i) (assemblePrefixFuture i x y) = y := by
  funext j
  exact assemblePrefixFuture_future i x y j

/-- The canonical prefix/future assembly is measurable for the product
measurable structures. -/
theorem measurable_assemblePrefixFuture
    [MeasurableSpace H] {N : ℕ} (i : Fin N) :
    Measurable (fun xy : (prefixBlock i.1 → H) × (future i → H) =>
      assemblePrefixFuture i xy.1 xy.2) := by
  rw [measurable_pi_iff]
  intro j
  by_cases h : j.1 ≤ i.1
  · simp only [assemblePrefixFuture, dif_pos h]
    exact (measurable_pi_apply ⟨j, (mem_prefixBlock_iff i.1 j).2 h⟩).comp measurable_fst
  · simp only [assemblePrefixFuture, dif_neg h]
    exact (measurable_pi_apply
      ⟨j, (mem_future_iff i j).2
        (Fin.lt_iff_val_lt_val.2 (Nat.lt_of_not_ge h))⟩).comp measurable_snd

end UEOT.V3.HilbertMeanPrefixFutureAssembly
