import UEOT.V3.HilbertMeanPrefixFiltration
import Mathlib.Tactic

/-!
# P-STAT-06 — past/active assembly of a revealed prefix

For a fixed active index `i`, the revealed prefix is exactly the disjoint union
of the strict past and the active coordinate.  This module packages the
canonical assembly map from `(past i → H) × H` to the revealed prefix used in
the final conditional-increment identification.
-/

namespace UEOT.V3.HilbertMeanPastActiveAssembly

open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanProductBlockIndependence

universe uH

variable {H : Type uH} [MeasurableSpace H]

/-- Assemble a revealed prefix from its strict-past block and active value. -/
def assemblePastActive {N : ℕ} (i : Fin N)
    (p : past i → H) (a : H) : prefixBlock (N := N) i.1 → H :=
  fun j => if hji : (j : Fin N) = i then a else
    p ⟨(j : Fin N), by
      apply (mem_past_iff i (j : Fin N)).2
      have hjle : (j : Fin N) ≤ i := by
        apply (mem_revealed_iff i (j : Fin N)).1
        rw [← prefixBlock_val_eq_revealed i]
        exact j.2
      exact lt_of_le_of_ne hjle hji⟩

/-- On a genuine sample, assembling its strict-past projection and active
coordinate reproduces its revealed-prefix projection exactly. -/
@[simp] theorem assemblePastActive_blockProjection
    {N : ℕ} (i : Fin N) (ω : Fin N → H) :
    assemblePastActive i (blockProjection (past i) ω) (ω i) =
      blockProjection (prefixBlock (N := N) i.1) ω := by
  funext j
  unfold assemblePastActive blockProjection
  by_cases hji : (j : Fin N) = i
  · simp [hji]
  · simp [hji]

/-- Replacing the active value while keeping the same strict past is exactly the
revealed prefix of the coordinate-updated full sample. -/
@[simp] theorem assemblePastActive_blockProjection_update
    {N : ℕ} (i : Fin N) (ω : Fin N → H) (a : H) :
    assemblePastActive i (blockProjection (past i) ω) a =
      blockProjection (prefixBlock (N := N) i.1) (Function.update ω i a) := by
  funext j
  unfold assemblePastActive blockProjection
  by_cases hji : (j : Fin N) = i
  · simp [hji]
  · simp [Function.update, hji]

/-- Past/active assembly is measurable as a map into the finite product prefix. -/
theorem measurable_assemblePastActive {N : ℕ} (i : Fin N) :
    Measurable (fun z : (past i → H) × H => assemblePastActive i z.1 z.2) := by
  rw [measurable_pi_iff]
  intro j
  by_cases hji : (j : Fin N) = i
  · simpa [assemblePastActive, hji] using
      (measurable_snd : Measurable (fun z : (past i → H) × H => z.2))
  · have hjpast : (j : Fin N) ∈ past i := by
      apply (mem_past_iff i (j : Fin N)).2
      have hjle : (j : Fin N) ≤ i := by
        apply (mem_revealed_iff i (j : Fin N)).1
        rw [← prefixBlock_val_eq_revealed i]
        exact j.2
      exact lt_of_le_of_ne hjle hji
    let jp : past i := ⟨(j : Fin N), hjpast⟩
    have hm : Measurable (fun z : (past i → H) × H => z.1 jp) :=
      (measurable_pi_apply jp).comp measurable_fst
    simpa [assemblePastActive, hji, jp] using hm

end UEOT.V3.HilbertMeanPastActiveAssembly
