import Mathlib

/-!
# Scientific Closure C3 — one structured carrier-search special case

A nested candidate family is a genuine restricted alternative to powerset
enumeration.  The theorem searches only the registered `n+1` candidates and
returns the least good index.  It deliberately makes no claim of global
minimality outside the nested family.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure

universe uV

/-- A chain of registered candidate carriers. -/
structure NestedCandidateFamily (V : Type uV) (n : ℕ) where
  candidate : Fin (n + 1) → Finset V
  nested : ∀ {i j : Fin (n + 1)}, i ≤ j → candidate i ⊆ candidate j

namespace NestedCandidateFamily

variable {V : Type uV} {n : ℕ}

noncomputable section

/-- Indices satisfying the declared oracle predicate. -/
noncomputable def goodIndices
    (F : NestedCandidateFamily V n)
    (Good : Finset V → Prop) [DecidablePred Good] : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => Good (F.candidate i))

/-- If one registered candidate is good, the good-index set is nonempty. -/
theorem goodIndices_nonempty
    (F : NestedCandidateFamily V n)
    (Good : Finset V → Prop) [DecidablePred Good]
    {i : Fin (n + 1)} (hi : Good (F.candidate i)) :
    (F.goodIndices Good).Nonempty := by
  exact ⟨i, by simp [goodIndices, hi]⟩

/-- Least good index inside the registered chain. -/
noncomputable def firstGoodIndex
    (F : NestedCandidateFamily V n)
    (Good : Finset V → Prop) [DecidablePred Good]
    (hne : (F.goodIndices Good).Nonempty) : Fin (n + 1) :=
  (F.goodIndices Good).min' hne

/-- The returned candidate satisfies the oracle. -/
theorem firstGoodIndex_good
    (F : NestedCandidateFamily V n)
    (Good : Finset V → Prop) [DecidablePred Good]
    (hne : (F.goodIndices Good).Nonempty) :
    Good (F.candidate (F.firstGoodIndex Good hne)) := by
  have hm := Finset.min'_mem (F.goodIndices Good) hne
  simpa [firstGoodIndex, goodIndices] using hm

/-- No strictly earlier registered candidate is good. -/
theorem firstGoodIndex_no_earlier_good
    (F : NestedCandidateFamily V n)
    (Good : Finset V → Prop) [DecidablePred Good]
    (hne : (F.goodIndices Good).Nonempty) :
    ∀ j : Fin (n + 1), j < F.firstGoodIndex Good hne →
      ¬ Good (F.candidate j) := by
  intro j hj hgood
  have hjmem : j ∈ F.goodIndices Good := by
    simp [goodIndices, hgood]
  have hmin : F.firstGoodIndex Good hne ≤ j :=
    Finset.min'_le _ _ hjmem
  exact (not_le_of_gt hj) hmin

/-- If the oracle is upward under carrier inclusion, the least good index is
inclusion-minimal among this nested candidate family. -/
theorem firstGoodIndex_chainMinimal
    (F : NestedCandidateFamily V n)
    (Good : Finset V → Prop) [DecidablePred Good]
    (hne : (F.goodIndices Good).Nonempty) :
    Good (F.candidate (F.firstGoodIndex Good hne)) ∧
      ∀ j : Fin (n + 1), j < F.firstGoodIndex Good hne →
        ¬ Good (F.candidate j) :=
  ⟨F.firstGoodIndex_good Good hne,
    F.firstGoodIndex_no_earlier_good Good hne⟩

end

end NestedCandidateFamily

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure
