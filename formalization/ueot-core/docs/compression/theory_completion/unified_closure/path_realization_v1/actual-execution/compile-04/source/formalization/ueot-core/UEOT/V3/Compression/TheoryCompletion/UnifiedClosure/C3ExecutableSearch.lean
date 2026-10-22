import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C3NestedSearch

/-!
# Executable search in a registered nested carrier family

The oracle is an actual Boolean input.  `scan` records precisely the queried
indices and stops at its first positive response.  Its correctness requires no
monotonicity of the oracle; the registered family is nested only for the final
carrier-inclusion conclusion.  Model matching is an explicit theorem premise.

This implements a linear-query restricted search.  It does not enumerate all
minimal carriers, synthesize a physical intervention oracle, or certify noisy
responses.  Query count is distinct from the internal cost of one oracle call.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.C3ExecutableSearch

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure

universe uV

/-- The actual output and the indices at which the oracle was consulted. -/
structure SearchRun where
  found : Option ℕ
  queries : List ℕ
  deriving DecidableEq, Repr

/-- Query consecutive indices, stopping at the first positive response. -/
def scan (oracle : ℕ → Bool) : ℕ → ℕ → SearchRun
  | _, 0 => ⟨none, []⟩
  | start, fuel + 1 =>
      if oracle start = true then ⟨some start, [start]⟩
      else
        let rest := scan oracle (start + 1) fuel
        ⟨rest.found, start :: rest.queries⟩

/-- A successful scan returns exactly the first positive index in its interval. -/
theorem scan_found_iff (oracle : ℕ → Bool) (start fuel i : ℕ) :
    (scan oracle start fuel).found = some i ↔
      start ≤ i ∧ i < start + fuel ∧ oracle i = true ∧
        ∀ j, start ≤ j → j < i → oracle j = false := by
  induction fuel generalizing start with
  | zero =>
      constructor
      · intro h
        cases h
      · intro h
        omega
  | succ fuel ih =>
      cases ho : oracle start with
      | false =>
          simp only [scan, ho, if_neg Bool.false_ne_true]
          rw [ih]
          constructor
          · rintro ⟨hlo, hhi, hyes, hbefore⟩
            refine ⟨by omega, by omega, hyes, ?_⟩
            intro j hjlo hjhi
            by_cases hj : j = start
            · simpa [hj] using ho
            · exact hbefore j (by omega) hjhi
          · rintro ⟨hlo, hhi, hyes, hbefore⟩
            have hne : i ≠ start := by
              intro heq
              subst i
              simp [ho] at hyes
            refine ⟨by omega, by omega, hyes, ?_⟩
            intro j hjlo hjhi
            exact hbefore j (by omega) hjhi
      | true =>
          simp only [scan, ho]
          constructor
          · intro hi
            have heq : start = i := Option.some.inj hi
            subst i
            refine ⟨le_rfl, by omega, ho, ?_⟩
            intro j hjlo hjhi
            omega
          · rintro ⟨hlo, hhi, hyes, hbefore⟩
            have heq : start = i := by
              by_contra hne
              have hfalse := hbefore start (le_refl start) (by omega)
              simp [ho] at hfalse
            simp [heq]

/-- Failure means every index in the requested finite interval was negative. -/
theorem scan_none_iff (oracle : ℕ → Bool) (start fuel : ℕ) :
    (scan oracle start fuel).found = none ↔
      ∀ i, start ≤ i → i < start + fuel → oracle i = false := by
  induction fuel generalizing start with
  | zero =>
      constructor
      · intro _ i hlo hhi
        omega
      · intro _
        rfl
  | succ fuel ih =>
      cases ho : oracle start with
      | false =>
          simp only [scan, ho, if_neg Bool.false_ne_true]
          rw [ih]
          constructor
          · intro h i hlo hhi
            by_cases hi : i = start
            · simpa [hi] using ho
            · exact h i (by omega) (by omega)
          · intro h i hlo hhi
            exact h i (by omega) (by omega)
      | true =>
          simp only [scan, ho]
          constructor
          · intro h
            cases h
          · intro h
            have hfalse := h start (le_refl start) (by omega)
            simp [ho] at hfalse

/-- The trace length counts the actual short-circuit oracle calls. -/
theorem scan_query_count (oracle : ℕ → Bool) (start fuel : ℕ) :
    (scan oracle start fuel).queries.length =
      match (scan oracle start fuel).found with
      | none => fuel
      | some i => i - start + 1 := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      cases ho : oracle start with
      | false =>
          simp only [scan, ho, if_neg Bool.false_ne_true, List.length_cons]
          rw [ih]
          cases hr : (scan oracle (start + 1) fuel).found with
          | none => simp
          | some i =>
              have hlo := (scan_found_iff oracle (start + 1) fuel i).mp hr
              simp only
              omega
      | true => simp [scan, ho]

/-- Every query is within the original requested interval. -/
theorem scan_query_mem (oracle : ℕ → Bool) (start fuel i : ℕ)
    (hi : i ∈ (scan oracle start fuel).queries) :
    start ≤ i ∧ i < start + fuel := by
  induction fuel generalizing start with
  | zero => simp [scan] at hi
  | succ fuel ih =>
      cases ho : oracle start with
      | false =>
          simp only [scan, ho, if_neg Bool.false_ne_true, List.mem_cons] at hi
          rcases hi with hi | hi
          · subst i
            omega
          · have htail := ih (start + 1) hi
            omega
      | true =>
          have heq : i = start := by simpa [scan, ho] using hi
          subst i
          omega

/-- No registered query is repeated within one run. -/
theorem scan_queries_nodup (oracle : ℕ → Bool) (start fuel : ℕ) :
    (scan oracle start fuel).queries.Nodup := by
  induction fuel generalizing start with
  | zero => simp [scan]
  | succ fuel ih =>
      cases ho : oracle start with
      | false =>
          simp only [scan, ho, if_neg Bool.false_ne_true]
          refine List.nodup_cons.mpr ⟨?_, ih (start + 1)⟩
          intro hm
          have hbound := scan_query_mem oracle (start + 1) fuel start hm
          omega
      | true => simp [scan, ho]

/-- The number of oracle calls never exceeds the requested interval length. -/
theorem scan_query_bound (oracle : ℕ → Bool) (start fuel : ℕ) :
    (scan oracle start fuel).queries.length ≤ fuel := by
  rw [scan_query_count]
  cases hr : (scan oracle start fuel).found with
  | none => exact le_rfl
  | some i =>
      have hb := (scan_found_iff oracle start fuel i).mp hr
      change i - start + 1 ≤ fuel
      have hlo : start ≤ i := hb.1
      have hhi : i < start + fuel := hb.2.1
      have hsplit : i - start + start = i := Nat.sub_add_cancel hlo
      omega

variable {V : Type uV} {n : ℕ}

/-- The finite registered table supplies the oracle arguments.  The extension
outside the table is never consulted by `search`. -/
def familyOracle (F : NestedCandidateFamily V n) (oracle : Finset V → Bool)
    (i : ℕ) : Bool :=
  if hi : i < n + 1 then oracle (F.candidate ⟨i, hi⟩) else false

/-- Executable search over precisely the registered `n + 1` candidates. -/
def search (F : NestedCandidateFamily V n) (oracle : Finset V → Bool) : SearchRun :=
  scan (familyOracle F oracle) 0 (n + 1)

private theorem bool_false_iff_not {b : Bool} {P : Prop}
    (h : b = true ↔ P) : b = false ↔ ¬ P := by
  cases b <;> simp_all

/-- A correct Boolean oracle makes the actual output the first good candidate.
No monotonicity assumption is needed for this linear scan. -/
theorem search_found_iff
    (F : NestedCandidateFamily V n) (oracle : Finset V → Bool)
    (Good : Finset V → Prop)
    (hmatch : ∀ i, oracle (F.candidate i) = true ↔ Good (F.candidate i))
    (i : Fin (n + 1)) :
    (search F oracle).found = some i.val ↔
      Good (F.candidate i) ∧
        ∀ j : Fin (n + 1), j < i → ¬ Good (F.candidate j) := by
  rw [search, scan_found_iff]
  constructor
  · rintro ⟨hlo, hhi, hyes, hbefore⟩
    refine ⟨(hmatch i).mp ?_, ?_⟩
    · simpa [familyOracle, i.isLt] using hyes
    · intro j hji
      have hfalse := hbefore j.val (Nat.zero_le _) hji
      apply (bool_false_iff_not (hmatch j)).mp
      simpa [familyOracle, j.isLt] using hfalse
  · rintro ⟨hgood, hbefore⟩
    refine ⟨Nat.zero_le _, by simpa using i.isLt, ?_, ?_⟩
    · simpa [familyOracle, i.isLt] using (hmatch i).mpr hgood
    · intro j _ hji
      have hjn : j < n + 1 := by omega
      let jf : Fin (n + 1) := ⟨j, hjn⟩
      have hn : ¬ Good (F.candidate jf) := hbefore jf hji
      have hf := (bool_false_iff_not (hmatch jf)).mpr hn
      simpa [familyOracle, hjn, jf] using hf

/-- `none` certifies failure for every registered candidate under the same oracle
matching premise.  It says nothing about unregistered carriers. -/
theorem search_none_iff
    (F : NestedCandidateFamily V n) (oracle : Finset V → Bool)
    (Good : Finset V → Prop)
    (hmatch : ∀ i, oracle (F.candidate i) = true ↔ Good (F.candidate i)) :
    (search F oracle).found = none ↔
      ∀ i, ¬ Good (F.candidate i) := by
  rw [search, scan_none_iff]
  constructor
  · intro h i
    apply (bool_false_iff_not (hmatch i)).mp
    simpa [familyOracle, i.isLt] using h i.val (Nat.zero_le _) (by simpa using i.isLt)
  · intro h i _ hib
    have hin : i < n + 1 := by omega
    let fi : Fin (n + 1) := ⟨i, hin⟩
    have hf := (bool_false_iff_not (hmatch fi)).mpr (h fi)
    simpa [familyOracle, hin, fi] using hf

/-- Bind the executable result to the existing, independently defined least
good-index theorem.  The existing noncomputable selector is not program input. -/
theorem search_eq_firstGoodIndex
    (F : NestedCandidateFamily V n) (oracle : Finset V → Bool)
    (Good : Finset V → Prop) [DecidablePred Good]
    (hmatch : ∀ i, oracle (F.candidate i) = true ↔ Good (F.candidate i))
    (hne : (F.goodIndices Good).Nonempty) :
    (search F oracle).found = some (F.firstGoodIndex Good hne).val := by
  apply (search_found_iff F oracle Good hmatch _).mpr
  exact F.firstGoodIndex_chainMinimal Good hne

/-- A returned carrier has no strictly smaller good carrier in the registered
nested family.  This conclusion does not range over the entire powerset. -/
theorem search_registered_inclusion_minimal
    (F : NestedCandidateFamily V n) (oracle : Finset V → Bool)
    (Good : Finset V → Prop)
    (hmatch : ∀ i, oracle (F.candidate i) = true ↔ Good (F.candidate i))
    (i : Fin (n + 1)) (hfound : (search F oracle).found = some i.val) :
    Good (F.candidate i) ∧
      ∀ j, F.candidate j ⊂ F.candidate i → ¬ Good (F.candidate j) := by
  have hs := (search_found_iff F oracle Good hmatch i).mp hfound
  refine ⟨hs.1, ?_⟩
  intro j hproper
  apply hs.2 j
  by_contra hnot
  have hij : i ≤ j := le_of_not_gt hnot
  exact (not_lt_of_ge (F.nested hij)) hproper

/-- Success at index `i` makes exactly `i + 1` oracle calls. -/
theorem search_queries_of_found
    (F : NestedCandidateFamily V n) (oracle : Finset V → Bool)
    {i : ℕ} (hfound : (search F oracle).found = some i) :
    (search F oracle).queries.length = i + 1 := by
  change (scan (familyOracle F oracle) 0 (n + 1)).found = some i at hfound
  change (scan (familyOracle F oracle) 0 (n + 1)).queries.length = i + 1
  rw [scan_query_count, hfound]
  simp

/-- An unsuccessful search consults every registered candidate exactly once. -/
theorem search_queries_of_none
    (F : NestedCandidateFamily V n) (oracle : Finset V → Bool)
    (hnone : (search F oracle).found = none) :
    (search F oracle).queries.length = n + 1 ∧
      (search F oracle).queries.Nodup := by
  refine ⟨?_, scan_queries_nodup _ _ _⟩
  change (scan (familyOracle F oracle) 0 (n + 1)).found = none at hnone
  change (scan (familyOracle F oracle) 0 (n + 1)).queries.length = n + 1
  rw [scan_query_count, hnone]

/-- The exact-oracle query budget is linear in the registered candidate count. -/
theorem search_query_budget
    (F : NestedCandidateFamily V n) (oracle : Finset V → Bool) :
    (search F oracle).queries.length ≤ n + 1 ∧
      ∀ i ∈ (search F oracle).queries, i < n + 1 := by
  refine ⟨scan_query_bound _ _ _, ?_⟩
  intro i hi
  have hb := scan_query_mem (familyOracle F oracle) 0 (n + 1) i hi
  simpa using hb.2

private def prefixFamily : NestedCandidateFamily ℕ 4 where
  candidate i := Finset.range i.val
  nested := by
    intro i j hij
    exact Finset.range_mono hij

private def thresholdOracle (S : Finset ℕ) : Bool := decide (2 ≤ S.card)

private def impossibleOracle (S : Finset ℕ) : Bool := decide (5 ≤ S.card)

private def nonmonotoneOracle (S : Finset ℕ) : Bool :=
  decide (S.card = 1 ∨ S.card = 3)

/-- A nonempty prefix family stops at its first carrier of size two. -/
theorem prefix_threshold_search :
    search prefixFamily thresholdOracle = ⟨some 2, [0, 1, 2]⟩ := by
  decide

/-- A negative oracle exhausts exactly the five registered candidates. -/
theorem prefix_impossible_search :
    search prefixFamily impossibleOracle = ⟨none, [0, 1, 2, 3, 4]⟩ := by
  decide

/-- A nonmonotone predicate still has a correctly detected first good index. -/
theorem prefix_nonmonotone_search :
    search prefixFamily nonmonotoneOracle = ⟨some 1, [0, 1]⟩ ∧
      nonmonotoneOracle (prefixFamily.candidate 1) = true ∧
      nonmonotoneOracle (prefixFamily.candidate 2) = false := by
  decide

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.C3ExecutableSearch
