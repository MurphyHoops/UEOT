import UEOT.V3.ViabilityKernel

namespace UEOT.V3.Compression.Objecthood

open Set
open UEOT.V3.ViabilityKernel

universe uX uA
variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A]

def repairStep (P : X → A → PMF X) (R : Set X) : Set X :=
  R ∪ {x | ∃ a : A, StaysIn (P x a) R}

theorem subset_repairStep (P : X → A → PMF X) (R : Set X) :
    R ⊆ repairStep P R := by
  intro x hx
  exact Or.inl hx

theorem repairStep_mono (P : X → A → PMF X) {R S : Set X}
    (hRS : R ⊆ S) :
    repairStep P R ⊆ repairStep P S := by
  intro x hx
  rcases hx with hx | ⟨a, ha⟩
  · exact Or.inl (hRS hx)
  · exact Or.inr ⟨a, ha.trans hRS⟩

def repairIter (P : X → A → PMF X) (K : Set X) : ℕ → Set X
  | 0 => K
  | n + 1 => repairStep P (repairIter P K n)

@[simp] theorem repairIter_zero (P : X → A → PMF X) (K : Set X) :
    repairIter P K 0 = K := rfl

@[simp] theorem repairIter_succ (P : X → A → PMF X) (K : Set X) (n : ℕ) :
    repairIter P K (n + 1) = repairStep P (repairIter P K n) := rfl

theorem repairIter_subset_succ (P : X → A → PMF X) (K : Set X) :
    ∀ n, repairIter P K n ⊆ repairIter P K (n + 1) := by
  intro n
  exact subset_repairStep P (repairIter P K n)

theorem repairIter_monotone (P : X → A → PMF X) (K : Set X) :
    Monotone (repairIter P K) :=
  monotone_nat_of_le_succ (repairIter_subset_succ P K)

theorem exists_repairIter_fixed (P : X → A → PMF X) (K : Set X) :
    ∃ n : ℕ, repairIter P K (n + 1) = repairIter P K n := by
  classical
  obtain ⟨i, j, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (α := ℕ) (repairIter P K)
  have hmono := repairIter_monotone P K
  rcases lt_or_gt_of_ne hne with hij | hji
  · refine ⟨i, Set.Subset.antisymm ?_ (repairIter_subset_succ P K i)⟩
    have hs : i + 1 ≤ j := Nat.succ_le_iff.mpr hij
    have hsub := hmono hs
    rw [← heq] at hsub
    exact hsub
  · refine ⟨j, Set.Subset.antisymm ?_ (repairIter_subset_succ P K j)⟩
    have hs : j + 1 ≤ i := Nat.succ_le_iff.mpr hji
    have hsub := hmono hs
    rw [heq] at hsub
    exact hsub

def StrongRepairable (P : X → A → PMF X) (K : Set X) (x : X) : Prop :=
  ∃ n : ℕ, x ∈ repairIter P K n

theorem mem_strongRepairable_of_mem_iter
    (P : X → A → PMF X) (K : Set X) {x : X} {n : ℕ}
    (hx : x ∈ repairIter P K n) :
    StrongRepairable P K x :=
  ⟨n, hx⟩

theorem repairIter_add_eq_of_fixed
    (P : X → A → PMF X) (K : Set X) {n : ℕ}
    (hfix : repairIter P K (n + 1) = repairIter P K n) :
    ∀ k : ℕ, repairIter P K (n + k) = repairIter P K n := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        repairIter P K (n + (k + 1))
            = repairStep P (repairIter P K (n + k)) := by
                have hadd : n + (k + 1) = (n + k) + 1 := by omega
                rw [hadd, repairIter_succ]
        _ = repairStep P (repairIter P K n) := by rw [ih]
        _ = repairIter P K (n + 1) := rfl
        _ = repairIter P K n := hfix

theorem repairIter_subset_of_fixed
    (P : X → A → PMF X) (K : Set X) {n : ℕ}
    (hfix : repairIter P K (n + 1) = repairIter P K n)
    (m : ℕ) :
    repairIter P K m ⊆ repairIter P K n := by
  by_cases hmn : m ≤ n
  · exact repairIter_monotone P K hmn
  · have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [repairIter_add_eq_of_fixed P K hfix k]

theorem strongRepairable_iff_mem_fixed
    (P : X → A → PMF X) (K : Set X) {n : ℕ}
    (hfix : repairIter P K (n + 1) = repairIter P K n)
    (x : X) :
    StrongRepairable P K x ↔ x ∈ repairIter P K n := by
  constructor
  · rintro ⟨m, hm⟩
    exact repairIter_subset_of_fixed P K hfix m hm
  · intro hx
    exact ⟨n, hx⟩

theorem exists_strongRepairBasin_fixed
    (P : X → A → PMF X) (K : Set X) :
    ∃ n : ℕ,
      repairStep P (repairIter P K n) = repairIter P K n ∧
      ∀ x : X, StrongRepairable P K x ↔ x ∈ repairIter P K n := by
  obtain ⟨n, hfix⟩ := exists_repairIter_fixed P K
  refine ⟨n, ?_, ?_⟩
  · simpa using hfix
  · exact strongRepairable_iff_mem_fixed P K hfix

end UEOT.V3.Compression.Objecthood
