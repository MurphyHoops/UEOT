import UEOT.V3.Compression.Objecthood.StrongRepairAttractor

namespace UEOT.V3.Compression.Objecthood

open Set
open UEOT.V3.ViabilityKernel

universe uX uA

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A]

noncomputable def repairRank
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) : ℕ := by
  classical
  exact Nat.find hx

theorem repairRank_mem
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) :
    x ∈ repairIter P K (repairRank P K x hx) := by
  classical
  exact Nat.find_spec hx

theorem repairRank_le_of_mem
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) {n : ℕ}
    (hn : x ∈ repairIter P K n) :
    repairRank P K x hx ≤ n := by
  classical
  exact Nat.find_min' hx hn

theorem repairRank_eq_zero_iff_mem
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) :
    repairRank P K x hx = 0 ↔ x ∈ K := by
  classical
  constructor
  · intro hr
    have hm := repairRank_mem P K x hx
    rw [hr] at hm
    simpa using hm
  · intro hxK
    apply Nat.eq_zero_of_le_zero
    exact repairRank_le_of_mem P K x hx (n := 0) (by simpa using hxK)

theorem exists_descending_action
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) (hxK : x ∉ K) :
    ∃ n : ℕ,
      repairRank P K x hx = n + 1 ∧
      ∃ a : A, StaysIn (P x a) (repairIter P K n) := by
  classical
  have hr0 : repairRank P K x hx ≠ 0 := by
    intro h
    exact hxK ((repairRank_eq_zero_iff_mem P K x hx).1 h)
  obtain ⟨n, hr⟩ := Nat.exists_eq_succ_of_ne_zero hr0
  refine ⟨n, hr, ?_⟩
  have hm := repairRank_mem P K x hx
  rw [hr, repairIter_succ] at hm
  rcases hm with hprev | hact
  · exfalso
    have hlt : n < repairRank P K x hx := by omega
    have hlt' : n < Nat.find hx := by
      simpa [repairRank] using hlt
    exact (Nat.find_min hx hlt') hprev
  · exact hact

theorem exists_descending_action_first
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) (hxK : x ∉ K) :
    ∃ a : A, ∃ n : ℕ,
      repairRank P K x hx = n + 1 ∧
      StaysIn (P x a) (repairIter P K n) := by
  obtain ⟨n, hr, a, ha⟩ := exists_descending_action P K x hx hxK
  exact ⟨a, n, hr, ha⟩

variable [Nonempty A]

noncomputable def descendingRepairAction
    (P : X → A → PMF X) (K : Set X) (x : X) : A := by
  classical
  if h : StrongRepairable P K x ∧ x ∉ K then
    exact Classical.choose (exists_descending_action_first P K x h.1 h.2)
  else
    exact Classical.choice inferInstance

theorem descendingRepairAction_staysIn_previous
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) (hxK : x ∉ K) :
    ∃ n : ℕ,
      repairRank P K x hx = n + 1 ∧
      StaysIn (P x (descendingRepairAction P K x)) (repairIter P K n) := by
  classical
  let h : StrongRepairable P K x ∧ x ∉ K := ⟨hx, hxK⟩
  have hs := Classical.choose_spec (exists_descending_action_first P K x hx hxK)
  simpa [descendingRepairAction, h] using hs

theorem repairRank_lt_of_mem_support
    (P : X → A → PMF X) (K : Set X) (x : X)
    (hx : StrongRepairable P K x) (hxK : x ∉ K)
    {y : X}
    (hy : y ∈ (P x (descendingRepairAction P K x)).support) :
    ∃ hyR : StrongRepairable P K y,
      repairRank P K y hyR < repairRank P K x hx := by
  obtain ⟨n, hr, hs⟩ :=
    descendingRepairAction_staysIn_previous P K x hx hxK
  have hyn : y ∈ repairIter P K n := hs hy
  let hyR : StrongRepairable P K y := ⟨n, hyn⟩
  refine ⟨hyR, ?_⟩
  have hle : repairRank P K y hyR ≤ n :=
    repairRank_le_of_mem P K y hyR hyn
  omega

theorem support_path_hits_by_rank
    (P : X → A → PMF X) (K : Set X)
    (x : X) (hx : StrongRepairable P K x)
    (omega : ℕ → X)
    (h0 : omega 0 = x)
    (hpath : ∀ t : ℕ, omega t ∉ K →
      omega (t + 1) ∈
        (P (omega t) (descendingRepairAction P K (omega t))).support) :
    ∃ n : ℕ, n ≤ repairRank P K x hx ∧ omega n ∈ K := by
  classical
  by_cases hxK : x ∈ K
  · exact ⟨0, Nat.zero_le _, by simpa [h0] using hxK⟩
  · have hsup :
        omega 1 ∈
          (P x (descendingRepairAction P K x)).support := by
      rw [← h0]
      simpa using hpath 0 (by simpa [h0] using hxK)
    obtain ⟨hyR, hlt⟩ :=
      repairRank_lt_of_mem_support P K x hx hxK hsup
    let tail : ℕ → X := fun n => omega (n + 1)
    have htailPath : ∀ t : ℕ, tail t ∉ K →
        tail (t + 1) ∈
          (P (tail t) (descendingRepairAction P K (tail t))).support := by
      intro t ht
      simpa [tail, Nat.add_assoc] using hpath (t + 1) ht
    obtain ⟨n, hnrank, hnK⟩ :=
      support_path_hits_by_rank P K (omega 1) hyR tail rfl htailPath
    refine ⟨n + 1, ?_, ?_⟩
    · have hnr : n < repairRank P K x hx :=
        lt_of_le_of_lt hnrank hlt
      omega
    · simpa [tail] using hnK
termination_by repairRank P K x hx
decreasing_by exact hlt

end UEOT.V3.Compression.Objecthood
