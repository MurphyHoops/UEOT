import UEOT.Core.Finite
import Mathlib.Data.Fintype.Powerset

/-! Finite Boolean access/blocker duality. These theorems quantify over all
finite universes, not a list of enumerated examples. -/

namespace UEOT.Blocker

universe u
variable {V : Type u}

def Hits (G : Set (Finset V)) (D : Finset V) : Prop :=
  ∀ M ∈ G, ∃ v, v ∈ D ∧ v ∈ M

def blocker (G : Set (Finset V)) : Set (Finset V) :=
  {D | Finite.Minimal (Hits G) D}

def IsClutter (G : Set (Finset V)) : Prop :=
  ∀ S ∈ G, ∀ T ∈ G, S ⊆ T → S = T

theorem hits_mono {G : Set (Finset V)} {D E : Finset V}
    (hDE : D ⊆ E) (hD : Hits G D) : Hits G E := by
  intro M hM
  obtain ⟨v, hvD, hvM⟩ := hD M hM
  exact ⟨v, hDE hvD, hvM⟩

theorem blocker_isClutter (G : Set (Finset V)) : IsClutter (blocker G) := by
  intro S hS T hT hST
  exact Finite.minimal_antichain _ hS hT hST

theorem hits_iff_contains_blocker (G : Set (Finset V)) (D : Finset V) :
    Hits G D ↔ ∃ E ∈ blocker G, E ⊆ D := by
  constructor
  · intro h
    obtain ⟨E, hED, hE⟩ := Finite.exists_minimal_subset (Hits G) D h
    exact ⟨E, hE, hED⟩
  · rintro ⟨E, hE, hED⟩
    exact hits_mono hED hE.1

theorem access_failure_iff_hits (G : Set (Finset V)) (D : Finset V) :
    (¬ ∃ M ∈ G, ∀ v ∈ M, v ∉ D) ↔ Hits G D := by
  classical
  constructor
  · intro h M hM
    by_contra hn
    apply h
    refine ⟨M, hM, ?_⟩
    intro v hvM hvD
    exact hn ⟨v, hvD, hvM⟩
  · rintro h ⟨M, hM, hdis⟩
    obtain ⟨v, hvD, hvM⟩ := h M hM
    exact hdis v hvM hvD

theorem hits_blocker_iff [Fintype V] (G : Set (Finset V)) (S : Finset V) :
    Hits (blocker G) S ↔ ∃ M ∈ G, M ⊆ S := by
  classical
  constructor
  · intro h
    by_contra hn
    have hc : Hits G (Finset.univ \ S) := by
      intro M hM
      have hnot : ¬ M ⊆ S := fun hMS => hn ⟨M, hM, hMS⟩
      obtain ⟨v, hvM, hvS⟩ := Finset.not_subset.mp hnot
      exact ⟨v, by simp [hvS], hvM⟩
    obtain ⟨D, hD, hDS⟩ := (hits_iff_contains_blocker G _).1 hc
    obtain ⟨v, hvS, hvD⟩ := h D hD
    exact (Finset.mem_sdiff.mp (hDS hvD)).2 hvS
  · rintro ⟨M, hM, hMS⟩ D hD
    obtain ⟨v, hvD, hvM⟩ := hD.1 M hM
    exact ⟨v, hMS hvM, hvD⟩

theorem blocker_involution [Fintype V] (G : Set (Finset V)) (hG : IsClutter G) :
    blocker (blocker G) = G := by
  ext S
  constructor
  · intro hS
    obtain ⟨M, hM, hMS⟩ := (hits_blocker_iff G S).1 hS.1
    have e : M = S := hS.2 M hMS ((hits_blocker_iff G M).2 ⟨M, hM, Finset.Subset.refl _⟩)
    exact e ▸ hM
  · intro hS
    refine ⟨(hits_blocker_iff G S).2 ⟨S, hS, Finset.Subset.refl _⟩, ?_⟩
    intro T hTS hT
    obtain ⟨M, hM, hMT⟩ := (hits_blocker_iff G T).1 hT
    have e : M = S := hG M hM S hS (hMT.trans hTS)
    exact Finset.Subset.antisymm hTS (e ▸ hMT)

theorem blocker_empty : blocker (∅ : Set (Finset V)) = {∅} := by
  ext S
  constructor
  · intro h
    have e := h.2 ∅ (Finset.empty_subset S) (by intro M hM; exact False.elim hM)
    exact Set.mem_singleton_iff.mpr e.symm
  · intro h
    have e : S = ∅ := Set.mem_singleton_iff.mp h
    subst S
    refine ⟨?_, ?_⟩
    · intro M hM
      exact False.elim hM
    · intro T hT _
      exact Finset.subset_empty.mp hT

theorem blocker_singleton_empty : blocker ({∅} : Set (Finset V)) = ∅ := by
  ext S
  constructor
  · intro h
    obtain ⟨v, _, hv⟩ := h.1 ∅ (by simp)
    exact Finset.notMem_empty v hv
  · intro h
    exact False.elim h

end UEOT.Blocker
