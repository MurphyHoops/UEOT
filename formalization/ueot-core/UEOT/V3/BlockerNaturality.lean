import UEOT.Core.Blocker
import Mathlib.Data.Finset.Image

/-! P-RES-03: finite Boolean blocker naturality, including empty families. -/
namespace UEOT.V3.BlockerNaturality
open UEOT.Blocker

def minFamily {V : Type*} (G : Set (Finset V)) : Set (Finset V) :=
  {S | Finite.Minimal (fun T => T ∈ G) S}

def upward {V : Type*} (G : Set (Finset V)) : Set (Finset V) :=
  {S | ∃ M ∈ G, M ⊆ S}

theorem minimal_upward {V : Type*} (G : Set (Finset V)) :
    minFamily (upward G) = minFamily G := by
  ext S
  constructor
  · rintro ⟨⟨M, hM, hMS⟩, hmin⟩
    have e : M = S := hmin M hMS ⟨M, hM, Finset.Subset.refl _⟩
    refine ⟨e ▸ hM, ?_⟩
    intro T hTS hT
    exact hmin T hTS ⟨T, hT, Finset.Subset.refl _⟩
  · rintro ⟨hS, hmin⟩
    refine ⟨⟨S, hS, Finset.Subset.refl _⟩, ?_⟩
    rintro T hTS ⟨M, hM, hMT⟩
    have e : M = S := hmin M (hMT.trans hTS) hM
    exact Finset.Subset.antisymm hTS (e ▸ hMT)

theorem hits_minFamily {V : Type*} (G : Set (Finset V)) (D : Finset V) :
    Hits (minFamily G) D ↔ Hits G D := by
  constructor
  · intro h M hM
    obtain ⟨N, hNM, hN⟩ := Finite.exists_minimal_subset (fun T => T ∈ G) M hM
    obtain ⟨v, hvD, hvN⟩ := h N hN
    exact ⟨v, hvD, hNM hvN⟩
  · intro h M hM
    exact h M hM.1

def images {V W : Type*} [DecidableEq W] (π : V → W)
    (G : Set (Finset V)) : Set (Finset W) :=
  {B | ∃ M ∈ G, M.image π = B}

def push {V W : Type*} [DecidableEq W] (π : V → W)
    (G : Set (Finset V)) : Set (Finset W) := minFamily (images π G)

/-! Re-derived from the historical module's downstream type constraints:
hitting all image edges is exactly hitting all original edges with the
preimage of the hitting set. -/
theorem image_hits {V W : Type*} [Fintype V] [DecidableEq W]
    (π : V → W) (G : Set (Finset V)) (T : Finset W) :
    Hits (images π G) T ↔
      Hits G (Finset.univ.filter fun v => π v ∈ T) := by
  classical
  constructor
  · intro h M hM
    obtain ⟨w, hwT, hwImg⟩ := h (M.image π) ⟨M, hM, rfl⟩
    obtain ⟨v, hvM, hvw⟩ := Finset.mem_image.mp hwImg
    subst w
    exact ⟨v, by simp [hwT], hvM⟩
  · intro h B hB
    rcases hB with ⟨M, hM, rfl⟩
    obtain ⟨v, hvPre, hvM⟩ := h M hM
    have hvT : π v ∈ T := (Finset.mem_filter.mp hvPre).2
    exact ⟨π v, hvT, Finset.mem_image.mpr ⟨v, hvM, rfl⟩⟩

theorem hits_push_iff {V W : Type*} [Fintype V] [DecidableEq W]
    (π : V → W) (G : Set (Finset V)) (T : Finset W) :
    Hits (push π G) T ↔ T ∈ upward (images π (blocker G)) := by
  rw [push, hits_minFamily, image_hits, hits_iff_contains_blocker]
  constructor
  · rintro ⟨D, hD, hDT⟩
    refine ⟨D.image π, ⟨D, hD, rfl⟩, ?_⟩
    intro w hw
    obtain ⟨v, hvD, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp (hDT hvD)).2
  · rintro ⟨B, ⟨D, hD, rfl⟩, hDT⟩
    refine ⟨D, hD, ?_⟩
    intro v hvD
    have hv := hDT (Finset.mem_image.mpr ⟨v, hvD, rfl⟩)
    simp [hv]

theorem blocker_naturality {V W : Type*} [Fintype V] [DecidableEq W]
    (π : V → W) (G : Set (Finset V)) : blocker (push π G) = push π (blocker G) := by
  have h : Hits (push π G) = (fun T => T ∈ upward (images π (blocker G))) := by
    funext T
    exact propext (hits_push_iff π G T)
  change minFamily {T | Hits (push π G) T} = minFamily (images π (blocker G))
  rw [h]
  exact minimal_upward _

end UEOT.V3.BlockerNaturality
