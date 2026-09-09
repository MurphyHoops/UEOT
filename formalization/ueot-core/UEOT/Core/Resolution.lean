import Mathlib.Data.Set.Image

/-! Resolution adjunctions for upper families, P-RES-04. -/

namespace UEOT.Resolution

universe u v
variable {V : Type u} {W : Type v}

def Upward {X : Type*} (A : Set (Set X)) : Prop :=
  ∀ S ∈ A, ∀ T, S ⊆ T → T ∈ A

def restrict (π : V → W) (A : Set (Set V)) : Set (Set W) :=
  {B | π ⁻¹' B ∈ A}

def lower (π : V → W) (A : Set (Set W)) : Set (Set V) :=
  {S | ∃ B ∈ A, π ⁻¹' B ⊆ S}

def upper (π : V → W) (A : Set (Set W)) : Set (Set V) :=
  {S | π '' S ∈ A}

theorem restrict_upward (π : V → W) {A : Set (Set V)} (hA : Upward A) :
    Upward (restrict π A) := by
  intro B hB C hBC
  exact hA _ hB _ (fun _ hx => hBC hx)

theorem lower_upward (π : V → W) (A : Set (Set W)) : Upward (lower π A) := by
  rintro S ⟨B, hB, hBS⟩ T hST
  exact ⟨B, hB, hBS.trans hST⟩

theorem upper_upward (π : V → W) {A : Set (Set W)} (hA : Upward A) :
    Upward (upper π A) := by
  intro S hS T hST
  exact hA _ hS _ (Set.image_mono hST)

theorem lower_adjunction (π : V → W) (C : Set (Set W))
    (F : Set (Set V)) (hF : Upward F) :
    lower π C ⊆ F ↔ C ⊆ restrict π F := by
  constructor
  · intro h B hB
    exact h ⟨B, hB, Set.Subset.rfl⟩
  · rintro h S ⟨B, hB, hBS⟩
    exact hF _ (h hB) S hBS

theorem upper_adjunction (π : V → W) (F : Set (Set V)) (C : Set (Set W))
    (hF : Upward F) (hC : Upward C) :
    restrict π F ⊆ C ↔ F ⊆ upper π C := by
  constructor
  · intro h S hS
    apply h
    exact hF S hS _ (fun x hx => ⟨x, hx, rfl⟩)
  · intro h B hB
    exact hC _ (h hB) B (by rintro y ⟨x, hx, rfl⟩; exact hx)

theorem restrict_lower (π : V → W) (C : Set (Set W)) :
    C ⊆ restrict π (lower π C) := by
  intro B hB
  exact ⟨B, hB, Set.Subset.rfl⟩

theorem restrict_upper (π : V → W) (C : Set (Set W))
    (surj : Function.Surjective π) :
    restrict π (upper π C) = C := by
  ext B
  constructor
  · intro h
    simpa [upper, restrict, Set.image_preimage_eq _ surj] using h
  · intro h
    simpa [upper, restrict, Set.image_preimage_eq _ surj] using h

end UEOT.Resolution
