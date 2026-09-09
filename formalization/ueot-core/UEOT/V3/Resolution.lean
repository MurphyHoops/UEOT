import UEOT.Core.Resolution

namespace UEOT.V3.Resolution
open UEOT.Resolution

theorem realization_interval {V W : Type*} (π : V → W)
    (C : Set (Set W)) (F : Set (Set V))
    (hC : Upward C) (hF : Upward F) :
    restrict π F = C ↔ lower π C ⊆ F ∧ F ⊆ upper π C := by
  constructor
  · intro h
    constructor
    · exact (lower_adjunction π C F hF).2 (by rw [h])
    · exact (upper_adjunction π F C hF hC).1 (by rw [h])
  · rintro ⟨hlo, hhi⟩
    apply Set.Subset.antisymm
    · exact (upper_adjunction π F C hF hC).2 hhi
    · exact (lower_adjunction π C F hF).1 hlo

/-! ## Finite-clutter bridge for P-RES-05

`UpClosure C` is the family generated upward by the carrier clutter `C`.
`PushMin π C D` is the extensional characterization of
`π_* C = D`: every coarse minimal edge is attained exactly by an image of a
fine edge, while every fine image contains a coarse minimal edge.

For the finite Boolean setting of the source specification, `D` is a clutter,
hence an antichain. The theorem below is slightly more general: finiteness is
not used once the attained/cofinal characterization is stated explicitly.
-/

def UpClosure {X : Type*} (C : Set (Set X)) : Set (Set X) :=
  {S | ∃ E ∈ C, E ⊆ S}

def IsAntichain {X : Type*} (C : Set (Set X)) : Prop :=
  ∀ ⦃A B⦄, A ∈ C → B ∈ C → A ⊆ B → A = B

def PushMin {V W : Type*} (π : V → W)
    (C : Set (Set V)) (D : Set (Set W)) : Prop :=
  (∀ d ∈ D, ∃ c ∈ C, π '' c = d) ∧
  (∀ c ∈ C, ∃ d ∈ D, d ⊆ π '' c)

theorem upClosure_upward {X : Type*} (C : Set (Set X)) :
    Upward (UpClosure C) := by
  rintro S ⟨E, hE, hES⟩ T hST
  exact ⟨E, hE, hES.trans hST⟩

theorem restrict_upClosure_iff_pushMin {V W : Type*} (π : V → W)
    (C : Set (Set V)) (D : Set (Set W)) (hD : IsAntichain D) :
    restrict π (UpClosure C) = UpClosure D ↔ PushMin π C D := by
  constructor
  · intro h
    constructor
    · intro d hd
      have hpre : π ⁻¹' d ∈ UpClosure C := by
        have : d ∈ restrict π (UpClosure C) := by
          rw [h]
          exact ⟨d, hd, Set.Subset.rfl⟩
        exact this
      rcases hpre with ⟨c, hc, hcpre⟩
      have himgSub : π '' c ⊆ d := by
        rintro y ⟨x, hx, rfl⟩
        exact hcpre hx
      have himgMem : π '' c ∈ UpClosure D := by
        rw [← h]
        exact ⟨c, hc, fun x hx => ⟨x, hx, rfl⟩⟩
      rcases himgMem with ⟨d', hd', hd'sub⟩
      have hdd' : d' = d := hD hd' hd (hd'sub.trans himgSub)
      refine ⟨c, hc, Set.Subset.antisymm himgSub ?_⟩
      rw [← hdd']
      exact hd'sub
    · intro c hc
      have himgMem : π '' c ∈ UpClosure D := by
        rw [← h]
        exact ⟨c, hc, fun x hx => ⟨x, hx, rfl⟩⟩
      rcases himgMem with ⟨d, hd, hsub⟩
      exact ⟨d, hd, hsub⟩
  · rintro ⟨hattain, hcover⟩
    ext B
    constructor
    · intro hB
      rcases hB with ⟨c, hc, hcpre⟩
      rcases hcover c hc with ⟨d, hd, hdsub⟩
      refine ⟨d, hd, ?_⟩
      intro y hy
      rcases hdsub hy with ⟨x, hxc, rfl⟩
      exact hcpre hxc
    · rintro ⟨d, hd, hdB⟩
      rcases hattain d hd with ⟨c, hc, himg⟩
      refine ⟨c, hc, ?_⟩
      intro x hxc
      apply hdB
      rw [← himg]
      exact ⟨x, hxc, rfl⟩

theorem clutter_realization_interval {V W : Type*} (π : V → W)
    (C : Set (Set V)) (D : Set (Set W)) (hD : IsAntichain D) :
    PushMin π C D ↔
      lower π (UpClosure D) ⊆ UpClosure C ∧
      UpClosure C ⊆ upper π (UpClosure D) := by
  calc
    PushMin π C D ↔ restrict π (UpClosure C) = UpClosure D :=
      (restrict_upClosure_iff_pushMin π C D hD).symm
    _ ↔ lower π (UpClosure D) ⊆ UpClosure C ∧
        UpClosure C ⊆ upper π (UpClosure D) :=
      realization_interval π (UpClosure D) (UpClosure C)
        (upClosure_upward D) (upClosure_upward C)

end UEOT.V3.Resolution
