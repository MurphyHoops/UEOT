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

end UEOT.V3.Resolution
