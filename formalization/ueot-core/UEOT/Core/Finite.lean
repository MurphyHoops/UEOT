import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

namespace UEOT.Finite

universe u
variable {V : Type u}

def Minimal (P : Finset V → Prop) (S : Finset V) : Prop :=
  P S ∧ ∀ T, T ⊆ S → P T → T = S

theorem exists_minimal_subset (P : Finset V → Prop) (S : Finset V) (hS : P S) :
    ∃ M, M ⊆ S ∧ Minimal P M := by
  classical
  let candidates := S.powerset.filter P
  have hmem : S ∈ candidates := by simp [candidates, hS]
  obtain ⟨M, hM, hmin⟩ := candidates.exists_min_image Finset.card ⟨S, hmem⟩
  have hMp : M ⊆ S ∧ P M := by simpa [candidates] using hM
  refine ⟨M, hMp.1, hMp.2, ?_⟩
  intro T hTM hT
  apply Finset.eq_of_subset_of_card_le hTM
  apply hmin T
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hTM.trans hMp.1, hT⟩

theorem minimal_antichain (P : Finset V → Prop) {S T : Finset V}
    (hS : Minimal P S) (hT : Minimal P T) (hST : S ⊆ T) : S = T :=
  hT.2 S hST hS.1

end UEOT.Finite
