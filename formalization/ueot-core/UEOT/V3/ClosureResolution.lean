import Mathlib

/-!
# UEOT Core v3 — closure systems and resolution composition

This module starts the exact D-RES / P-RES-02 formalization.  A closure system
is represented as a Moore family: it contains the universe and is closed under
nonempty arbitrary intersections.  On the finite carrier used by the source
specification this is equivalent to the usual finite-intersection closure and
gives the same closure operator.
-/

namespace UEOT.V3.ClosureResolution

universe u
variable {V : Type u}

structure ClosureSystem (V : Type u) where
  carrier : Set (Set V)
  univ_mem : (Set.univ : Set V) ∈ carrier
  sInter_mem :
    ∀ F : Set (Set V), F ⊆ carrier → F.Nonempty → ⋂₀ F ∈ carrier

def closure (L : ClosureSystem V) (S : Set V) : Set V :=
  ⋂₀ {A : Set V | A ∈ L.carrier ∧ S ⊆ A}

theorem candidates_nonempty (L : ClosureSystem V) (S : Set V) :
    ({A : Set V | A ∈ L.carrier ∧ S ⊆ A}).Nonempty := by
  refine ⟨Set.univ, L.univ_mem, ?_⟩
  exact Set.subset_univ S

theorem subset_closure (L : ClosureSystem V) (S : Set V) :
    S ⊆ closure L S := by
  intro x hx
  apply Set.mem_sInter
  intro A hA
  exact hA.2 hx

theorem closure_mem (L : ClosureSystem V) (S : Set V) :
    closure L S ∈ L.carrier := by
  apply L.sInter_mem
  · intro A hA
    exact hA.1
  · exact candidates_nonempty L S

theorem closure_least (L : ClosureSystem V) {S A : Set V}
    (hA : A ∈ L.carrier) (hSA : S ⊆ A) :
    closure L S ⊆ A := by
  exact Set.sInter_subset_of_mem ⟨hA, hSA⟩

theorem closure_eq_of_mem (L : ClosureSystem V) {S : Set V}
    (hS : S ∈ L.carrier) :
    closure L S = S := by
  apply Set.Subset.antisymm
  · exact closure_least L hS Set.Subset.rfl
  · exact subset_closure L S

theorem closure_mono (L : ClosureSystem V) {S T : Set V}
    (hST : S ⊆ T) :
    closure L S ⊆ closure L T := by
  apply closure_least L (closure_mem L T)
  exact hST.trans (subset_closure L T)

/-! P-RES-02, operator part:
if the coarse closed family is contained in the finer closed family, then
closing first at the fine level does not change the subsequent coarse closure.
-/
theorem closure_comp_of_nested
    (Lr Ls : ClosureSystem V)
    (hrs : Lr.carrier ⊆ Ls.carrier)
    (S : Set V) :
    closure Lr (closure Ls S) = closure Lr S := by
  apply Set.Subset.antisymm
  · apply closure_least Lr (closure_mem Lr S)
    apply closure_least Ls
    · exact hrs (closure_mem Lr S)
    · exact subset_closure Lr S
  · apply closure_mono Lr
    exact subset_closure Ls S

end UEOT.V3.ClosureResolution
