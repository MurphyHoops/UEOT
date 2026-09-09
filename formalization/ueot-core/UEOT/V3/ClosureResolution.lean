import Mathlib
import UEOT.V3.Resolution

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
  change x ∈ ⋂₀ {A : Set V | A ∈ L.carrier ∧ S ⊆ A}
  exact (Set.mem_sInter).2 (by
    intro A hA
    exact hA.2 hx)

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


open UEOT.V3.Resolution

def imageClosure (L : ClosureSystem V) (M : Set (Set V)) : Set (Set V) :=
  (closure L) '' M

def resolutionMap (L : ClosureSystem V) (M : Set (Set V)) : Set (Set V) :=
  MinimalFamily (imageClosure L M)

theorem imageClosure_finite (L : ClosureSystem V) {M : Set (Set V)}
    (hM : M.Finite) :
    (imageClosure L M).Finite := by
  exact hM.image (closure L)

theorem minimalFamily_cofinal {F : Set (Set V)}
    (hF : F.Finite) {S : Set V} (hS : S ∈ F) :
    ∃ M ∈ MinimalFamily F, M ⊆ S := by
  obtain ⟨M, hMS, hMmin⟩ := hF.exists_le_minimal hS
  exact ⟨M, hMmin, hMS⟩

theorem upClosure_resolutionMap (L : ClosureSystem V)
    {M : Set (Set V)} (hM : M.Finite) :
    UpClosure (resolutionMap L M) = UpClosure (imageClosure L M) := by
  ext S
  constructor
  · rintro ⟨E, hE, hES⟩
    exact ⟨E, hE.prop, hES⟩
  · rintro ⟨E, hE, hES⟩
    obtain ⟨D, hD, hDE⟩ :=
      minimalFamily_cofinal (imageClosure_finite L hM) hE
    exact ⟨D, hD, hDE.trans hES⟩

theorem minimalFamily_subset_of_upClosure_eq
    {F G : Set (Set V)}
    (hFG : UpClosure F = UpClosure G) :
    MinimalFamily F ⊆ MinimalFamily G := by
  intro S hS
  have hSUF : S ∈ UpClosure F := ⟨S, hS.prop, Set.Subset.rfl⟩
  have hSUG : S ∈ UpClosure G := by
    rw [← hFG]
    exact hSUF
  rcases hSUG with ⟨G0, hG0, hG0S⟩
  have hG0UF : G0 ∈ UpClosure F := by
    rw [hFG]
    exact ⟨G0, hG0, Set.Subset.rfl⟩
  rcases hG0UF with ⟨F0, hF0, hF0G0⟩
  have hF0S : F0 ⊆ S := hF0G0.trans hG0S
  have hSF0 : S ⊆ F0 := hS.le_of_le hF0 hF0S
  have hSG0 : S ⊆ G0 := hSF0.trans hF0G0
  have hG0eq : G0 = S := Set.Subset.antisymm hG0S hSG0
  subst G0
  refine ⟨hG0, ?_⟩
  intro T hT hTS
  have hTUF : T ∈ UpClosure F := by
    rw [hFG]
    exact ⟨T, hT, Set.Subset.rfl⟩
  rcases hTUF with ⟨F1, hF1, hF1T⟩
  exact (hS.le_of_le hF1 (hF1T.trans hTS)).trans hF1T

theorem minimalFamily_eq_of_upClosure_eq
    {F G : Set (Set V)}
    (hFG : UpClosure F = UpClosure G) :
    MinimalFamily F = MinimalFamily G := by
  apply Set.Subset.antisymm
  · exact minimalFamily_subset_of_upClosure_eq hFG
  · exact minimalFamily_subset_of_upClosure_eq hFG.symm

theorem upClosure_imageClosure_resolutionMap
    (Lr Ls : ClosureSystem V)
    (hrs : Lr.carrier ⊆ Ls.carrier)
    {M : Set (Set V)} (hM : M.Finite) :
    UpClosure (imageClosure Lr (resolutionMap Ls M)) =
      UpClosure (imageClosure Lr M) := by
  ext S
  constructor
  · rintro ⟨E, ⟨D, hD, rfl⟩, hES⟩
    rcases hD.prop with ⟨m, hm, rfl⟩
    refine ⟨closure Lr m, ⟨m, hm, rfl⟩, ?_⟩
    rw [← closure_comp_of_nested Lr Ls hrs m]
    exact hES
  · rintro ⟨E, ⟨m, hm, rfl⟩, hES⟩
    have hImg : closure Ls m ∈ imageClosure Ls M := ⟨m, hm, rfl⟩
    obtain ⟨D, hD, hDsub⟩ :=
      minimalFamily_cofinal (imageClosure_finite Ls hM) hImg
    refine ⟨closure Lr D, ⟨D, hD, rfl⟩, ?_⟩
    have hmono :
        closure Lr D ⊆ closure Lr (closure Ls m) :=
      closure_mono Lr hDsub
    rw [closure_comp_of_nested Lr Ls hrs m] at hmono
    exact hmono.trans hES

/-! P-RES-02, minimal-family part.  This theorem is stronger than the
three-scale source statement: the top-scale family need only be finite; it does
not need an additional closedness assumption for the composition identity. -/
theorem resolutionMap_comp
    (Lr Ls : ClosureSystem V)
    (hrs : Lr.carrier ⊆ Ls.carrier)
    {M : Set (Set V)} (hM : M.Finite) :
    resolutionMap Lr M =
      resolutionMap Lr (resolutionMap Ls M) := by
  unfold resolutionMap
  apply minimalFamily_eq_of_upClosure_eq
  exact (upClosure_imageClosure_resolutionMap Lr Ls hrs hM).symm


def admissibleMin (L : ClosureSystem V) (A : Set (Set V)) : Set (Set V) :=
  MinimalFamily (A ∩ L.carrier)

theorem closure_admissible
    (L : ClosureSystem V) {A : Set (Set V)}
    (hA : UEOT.Resolution.Upward A)
    {M : Set V} (hM : M ∈ A) :
    closure L M ∈ A ∩ L.carrier := by
  constructor
  · exact hA M hM (closure L M) (subset_closure L M)
  · exact closure_mem L M

/-! P-RES-01: coarse-graining of minimal admissible properties. -/
theorem minimal_property_coarse_graining
    (Lr Ls : ClosureSystem V)
    (hrs : Lr.carrier ⊆ Ls.carrier)
    {A : Set (Set V)}
    (hA : UEOT.Resolution.Upward A)
    (hFinite : (A ∩ Ls.carrier).Finite) :
    admissibleMin Lr A =
      resolutionMap Lr (admissibleMin Ls A) := by
  ext S
  constructor
  · intro hS
    have hSfine : S ∈ A ∩ Ls.carrier :=
      ⟨hS.prop.1, hrs hS.prop.2⟩
    obtain ⟨M, hM, hMS⟩ :=
      minimalFamily_cofinal hFinite hSfine
    have hclS : closure Lr M ⊆ S :=
      closure_least Lr hS.prop.2 hMS
    have hclAdm : closure Lr M ∈ A ∩ Lr.carrier :=
      closure_admissible Lr hA hM.prop.1
    have hScl : S ⊆ closure Lr M :=
      hS.le_of_le hclAdm hclS
    have hEq : closure Lr M = S :=
      Set.Subset.antisymm hclS hScl
    change Minimal
      (fun T => T ∈ imageClosure Lr (admissibleMin Ls A)) S
    refine ⟨⟨M, hM, hEq⟩, ?_⟩
    intro T hT hTS
    rcases hT with ⟨M', hM', rfl⟩
    have hTAdm : closure Lr M' ∈ A ∩ Lr.carrier :=
      closure_admissible Lr hA hM'.prop.1
    exact hS.le_of_le hTAdm hTS
  · intro hS
    change Minimal
      (fun T => T ∈ imageClosure Lr (admissibleMin Ls A)) S at hS
    rcases hS.prop with ⟨M, hM, hEq⟩
    have hSAdm : S ∈ A ∩ Lr.carrier := by
      rw [← hEq]
      exact closure_admissible Lr hA hM.prop.1
    change Minimal (fun T => T ∈ A ∩ Lr.carrier) S
    refine ⟨hSAdm, ?_⟩
    intro B hB hBS
    have hBfine : B ∈ A ∩ Ls.carrier :=
      ⟨hB.1, hrs hB.2⟩
    obtain ⟨M', hM', hM'B⟩ :=
      minimalFamily_cofinal hFinite hBfine
    have hclB : closure Lr M' ⊆ B :=
      closure_least Lr hB.2 hM'B
    have hImg :
        closure Lr M' ∈ imageClosure Lr (admissibleMin Ls A) :=
      ⟨M', hM', rfl⟩
    have hclS : closure Lr M' ⊆ S :=
      hclB.trans hBS
    have hScl : S ⊆ closure Lr M' :=
      hS.le_of_le hImg hclS
    exact hScl.trans hclB

end UEOT.V3.ClosureResolution
