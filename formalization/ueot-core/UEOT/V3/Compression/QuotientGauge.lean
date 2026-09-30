import UEOT.V3.Compression.QuotientDescent

/-!
# Quotient gauge: exact representations are unique up to relabeling

Two surjective representations of the same source that induce exactly the same
fibres should be regarded as the same quotient object up to a unique bijective
relabeling of quotient states.

This module derives that fact directly from M-QD's universal descent property.
It is a prerequisite for comparing moving encoders without making conclusions
depend on arbitrary state labels.
-/

namespace UEOT.V3.Compression.QuotientGauge

open Function
open UEOT.V3.Compression.QuotientDescent

universe uX uY uZ

/-- Two representations induce exactly the same partition of the source. -/
def SameFibers
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    (q : X → Y) (r : X → Z) : Prop :=
  ∀ x x', q x = q x' ↔ r x = r x'

theorem sameFibers_refl
    {X : Type uX} {Y : Type uY} (q : X → Y) :
    SameFibers q q := by
  intro x x'
  rfl

theorem sameFibers_symm
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {q : X → Y} {r : X → Z}
    (h : SameFibers q r) :
    SameFibers r q := by
  intro x x'
  exact (h x x').symm

/-- Equal fibres make `r` descend through `q`. -/
theorem right_fiberCompatible_of_sameFibers
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {q : X → Y} {r : X → Z}
    (h : SameFibers q r) :
    FiberCompatible q r := by
  intro x x' hq
  exact (h x x').mp hq

/-- Equal fibres make `q` descend through `r`. -/
theorem left_fiberCompatible_of_sameFibers
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {q : X → Y} {r : X → Z}
    (h : SameFibers q r) :
    FiberCompatible r q := by
  intro x x' hr
  exact (h x x').mpr hr

/-- Canonical relabeling between two surjective quotient representations with
the same fibres.  The forward and inverse maps are both M-QD descents. -/
noncomputable def quotientEquiv
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    (q : X → Y) (r : X → Z)
    (hq : Surjective q) (hr : Surjective r)
    (hsame : SameFibers q r) :
    Y ≃ Z where
  toFun := descend q r hq (right_fiberCompatible_of_sameFibers hsame)
  invFun := descend r q hr (left_fiberCompatible_of_sameFibers hsame)
  left_inv := by
    intro y
    rcases hq y with ⟨x, rfl⟩
    have hforward := congrFun
      (descend_comp q r hq (right_fiberCompatible_of_sameFibers hsame)) x
    have hback := congrFun
      (descend_comp r q hr (left_fiberCompatible_of_sameFibers hsame)) x
    simp only [Function.comp_apply] at hforward hback
    rw [hforward, hback]
  right_inv := by
    intro z
    rcases hr z with ⟨x, rfl⟩
    have hforward := congrFun
      (descend_comp q r hq (right_fiberCompatible_of_sameFibers hsame)) x
    have hback := congrFun
      (descend_comp r q hr (left_fiberCompatible_of_sameFibers hsame)) x
    simp only [Function.comp_apply] at hforward hback
    rw [hback, hforward]

/-- The canonical equivalence literally transports one representation to the
other on every source point. -/
theorem quotientEquiv_comp
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    (q : X → Y) (r : X → Z)
    (hq : Surjective q) (hr : Surjective r)
    (hsame : SameFibers q r) :
    quotientEquiv q r hq hr hsame ∘ q = r := by
  exact descend_comp q r hq (right_fiberCompatible_of_sameFibers hsame)

/-- Any other equivalence carrying `q` to `r` has the same forward map as the
canonical quotient relabeling. -/
theorem quotientEquiv_unique
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    (q : X → Y) (r : X → Z)
    (hq : Surjective q) (hr : Surjective r)
    (hsame : SameFibers q r)
    (e : Y ≃ Z)
    (he : e ∘ q = r) :
    e = quotientEquiv q r hq hr hsame := by
  apply Equiv.ext
  have hfun := eq_descend_of_comp_eq
    q r hq (right_fiberCompatible_of_sameFibers hsame) e he
  intro y
  exact congrFun hfun y

/-- Source-level characterization: for surjective maps, equal fibres are
equivalent to existence of a unique quotient-state equivalence transporting one
representation to the other. -/
theorem sameFibers_iff_existsUnique_equiv
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    (q : X → Y) (r : X → Z)
    (hq : Surjective q) (hr : Surjective r) :
    SameFibers q r ↔
      ∃! e : Y ≃ Z, e ∘ q = r := by
  constructor
  · intro hsame
    refine ⟨quotientEquiv q r hq hr hsame,
      quotientEquiv_comp q r hq hr hsame, ?_⟩
    intro e he
    exact quotientEquiv_unique q r hq hr hsame e he
  · rintro ⟨e, he, _⟩
    intro x x'
    constructor
    · intro hqxx
      calc
        r x = e (q x) := by
          symm
          simpa only [Function.comp_apply] using congrFun he x
        _ = e (q x') := by rw [hqxx]
        _ = r x' := by
          simpa only [Function.comp_apply] using congrFun he x'
    · intro hrxx
      apply e.injective
      calc
        e (q x) = r x := by
          simpa only [Function.comp_apply] using congrFun he x
        _ = r x' := hrxx
        _ = e (q x') := by
          symm
          simpa only [Function.comp_apply] using congrFun he x'

end UEOT.V3.Compression.QuotientGauge
