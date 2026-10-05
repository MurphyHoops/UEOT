import Mathlib.Data.Set.Basic

/-!
# P1.1 — Admissible futures

Purpose is first scoped to a declared set of admissible futures.  This stage
introduces only the typed domain `Γ_Ω`; preference, scalar representation and
expected-value structure are deliberately deferred.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set

universe uF

/-- The admissible-future set `Γ_Ω` for one declared object/context. -/
abbrev AdmissibleFutures (Future : Type uF) := Set Future

/-- A future together with evidence that it lies in the admissible set. -/
abbrev AdmissibleFuture
    {Future : Type uF} (Γ : AdmissibleFutures Future) :=
  {future : Future // future ∈ Γ}

@[simp] theorem admissibleFuture_mem
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    (x : AdmissibleFuture Γ) : (x : Future) ∈ Γ :=
  x.property

/-- A nonempty admissible domain has at least one typed admissible future. -/
theorem exists_admissibleFuture
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    (hΓ : Γ.Nonempty) : Nonempty (AdmissibleFuture Γ) := by
  rcases hΓ with ⟨x, hx⟩
  exact ⟨⟨x, hx⟩⟩

/-- Weak teleological preference on the typed admissible-future domain. -/
abbrev PreferenceRelation
    {Future : Type uF} (Γ : AdmissibleFutures Future) :=
  AdmissibleFuture Γ → AdmissibleFuture Γ → Prop

/-- Minimal preorder discipline for teleological preference. -/
def IsPreferencePreorder
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    (prefers : PreferenceRelation Γ) : Prop :=
  (∀ x, prefers x x) ∧
    ∀ ⦃x y z⦄, prefers x y → prefers y z → prefers x z

/-- Minimal general teleological contract.

The contract declares which futures are admissible and how they are weakly
ordered. It contains no scalar objective, no totality/completeness assumption,
no uniqueness statement and no Π/Φ decomposition. -/
structure TeleologicalContract (Future : Type uF) where
  admissible : AdmissibleFutures Future
  admissible_nonempty : admissible.Nonempty
  prefers : PreferenceRelation admissible
  preference_preorder : IsPreferencePreorder prefers

namespace TeleologicalContract

variable {Future : Type uF} (C : TeleologicalContract Future)

theorem prefers_refl (x : AdmissibleFuture C.admissible) :
    C.prefers x x :=
  C.preference_preorder.1 x

theorem prefers_trans
    {x y z : AdmissibleFuture C.admissible}
    (hxy : C.prefers x y) (hyz : C.prefers y z) :
    C.prefers x z :=
  C.preference_preorder.2 hxy hyz

/-- Indifference induced by mutual weak preference. -/
def Indifferent
    (x y : AdmissibleFuture C.admissible) : Prop :=
  C.prefers x y ∧ C.prefers y x

theorem indifferent_refl (x : AdmissibleFuture C.admissible) :
    C.Indifferent x x :=
  ⟨C.prefers_refl x, C.prefers_refl x⟩

theorem indifferent_symm
    {x y : AdmissibleFuture C.admissible}
    (h : C.Indifferent x y) :
    C.Indifferent y x :=
  ⟨h.2, h.1⟩

theorem indifferent_trans
    {x y z : AdmissibleFuture C.admissible}
    (hxy : C.Indifferent x y) (hyz : C.Indifferent y z) :
    C.Indifferent x z :=
  ⟨C.prefers_trans hxy.1 hyz.1, C.prefers_trans hyz.2 hxy.2⟩

end TeleologicalContract

end UEOT.V3.Compression.TheoryCompletion
