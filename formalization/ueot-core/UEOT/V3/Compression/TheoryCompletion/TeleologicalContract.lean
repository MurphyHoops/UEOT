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

end UEOT.V3.Compression.TheoryCompletion
