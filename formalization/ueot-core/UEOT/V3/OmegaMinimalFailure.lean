import UEOT.Core.Finite

/-!
# P-OMG-01 — minimal destructive-set reconstruction

The frozen Core 3 source assumes a finite mechanism/deletion model with a
monotone failure predicate: once a deletion set fails the object certificate,
any larger deletion set also fails.  The entire failure family is therefore the
upward closure of its inclusion-minimal failures.

This source-facing layer is intentionally generic in the failure predicate.
The manuscript's Boolean certificate clause `χ(D)=0` is represented by
`Failure D`.
-/

namespace UEOT.V3.OmegaMinimalFailure

universe u
variable {V : Type u}

/-- Failure is monotone under adding further deleted mechanisms. -/
def FailureMonotone (Failure : Finset V → Prop) : Prop :=
  ∀ ⦃D D' : Finset V⦄, D ⊆ D' → Failure D → Failure D'

/-- The clutter of inclusion-minimal destructive deletion sets. -/
def minimalFailures (Failure : Finset V → Prop) : Set (Finset V) :=
  {C | UEOT.Finite.Minimal Failure C}

/-- Source-facing P-OMG-01.

For a monotone finite-deletion failure predicate, a deletion set fails iff it
contains an inclusion-minimal failing deletion set.  The forward implication is
the finite minimal-subset argument; the reverse implication is exactly failure
monotonicity. -/
theorem p_omg_01
    (Failure : Finset V → Prop)
    (hmono : FailureMonotone Failure)
    (D : Finset V) :
    Failure D ↔ ∃ C, C ∈ minimalFailures Failure ∧ C ⊆ D := by
  constructor
  · intro hD
    obtain ⟨C, hCD, hC⟩ :=
      UEOT.Finite.exists_minimal_subset Failure D hD
    exact ⟨C, hC, hCD⟩
  · rintro ⟨C, hC, hCD⟩
    exact hmono hCD hC.1

end UEOT.V3.OmegaMinimalFailure
