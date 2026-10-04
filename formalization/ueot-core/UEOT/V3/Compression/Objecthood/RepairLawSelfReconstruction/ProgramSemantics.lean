import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.InternalProgramState
import UEOT.V3.Compression.Objecthood.ControllerRepair

/-!
# RLSR2 — behavioral repair-program validity and identity

Program identity is operational rather than syntactic.  A program is valid when
its trusted execution preserves the declared object carrier.  Two programs are
equivalent when they select the same actions on that carrier; validity therefore
transports across the equivalence class.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

open Set
open UEOT.V3.Compression.Objecthood

universe uX uA uP

variable {X : Type uX} {A : Type uA} {Program : Type uP}

/-- Behavioral validity of an executable repair program relative to one object
carrier. -/
def RepairProgramValid
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    (r : Program) : Prop :=
  PreservingController P K (T.execute r)

/-- Carrier-relative behavioral identity of repair programs.  Code equality is
not required. -/
def RepairProgramEquivalentOn
    (T : TrustedRepairSubstrate Program X A)
    (K : Set X) (r₁ r₂ : Program) : Prop :=
  ∀ x ∈ K, T.execute r₁ x = T.execute r₂ x

/-- Exact behavioral implementation of a supplied policy.  This relation is
used later only to tie a reconstructed program to an independently certified
same-parent repair policy; it is not part of the trusted substrate. -/
def RepairProgramImplementsPolicy
    (T : TrustedRepairSubstrate Program X A)
    (r : Program) (pi : X → A) : Prop :=
  ∀ x, T.execute r x = pi x

@[refl] theorem repairProgramEquivalentOn_refl
    (T : TrustedRepairSubstrate Program X A)
    (K : Set X) (r : Program) :
    RepairProgramEquivalentOn T K r r := by
  intro x hx
  rfl

@[symm] theorem repairProgramEquivalentOn_symm
    (T : TrustedRepairSubstrate Program X A)
    (K : Set X) {r₁ r₂ : Program}
    (h : RepairProgramEquivalentOn T K r₁ r₂) :
    RepairProgramEquivalentOn T K r₂ r₁ := by
  intro x hx
  exact (h x hx).symm

@[trans] theorem repairProgramEquivalentOn_trans
    (T : TrustedRepairSubstrate Program X A)
    (K : Set X) {r₁ r₂ r₃ : Program}
    (h₁₂ : RepairProgramEquivalentOn T K r₁ r₂)
    (h₂₃ : RepairProgramEquivalentOn T K r₂ r₃) :
    RepairProgramEquivalentOn T K r₁ r₃ := by
  intro x hx
  exact (h₁₂ x hx).trans (h₂₃ x hx)

/-- Preserving validity depends only on carrier behavior, not program syntax. -/
theorem repairProgramValid_of_equivalent
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    {r₁ r₂ : Program}
    (hvalid : RepairProgramValid T P K r₁)
    (heq : RepairProgramEquivalentOn T K r₁ r₂) :
    RepairProgramValid T P K r₂ := by
  intro x hx y hy
  rw [← heq x hx] at hy
  exact hvalid x hx hy

/-- Equivalent programs are valid simultaneously. -/
theorem repairProgramValid_iff_of_equivalent
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    {r₁ r₂ : Program}
    (heq : RepairProgramEquivalentOn T K r₁ r₂) :
    RepairProgramValid T P K r₁ ↔ RepairProgramValid T P K r₂ := by
  constructor
  · intro h
    exact repairProgramValid_of_equivalent T P K h heq
  · intro h
    exact repairProgramValid_of_equivalent T P K h
      (repairProgramEquivalentOn_symm T K heq)

/-- Global policy implementation implies carrier-relative program equivalence
whenever two programs implement the same policy. -/
theorem repairProgramEquivalentOn_of_implements_same_policy
    (T : TrustedRepairSubstrate Program X A)
    (K : Set X) {r₁ r₂ : Program} {pi : X → A}
    (h₁ : RepairProgramImplementsPolicy T r₁ pi)
    (h₂ : RepairProgramImplementsPolicy T r₂ pi) :
    RepairProgramEquivalentOn T K r₁ r₂ := by
  intro x hx
  exact (h₁ x).trans (h₂ x).symm

end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
