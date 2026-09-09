import Mathlib.Data.EReal.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# P-REF-05 — monotonicity under feasible policy-set expansion

The source uses a real-valued evaluation J and policy sets Π₁ ⊆ Π₂.
To make the supremum total without silently assuming nonempty/bounded policy
sets, real rewards are embedded in EReal.  For ordinary nonempty bounded
problems this is the usual real supremum; the monotonicity theorem itself needs
no extra side conditions.
-/

namespace UEOT.V3.Agency

universe uP

open Set

variable {P : Type uP}

noncomputable def feasibleValue (J : P → ℝ) (S : Set P) : EReal :=
  ⨆ p : S, (J p.1 : EReal)

theorem feasibleValue_mono
    (J : P → ℝ) {S T : Set P} (hST : S ⊆ T) :
    feasibleValue J S ≤ feasibleValue J T := by
  unfold feasibleValue
  refine iSup_le ?_
  intro p
  exact le_iSup_of_le ⟨p.1, hST p.2⟩ le_rfl


noncomputable def feasibleValueReal (J : P → ℝ) (S : Set P) : ℝ :=
  sSup (J '' S)

theorem feasibleValueReal_mono
    (J : P → ℝ) {S T : Set P}
    (hS : S.Nonempty)
    (hT : BddAbove (J '' T))
    (hST : S ⊆ T) :
    feasibleValueReal J S ≤ feasibleValueReal J T := by
  unfold feasibleValueReal
  exact csSup_le_csSup hT (hS.image J) (Set.image_mono hST)

structure FeasibleDecision (P : Type uP) where
  feasible : Set P
  value : P → ℝ

def Extends (D₁ D₂ : FeasibleDecision P) : Prop :=
  D₁.value = D₂.value ∧ D₁.feasible ⊆ D₂.feasible

noncomputable def optimalValue (D : FeasibleDecision P) : EReal :=
  feasibleValue D.value D.feasible

theorem extension_optimalValue_mono
    {D₁ D₂ : FeasibleDecision P} (h : Extends D₁ D₂) :
    optimalValue D₁ ≤ optimalValue D₂ := by
  rcases h with ⟨hJ, hS⟩
  unfold optimalValue
  rw [hJ]
  exact feasibleValue_mono D₂.value hS

end UEOT.V3.Agency
