import UEOT.Core.Reward
import Mathlib.Order.CompleteLattice.Basic

/-! Exact decision inequalities from the v3.0 specification. -/
namespace UEOT.V3.Decision

theorem action_gap {A : Type*} (q estimate : A → ℝ) (η : ℝ) (best : A)
    (err : ∀ a, |q a - estimate a| ≤ η)
    (gap : ∀ a, a ≠ best → 2 * η < estimate best - estimate a) :
    ∀ a, a ≠ best → q a < q best := by
  intro a ha
  have h₁ := (abs_le.mp (err a)).2
  have h₂ := (abs_le.mp (err best)).1
  have h₃ := gap a ha
  linarith

theorem goal_regret {P : Type*} (J estimate : P → ℝ) (ε : ℝ)
    (err : ∀ p, |J p - estimate p| ≤ ε) (chosen : P)
    (optimal : Reward.IsMaximizer estimate chosen) (competitor : P) :
    J competitor - J chosen ≤ 2 * ε := by
  have h₁ := (abs_le.mp (err competitor)).2
  have h₂ := (abs_le.mp (err chosen)).1
  have h₃ := optimal competitor
  linarith

theorem feasible_sup_mono {P R : Type*} [CompleteLattice R]
    (J : P → R) (S T : Set P) (h : S ⊆ T) :
    (⨆ p ∈ S, J p) ≤ ⨆ p ∈ T, J p := by
  apply iSup₂_le
  intro p hp
  exact le_iSup_of_le p (le_iSup_of_le (h hp) le_rfl)

theorem replication_factors {P Q : Type*} (response : P → Q) (replicate : Q → ℝ)
    {a b : P} (h : response a = response b) :
    replicate (response a) = replicate (response b) := congrArg replicate h

end UEOT.V3.Decision
