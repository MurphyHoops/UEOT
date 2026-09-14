import UEOT.V3.RecoveryHittingBound

/-!
# P-REC-03 — first-step hitting-time identities

The frozen Core 3 source defines the canonical recovery potential
`V_A(x) = E_x τ_A` and derives its Poisson equation by first-step analysis and
Markov restart.  This file begins with the purely pathwise half of that
argument.  No Markov property is used here.
-/

namespace UEOT.V3.RecoveryHittingFirstStep

open Finset Function MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open UEOT.V3.RecoveryHittingNonnegative
open scoped ENNReal ProbabilityTheory

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- Drop the initial coordinate of a discrete path. -/
def pathShift (ω : ℕ → X) : ℕ → X :=
  fun n => ω (n + 1)

theorem measurable_pathShift : Measurable (pathShift (X := X)) := by
  apply measurable_pi_iff.mpr
  intro n
  exact measurable_pi_apply (n + 1)

@[simp]
theorem mem_survivalSet_zero_iff
    (A : Set X) (ω : ℕ → X) :
    ω ∈ survivalSet A 0 ↔ ω 0 ∉ A := by
  rw [mem_survivalSet_iff]
  constructor
  · intro h
    exact h 0 le_rfl
  · intro h k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    simpa [hk0] using h

/-- If the initial state is outside the target, surviving through time `n+1`
is exactly surviving through time `n` after deleting the initial coordinate. -/
theorem mem_survivalSet_succ_iff_shift
    (A : Set X) (n : ℕ) (ω : ℕ → X)
    (h0 : ω 0 ∉ A) :
    ω ∈ survivalSet A (n + 1) ↔
      pathShift ω ∈ survivalSet A n := by
  rw [mem_survivalSet_iff, mem_survivalSet_iff]
  constructor
  · intro h k hk
    exact h (k + 1) (Nat.succ_le_succ hk)
  · intro h k hk
    cases k with
    | zero => simpa using h0
    | succ j =>
        have hj : j ≤ n := Nat.le_of_succ_le_succ hk
        simpa [pathShift] using h j hj

/-- The survival indicator shifts by one step when the initial state has not
already hit the target. -/
theorem survivalIndicator_succ_eq_shift
    (A : Set X) (n : ℕ) (ω : ℕ → X)
    (h0 : ω 0 ∉ A) :
    (survivalSet A (n + 1)).indicator (fun _ => (1 : ℝ≥0∞)) ω =
      (survivalSet A n).indicator (fun _ => (1 : ℝ≥0∞)) (pathShift ω) := by
  have hiff := mem_survivalSet_succ_iff_shift A n ω h0
  by_cases h : ω ∈ survivalSet A (n + 1)
  · have hs : pathShift ω ∈ survivalSet A n := hiff.mp h
    simp [h, hs]
  · have hs : pathShift ω ∉ survivalSet A n := by
      intro hs
      exact h (hiff.mpr hs)
    simp [h, hs]

/-- One-step expansion of the pathwise truncated hitting value. -/
theorem truncatedHittingValue_succ
    (A : Set X) (N : ℕ) (ω : ℕ → X) :
    truncatedHittingValue A (N + 1) ω =
      truncatedHittingValue A N ω +
        (survivalSet A N).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  simp [truncatedHittingValue, Finset.sum_range_succ]

/-- Pathwise first-step decomposition for every finite truncation. -/
theorem truncatedHittingValue_succ_eq_one_add_shift
    (A : Set X) (N : ℕ) (ω : ℕ → X)
    (h0 : ω 0 ∉ A) :
    truncatedHittingValue A (N + 1) ω =
      1 + truncatedHittingValue A N (pathShift ω) := by
  induction N with
  | zero =>
      rw [truncatedHittingValue_succ]
      simp [truncatedHittingValue, h0]
  | succ N ih =>
      rw [truncatedHittingValue_succ, ih,
        survivalIndicator_succ_eq_shift A N ω h0, add_assoc,
        ← truncatedHittingValue_succ]

/-- **Pathwise first-step identity.**  If the path starts outside `A`, its
extended hitting time is one plus the hitting time of the shifted path. -/
theorem hittingValue_eq_one_add_shift
    (A : Set X) (ω : ℕ → X)
    (h0 : ω 0 ∉ A) :
    hittingValue A ω = 1 + hittingValue A (pathShift ω) := by
  apply le_antisymm
  · unfold hittingValue
    refine iSup_le ?_
    intro N
    cases N with
    | zero => simp [truncatedHittingValue]
    | succ N =>
        rw [truncatedHittingValue_succ_eq_one_add_shift A N ω h0]
        exact add_le_add le_rfl
          (le_iSup (fun M : ℕ => truncatedHittingValue A M (pathShift ω)) N)
  · unfold hittingValue
    rw [ENNReal.add_iSup]
    refine iSup_le ?_
    intro N
    rw [← truncatedHittingValue_succ_eq_one_add_shift A N ω h0]
    exact le_iSup (fun M : ℕ => truncatedHittingValue A M ω) (N + 1)

/-- Measurability of the extended hitting-time functional. -/
theorem measurable_hittingValue
    {A : Set X} (hA : MeasurableSet A) :
    Measurable (hittingValue A) := by
  unfold hittingValue
  exact Measurable.iSup fun N => measurable_truncatedHittingValue hA N

end UEOT.V3.RecoveryHittingFirstStep
