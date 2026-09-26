/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
Modified for UEOT Core v3 integration in 2026: module import paths and a proof
adaptation of `map_horizonMeasure_reverse` for the pinned Mathlib API; its
statement and the surrounding path-space definitions are unchanged.
-/
import UEOT.V3.ThirdParty.CrooksJarzynski.ContinuousTimeJumpFull
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Fixed-horizon continuous-time jump paths

A fixed-jump-count path belongs to the horizon-`T` sector when its holding
intervals sum to `T`.  This condition is measurable and invariant under path
reversal.  Consequently a Crooks relation can be restricted to the horizon
sector, and the restricted sector relations can then be summed over all jump
counts by `FullPath.crooks_of_sector_relations`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace JumpPath

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

/-- Total elapsed time represented by all holding intervals of a jump path. -/
def totalHoldingTime (γ : JumpPath Ω n) : NNReal :=
  ∑ i, γ.2 i

/-- The total holding time is a measurable path observable. -/
@[fun_prop]
theorem measurable_totalHoldingTime :
    Measurable (totalHoldingTime (Ω := Ω) (n := n)) := by
  unfold totalHoldingTime
  fun_prop

omit [MeasurableSpace Ω] in
/-- Reversing a jump path preserves its total elapsed time. -/
@[simp]
theorem totalHoldingTime_reverse (γ : JumpPath Ω n) :
    totalHoldingTime (reverse γ) = totalHoldingTime γ := by
  unfold totalHoldingTime reverse
  let e : Fin (n + 1) ≃ Fin (n + 1) :=
    { toFun := Fin.rev
      invFun := Fin.rev
      left_inv := Fin.rev_involutive
      right_inv := Fin.rev_involutive }
  exact Fintype.sum_equiv e
    (fun i => γ.2 i.rev) (fun i => γ.2 i) (fun _ => rfl)

/-- The measurable set of paths whose holding intervals fill the horizon `T`. -/
def horizonSet (T : NNReal) : Set (JumpPath Ω n) :=
  {γ | totalHoldingTime γ = T}

/-- The fixed-horizon sector is measurable. -/
theorem measurableSet_horizonSet (T : NNReal) :
    MeasurableSet (horizonSet (Ω := Ω) (n := n) T) := by
  simpa [horizonSet] using
    (measurable_totalHoldingTime (Ω := Ω) (n := n)).eq_const T |>.setOf

omit [MeasurableSpace Ω] in
/-- The horizon sector is invariant under path reversal. -/
@[simp]
theorem preimage_horizonSet_reverse (T : NNReal) :
    reverse ⁻¹' horizonSet (Ω := Ω) (n := n) T =
      horizonSet (Ω := Ω) (n := n) T := by
  ext γ
  simp [horizonSet]

/-- Path reversal packaged as a measurable equivalence. -/
noncomputable def reverseEquiv : JumpPath Ω n ≃ᵐ JumpPath Ω n where
  toEquiv :=
    { toFun := reverse
      invFun := reverse
      left_inv := reverse_involutive
      right_inv := reverse_involutive }
  measurable_toFun := measurable_reverse
  measurable_invFun := measurable_reverse

/-- Restrict a path measure to trajectories with total duration `T`. -/
noncomputable def horizonMeasure (T : NNReal)
    (μ : Measure (JumpPath Ω n)) : Measure (JumpPath Ω n) :=
  μ.restrict (horizonSet T)

/-- The mass of a horizon-restricted measure is the mass of its horizon sector. -/
theorem horizonMeasure_univ (T : NNReal) (μ : Measure (JumpPath Ω n)) :
    horizonMeasure T μ Set.univ = μ (horizonSet T) := by
  simp [horizonMeasure]

/-- A probability measure concentrated on the horizon remains a probability
measure after explicit restriction to that horizon. -/
theorem isProbabilityMeasure_horizonMeasure
    (T : NNReal) (μ : Measure (JumpPath Ω n)) [IsProbabilityMeasure μ]
    (hμ : μ (horizonSet T) = 1) :
    IsProbabilityMeasure (horizonMeasure T μ) := by
  constructor
  rw [horizonMeasure_univ]
  exact hμ

/-- Restricting a reversal-invariant reference measure to a fixed horizon
preserves reversal invariance. -/
theorem map_horizonMeasure_reverse
    (T : NNReal) (μ : Measure (JumpPath Ω n))
    (hμ : μ.map reverse = μ) :
    (horizonMeasure T μ).map reverse = horizonMeasure T μ := by
  let e := reverseEquiv (Ω := Ω) (n := n)
  let S := horizonSet (Ω := Ω) (n := n) T
  have h := e.restrict_map μ S
  have hefun : (e : JumpPath Ω n → JumpPath Ω n) = reverse := rfl
  have hmap : μ.map e = μ := by
    rw [hefun]
    exact hμ
  have hpre : e ⁻¹' S = S := by
    rw [hefun]
    exact preimage_horizonSet_reverse T
  rw [hmap, hpre] at h
  change (μ.restrict S).map reverse = μ.restrict S
  rw [← hefun]
  exact h.symm

/-- A Crooks relation remains valid after both path laws are restricted to the
same measurable horizon sector. -/
theorem crooks_restrict_horizon
    (T : NNReal) (forward reverseMeasure : Measure (JumpPath Ω n))
    (workWeight : JumpPath Ω n → ℝ≥0∞) (freeEnergyWeight : ℝ≥0∞)
    (h : CrooksRelation forward reverseMeasure workWeight freeEnergyWeight) :
    CrooksRelation (horizonMeasure T forward)
      (horizonMeasure T reverseMeasure) workWeight freeEnergyWeight := by
  unfold CrooksRelation at h ⊢
  let S := horizonSet (Ω := Ω) (n := n) T
  change (forward.restrict S).withDensity workWeight =
    freeEnergyWeight • reverseMeasure.restrict S
  have hS : MeasurableSet S := measurableSet_horizonSet T
  calc
    (forward.restrict S).withDensity workWeight =
        (forward.withDensity workWeight).restrict S :=
      (MeasureTheory.restrict_withDensity hS workWeight).symm
    _ = (freeEnergyWeight • reverseMeasure).restrict S := by rw [h]
    _ = freeEnergyWeight • reverseMeasure.restrict S := by simp

end JumpPath

namespace FullPath

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Sectorwise Crooks relations can first be restricted to a common physical
horizon and then summed over every finite jump count. -/
theorem crooks_restrict_horizon_of_sector_relations
    (T : NNReal)
    (forward reverseMeasure : (n : ℕ) → Measure (JumpPath Ω n))
    (workWeight : (n : ℕ) → JumpPath Ω n → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hwork : ∀ n, Measurable (workWeight n))
    (hsector : ∀ n,
      CrooksRelation (forward n) (reverseMeasure n)
        (workWeight n) freeEnergyWeight) :
    CrooksRelation
      (measure fun n => JumpPath.horizonMeasure T (forward n))
      (measure fun n => JumpPath.horizonMeasure T (reverseMeasure n))
      (weight workWeight) freeEnergyWeight := by
  apply crooks_of_sector_relations
    (fun n => JumpPath.horizonMeasure T (forward n))
    (fun n => JumpPath.horizonMeasure T (reverseMeasure n))
    workWeight freeEnergyWeight hwork
  intro n
  exact JumpPath.crooks_restrict_horizon T
    (forward n) (reverseMeasure n) (workWeight n) freeEnergyWeight
    (hsector n)

/-- Jarzynski's equality for the complete path law after restriction to a fixed
horizon. -/
theorem jarzynski_restrict_horizon_of_sector_relations
    (T : NNReal)
    (forward reverseMeasure : (n : ℕ) → Measure (JumpPath Ω n))
    (workWeight : (n : ℕ) → JumpPath Ω n → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    [IsProbabilityMeasure
      (measure fun n => JumpPath.horizonMeasure T (reverseMeasure n))]
    (hwork : ∀ n, Measurable (workWeight n))
    (hsector : ∀ n,
      CrooksRelation (forward n) (reverseMeasure n)
        (workWeight n) freeEnergyWeight) :
    ∫⁻ γ, weight workWeight γ
        ∂(measure fun n => JumpPath.horizonMeasure T (forward n)) =
      freeEnergyWeight :=
  jarzynski_lintegral _ _ _ _
    (crooks_restrict_horizon_of_sector_relations T forward reverseMeasure
      workWeight freeEnergyWeight hwork hsector)

end FullPath
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
