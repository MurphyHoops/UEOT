/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
Modified for UEOT Core v3 integration in 2026: module import paths only.
-/
import UEOT.V3.ThirdParty.CrooksJarzynski.ContinuousTimeJump
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Full continuous-time jump path laws

This module assembles the fixed-jump-count path laws from
`ContinuousTimeJump` into one measure on the dependent sum of all jump-count
sectors.  A sectorwise Crooks relation with a common free-energy factor then
sums to a Crooks relation for the full continuous-time path law.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

/-- The disjoint union of all finite-jump path sectors. -/
abbrev FullPath (Ω : Type u) := Σ n : ℕ, JumpPath Ω n

namespace FullPath

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Inject one fixed-jump-count sector into the full path space. -/
@[fun_prop]
theorem measurable_mk (n : ℕ) :
    Measurable (Sigma.mk n : JumpPath Ω n → FullPath Ω) := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mp hs n

/-- Lift a measure on the `n`-jump sector to the full path space. -/
noncomputable def liftMeasure (n : ℕ) (μ : Measure (JumpPath Ω n)) :
    Measure (FullPath Ω) :=
  μ.map (Sigma.mk n)

/-- Sum all fixed-jump-count sectors into one path law. -/
noncomputable def measure
    (μ : (n : ℕ) → Measure (JumpPath Ω n)) : Measure (FullPath Ω) :=
  Measure.sum fun n => liftMeasure n (μ n)

/-- Assemble sectorwise observables into an observable on the full path space. -/
def weight (q : (n : ℕ) → JumpPath Ω n → ℝ≥0∞) : FullPath Ω → ℝ≥0∞
  | ⟨n, γ⟩ => q n γ

/-- A sectorwise measurable observable is measurable on the dependent sum. -/
theorem measurable_weight
    (q : (n : ℕ) → JumpPath Ω n → ℝ≥0∞)
    (hq : ∀ n, Measurable (q n)) : Measurable (weight q) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet ((q n) ⁻¹' s)
  exact hq n hs

/-- Lifting a sector measure commutes with reweighting by a sectorwise density. -/
theorem liftMeasure_withDensity
    (n : ℕ) (μ : Measure (JumpPath Ω n))
    (q : (m : ℕ) → JumpPath Ω m → ℝ≥0∞)
    (hq : ∀ m, Measurable (q m)) :
    (liftMeasure n μ).withDensity (weight q) =
      liftMeasure n (μ.withDensity (q n)) := by
  simpa [liftMeasure, weight, Function.comp_def] using
    (CrooksJarzynski.MeasureProtocol.map_withDensity
      μ (Sigma.mk n) (weight q) (measurable_mk n)
      (measurable_weight q hq))

/-- Lifting a sector measure commutes with scalar multiplication. -/
theorem liftMeasure_smul
    (n : ℕ) (c : ℝ≥0∞) (μ : Measure (JumpPath Ω n)) :
    liftMeasure n (c • μ) = c • liftMeasure n μ := by
  simp [liftMeasure, Measure.map_smul]

/-- The mass of the full path law is the sum of the sector masses. -/
theorem measure_univ
    (μ : (n : ℕ) → Measure (JumpPath Ω n)) :
    measure μ Set.univ = ∑' n, μ n Set.univ := by
  rw [measure, Measure.sum_apply _ MeasurableSet.univ]
  apply tsum_congr
  intro n
  simp [liftMeasure, measurable_mk]

/-- Sector masses summing to one make the full path law a probability measure. -/
theorem isProbabilityMeasure_measure
    (μ : (n : ℕ) → Measure (JumpPath Ω n))
    (hmass : ∑' n, μ n Set.univ = 1) :
    IsProbabilityMeasure (measure μ) := by
  constructor
  rw [measure_univ]
  exact hmass

/-- Sectorwise Crooks relations with a common equilibrium factor sum to a
Crooks relation for the complete finite-jump path law. -/
theorem crooks_of_sector_relations
    (forward reverse : (n : ℕ) → Measure (JumpPath Ω n))
    (workWeight : (n : ℕ) → JumpPath Ω n → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hwork : ∀ n, Measurable (workWeight n))
    (hsector : ∀ n,
      CrooksRelation (forward n) (reverse n)
        (workWeight n) freeEnergyWeight) :
    CrooksRelation (measure forward) (measure reverse)
      (weight workWeight) freeEnergyWeight := by
  unfold CrooksRelation at hsector ⊢
  calc
    (measure forward).withDensity (weight workWeight) =
        Measure.sum fun n =>
          (liftMeasure n (forward n)).withDensity (weight workWeight) :=
      MeasureTheory.withDensity_sum _ _
    _ = Measure.sum fun n =>
          liftMeasure n ((forward n).withDensity (workWeight n)) := by
      congr 1
      funext n
      exact liftMeasure_withDensity n (forward n) workWeight hwork
    _ = Measure.sum fun n =>
          liftMeasure n (freeEnergyWeight • reverse n) := by
      congr 1
      funext n
      rw [hsector n]
    _ = Measure.sum fun n =>
          freeEnergyWeight • liftMeasure n (reverse n) := by
      congr 1
      funext n
      exact liftMeasure_smul n freeEnergyWeight (reverse n)
    _ = freeEnergyWeight • measure reverse := by
      ext s hs
      simpa [measure, hs] using
        (ENNReal.tsum_mul_left
          (α := ℕ)
          (a := freeEnergyWeight)
          (f := fun i => (liftMeasure i (reverse i)) s))

/-- Jarzynski's equality for the complete finite-jump path law. -/
theorem jarzynski_of_sector_relations
    (forward reverse : (n : ℕ) → Measure (JumpPath Ω n))
    (workWeight : (n : ℕ) → JumpPath Ω n → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    [IsProbabilityMeasure (measure reverse)]
    (hwork : ∀ n, Measurable (workWeight n))
    (hsector : ∀ n,
      CrooksRelation (forward n) (reverse n)
        (workWeight n) freeEnergyWeight) :
    ∫⁻ γ, weight workWeight γ ∂(measure forward) = freeEnergyWeight :=
  jarzynski_lintegral _ _ _ _
    (crooks_of_sector_relations forward reverse workWeight
      freeEnergyWeight hwork hsector)

/-- Real-valued full-path Jarzynski equality for a finite common
free-energy weight. -/
theorem jarzynski_toReal_of_sector_relations
    (forward reverse : (n : ℕ) → Measure (JumpPath Ω n))
    (workWeight : (n : ℕ) → JumpPath Ω n → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    [IsProbabilityMeasure (measure reverse)]
    (hwork : ∀ n, Measurable (workWeight n))
    (hfreeEnergy : freeEnergyWeight ≠ ∞)
    (hsector : ∀ n,
      CrooksRelation (forward n) (reverse n)
        (workWeight n) freeEnergyWeight) :
    ∫ γ, (weight workWeight γ).toReal ∂(measure forward) =
      freeEnergyWeight.toReal :=
  jarzynski_toReal_integral _ _ _ _ (measurable_weight workWeight hwork)
    hfreeEnergy
    (crooks_of_sector_relations forward reverse workWeight
      freeEnergyWeight hwork hsector)

end FullPath
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
