import UEOT.V3.InformationPinsker
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# P-INFO-02 foundation — measurable pointwise total variation for Markov kernels

The frozen P-INFO-02 theorem contains an expectation of

`x ↦ D_TV(κ x, η x)`.

UEOT already has one canonical, real-valued event-supremum distance
`UEOT.V3.TotalVariation.tvDist`.  This module does **not** introduce a second
public TV distance.  Instead it proves a density representation for the
existing definition and then derives measurability of pointwise kernel TV on a
countably generated target.

The kernel-measurability route is adapted from the Apache-2.0 proof in
`StatLean/Bayesian/ForMathlib/TVDist.lean` (StatLean, 2026): use the jointly
measurable `Kernel.rnDerivAux` densities of `κ` and `η` with respect to `κ+η`,
identify TV with the positive-part density integral, and use
`Measurable.lintegral_kernel_prod_right`.
-/

namespace UEOT.V3.InformationKernelTV

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.TotalVariation

universe uX uY

variable {X : Type uX} {Y : Type uY}
variable [MeasurableSpace X] [MeasurableSpace Y]

/-- One-sided event gap is bounded by the positive-part density integral. -/
private theorem measureReal_sub_le_toReal_lintegral_tsub
    (base : Measure Y) {p q : Y → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable q)
    [IsProbabilityMeasure (base.withDensity p)]
    [IsProbabilityMeasure (base.withDensity q)]
    {A : Set Y} (hA : MeasurableSet A) :
    (base.withDensity p).real A - (base.withDensity q).real A ≤
      (∫⁻ y, p y - q y ∂base).toReal := by
  let μ := base.withDensity p
  let ν := base.withDensity q
  let L : ℝ≥0∞ := ∫⁻ y, p y - q y ∂base
  have hpint : ∫⁻ y, p y ∂base = 1 := by
    have h : ∫⁻ y, p y ∂base = μ Set.univ := by
      dsimp [μ]
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [h]
    exact measure_univ
  have hLle : L ≤ ∫⁻ y, p y ∂base := by
    dsimp [L]
    exact lintegral_mono fun y => tsub_le_self
  have hpTop : (∫⁻ y, p y ∂base) ≠ ∞ := by
    rw [hpint]
    exact ENNReal.one_ne_top
  have hLtop : L ≠ ∞ :=
    ne_top_of_le_ne_top hpTop hLle
  have hENN : μ A - ν A ≤ L := by
    dsimp [μ, ν, L]
    rw [withDensity_apply _ hA, withDensity_apply _ hA]
    calc
      (∫⁻ y in A, p y ∂base) - ∫⁻ y in A, q y ∂base
          ≤ ∫⁻ y in A, (p y - q y) ∂base :=
        lintegral_sub_le _ _ hq
      _ ≤ ∫⁻ y, (p y - q y) ∂base :=
        lintegral_mono' Measure.restrict_le_self le_rfl
  by_cases hμν : μ A ≤ ν A
  · have hreal : μ.real A ≤ ν.real A := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top ν A) hμν
    have hnonpos : μ.real A - ν.real A ≤ 0 := sub_nonpos.mpr hreal
    exact hnonpos.trans ENNReal.toReal_nonneg
  · have hνμ : ν A ≤ μ A := le_of_not_ge hμν
    have hsub : (μ A - ν A).toReal = μ.real A - ν.real A := by
      rw [ENNReal.toReal_sub_of_le hνμ (measure_ne_top μ A)]
      rfl
    rw [← hsub]
    exact ENNReal.toReal_mono hLtop hENN

/-- For probability densities `p,q` over a common base measure, UEOT's
real-valued event-supremum TV equals the real value of the positive-part density
integral `∫⁻ (p-q)`. -/
theorem tvDist_withDensity_eq_toReal_lintegral_tsub
    (base : Measure Y) {p q : Y → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable q)
    [IsProbabilityMeasure (base.withDensity p)]
    [IsProbabilityMeasure (base.withDensity q)] :
    tvDist (base.withDensity p) (base.withDensity q) =
      (∫⁻ y, p y - q y ∂base).toReal := by
  let μ := base.withDensity p
  let ν := base.withDensity q
  let L : ℝ≥0∞ := ∫⁻ y, p y - q y ∂base
  have hpint : ∫⁻ y, p y ∂base = 1 := by
    have h : ∫⁻ y, p y ∂base = μ Set.univ := by
      dsimp [μ]
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [h]
    exact measure_univ
  have hLle : L ≤ ∫⁻ y, p y ∂base := by
    dsimp [L]
    exact lintegral_mono fun y => tsub_le_self
  have hLtop : L ≠ ∞ := by
    have hpTop : (∫⁻ y, p y ∂base) ≠ ∞ := by
      rw [hpint]
      exact ENNReal.one_ne_top
    exact ne_top_of_le_ne_top hpTop hLle
  have hupper : tvDist μ ν ≤ L.toReal := by
    unfold tvDist
    refine csSup_le (tvEventSet_nonempty μ ν) ?_
    intro r hr
    rcases hr with ⟨A, hA, rfl⟩
    have hpos :=
      measureReal_sub_le_toReal_lintegral_tsub base hp hq (A := A) hA
    have hcomp :=
      measureReal_sub_le_toReal_lintegral_tsub base hp hq (A := Aᶜ) hA.compl
    have hflip : ν.real A - μ.real A = μ.real Aᶜ - ν.real Aᶜ := by
      rw [measureReal_compl hA, measureReal_compl hA,
        probReal_univ, probReal_univ]
      ring
    rw [← hflip] at hcomp
    rw [abs_le]
    constructor <;> linarith
  have hlower : L.toReal ≤ tvDist μ ν := by
    let A : Set Y := {y | q y ≤ p y}
    have hA : MeasurableSet A := measurableSet_le hq hp
    have hqA : ∫⁻ y in A, q y ∂base ≠ ∞ := by
      have hqint : ∫⁻ y, q y ∂base = 1 := by
        have h : ∫⁻ y, q y ∂base = ν Set.univ := by
          dsimp [ν]
          rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        rw [h]
        exact measure_univ
      exact ne_top_of_le_ne_top (by rw [hqint]; exact ENNReal.one_ne_top)
        (lintegral_mono' Measure.restrict_le_self le_rfl)
    have hle : q ≤ᵐ[base.restrict A] p :=
      ae_restrict_of_forall_mem hA fun y hy => hy
    have hcompl : ∫⁻ y in Aᶜ, (p y - q y) ∂base = 0 := by
      refine setLIntegral_eq_zero hA.compl (fun y hy => ?_)
      simp only [A, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hy
      exact tsub_eq_zero_of_le hy.le
    have hLeq : L = μ A - ν A := by
      dsimp [L, μ, ν]
      rw [← lintegral_add_compl _ hA, hcompl, add_zero,
        lintegral_sub hq hqA hle,
        withDensity_apply _ hA, withDensity_apply _ hA]
    have hνμ : ν A ≤ μ A := by
      dsimp [μ, ν]
      rw [withDensity_apply _ hA, withDensity_apply _ hA]
      exact lintegral_mono_ae hle
    have hreal : L.toReal = μ.real A - ν.real A := by
      rw [hLeq, ENNReal.toReal_sub_of_le hνμ (measure_ne_top μ A)]
      rfl
    have hgap0 : 0 ≤ μ.real A - ν.real A := by
      rw [measureReal_def, measureReal_def]
      exact sub_nonneg.mpr (ENNReal.toReal_mono (measure_ne_top μ A) hνμ)
    have htv := tvEvent_le μ ν A hA
    rw [abs_of_nonneg hgap0, ← hreal] at htv
    exact htv
  exact le_antisymm hupper hlower

/-- Pointwise TV between two Markov kernels is measurable when the target
σ-algebra is countably generated. -/
theorem measurable_tvDist_kernel
    [MeasurableSpace.CountablyGenerated Y]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η] :
    Measurable fun x => tvDist (κ x) (η x) := by
  classical
  set F : X → Y → ℝ≥0∞ :=
    fun x y => ENNReal.ofReal (Kernel.rnDerivAux κ (κ + η) x y) with hF
  set G : X → Y → ℝ≥0∞ :=
    fun x y => ENNReal.ofReal (Kernel.rnDerivAux η (κ + η) x y) with hG
  have hFκ : ∀ x, ((κ + η) x).withDensity (F x) = κ x := by
    intro x
    ext s hs
    rw [withDensity_apply _ hs]
    exact Kernel.setLIntegral_rnDerivAux κ η x hs
  have hGη : ∀ x, ((κ + η) x).withDensity (G x) = η x := by
    intro x
    ext s hs
    rw [withDensity_apply _ hs]
    have h := Kernel.setLIntegral_rnDerivAux η κ x hs
    rw [add_comm η κ] at h
    exact h
  have hFm : ∀ x, Measurable (F x) := fun x =>
    (Kernel.measurable_rnDerivAux_right κ (κ + η) x).ennreal_ofReal
  have hGm : ∀ x, Measurable (G x) := fun x =>
    (Kernel.measurable_rnDerivAux_right η (κ + η) x).ennreal_ofReal
  have heq : ∀ x, tvDist (κ x) (η x) =
      (∫⁻ y, F x y - G x y ∂((κ + η) x)).toReal := by
    intro x
    letI : IsProbabilityMeasure (((κ + η) x).withDensity (F x)) := by
      rw [hFκ x]
      infer_instance
    letI : IsProbabilityMeasure (((κ + η) x).withDensity (G x)) := by
      rw [hGη x]
      infer_instance
    conv_lhs => rw [← hFκ x, ← hGη x]
    exact tvDist_withDensity_eq_toReal_lintegral_tsub ((κ + η) x) (hFm x) (hGm x)
  simp_rw [heq]
  have hlin : Measurable fun x => ∫⁻ y, F x y - G x y ∂((κ + η) x) := by
    refine Measurable.lintegral_kernel_prod_right (κ := κ + η) ?_
    exact ((Kernel.measurable_rnDerivAux κ (κ + η)).ennreal_ofReal).sub
      ((Kernel.measurable_rnDerivAux η (κ + η)).ennreal_ofReal)
  exact hlin.ennreal_toReal

end UEOT.V3.InformationKernelTV
