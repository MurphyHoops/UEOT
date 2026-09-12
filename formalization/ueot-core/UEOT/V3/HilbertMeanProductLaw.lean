import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# P-STAT-06 — canonical product-law transport

McDiarmid's bounded-difference argument is cleanest on the canonical finite
product of the sample marginals. For an arbitrary independent sample family,
Mathlib's `iIndepFun.map_fun_eq_pi_map` identifies the law of the full sample
vector with exactly that product measure. This file packages the identification
and the two transports needed by the source proof: measurable tail events and
Bochner expectations.
-/

namespace UEOT.V3.HilbertMeanProductLaw

open MeasureTheory ProbabilityTheory

universe uΩ uH

variable {Ω : Type uΩ} {H : Type uH}
variable [MeasurableSpace Ω] [MeasurableSpace H]

/-- The full finite sample vector associated with a family `Z i`. -/
def sampleVector {N : ℕ} (Z : Fin N → Ω → H) (ω : Ω) : Fin N → H :=
  fun i => Z i ω

@[simp]
theorem sampleVector_apply {N : ℕ} (Z : Fin N → Ω → H) (ω : Ω) (i : Fin N) :
    sampleVector Z ω i = Z i ω := rfl

/-- Independence identifies the joint sample law with the product of the
coordinate marginals. -/
theorem map_sampleVector_eq_pi_marginals
    {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin N → Ω → H)
    (hZ : ∀ i, AEMeasurable (Z i) μ)
    (hindep : iIndepFun Z μ) :
    μ.map (sampleVector Z) = Measure.pi (fun i => μ.map (Z i)) := by
  exact hindep.map_fun_eq_pi_map hZ

/-- Every measurable event of the full sample vector has exactly the same
probability on the original space and on the canonical product space. -/
theorem measure_preimage_eq_pi_marginals
    {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin N → Ω → H)
    (hZ : ∀ i, AEMeasurable (Z i) μ)
    (hindep : iIndepFun Z μ)
    (A : Set (Fin N → H)) (hA : MeasurableSet A) :
    μ (sampleVector Z ⁻¹' A) = Measure.pi (fun i => μ.map (Z i)) A := by
  have hvec : AEMeasurable (sampleVector Z) μ :=
    aemeasurable_pi_lambda (sampleVector Z) hZ
  calc
    μ (sampleVector Z ⁻¹' A) = μ.map (sampleVector Z) A :=
      (Measure.map_apply_of_aemeasurable hvec hA).symm
    _ = Measure.pi (fun i => μ.map (Z i)) A := by
      rw [map_sampleVector_eq_pi_marginals μ Z hZ hindep]

/-- Scalar upper-tail events transport exactly to the product law. -/
theorem measure_ge_statistic_eq_pi_marginals
    {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin N → Ω → H)
    (hZ : ∀ i, AEMeasurable (Z i) μ)
    (hindep : iIndepFun Z μ)
    (F : (Fin N → H) → ℝ) (hF : Measurable F) (r : ℝ) :
    μ {ω | r ≤ F (sampleVector Z ω)} =
      Measure.pi (fun i => μ.map (Z i)) {x | r ≤ F x} := by
  have hA : MeasurableSet {x | r ≤ F x} :=
    measurableSet_le measurable_const hF
  change μ (sampleVector Z ⁻¹' {x | r ≤ F x}) =
    Measure.pi (fun i => μ.map (Z i)) {x | r ≤ F x}
  exact measure_preimage_eq_pi_marginals μ Z hZ hindep _ hA

/-- Expectations of measurable real statistics also transport exactly to the
canonical product law. -/
theorem integral_statistic_eq_pi_marginals
    {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin N → Ω → H)
    (hZ : ∀ i, AEMeasurable (Z i) μ)
    (hindep : iIndepFun Z μ)
    (F : (Fin N → H) → ℝ)
    (hF : AEStronglyMeasurable F (Measure.pi (fun i => μ.map (Z i)))) :
    (∫ ω, F (sampleVector Z ω) ∂μ) =
      ∫ x, F x ∂Measure.pi (fun i => μ.map (Z i)) := by
  have hvec : AEMeasurable (sampleVector Z) μ :=
    aemeasurable_pi_lambda (sampleVector Z) hZ
  have hmap := map_sampleVector_eq_pi_marginals μ Z hZ hindep
  have hFmap : AEStronglyMeasurable F (μ.map (sampleVector Z)) := by
    simpa [hmap] using hF
  calc
    (∫ ω, F (sampleVector Z ω) ∂μ)
        = ∫ x, F x ∂μ.map (sampleVector Z) := by
          simpa [Function.comp_def] using (integral_map hvec hFmap).symm
    _ = ∫ x, F x ∂Measure.pi (fun i => μ.map (Z i)) := by
      rw [hmap]

end UEOT.V3.HilbertMeanProductLaw
