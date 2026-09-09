import UEOT.V3.VariationBridge
import Mathlib.MeasureTheory.VectorMeasure.Integral

/-!
# P-MET-02 — total-variation span bound

This module derives the bounded-observable dual bound from the exact
event-supremum TV metric.  The proof goes through the signed-measure
variation bridge, and centers the observable at the midpoint of a bounding
interval so that the factor two cancels exactly.
-/

namespace UEOT.V3.TVSpan

open MeasureTheory
open scoped ENNReal

universe uX

variable {X : Type uX} [MeasurableSpace X]

theorem integrable_of_interval
    (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g)
    (a b : ℝ)
    (ha : ∀ x, a ≤ g x) (hb : ∀ x, g x ≤ b) :
    Integrable g μ := by
  refine (integrable_const (μ := μ) (max |a| |b|)).mono'
    hg.aestronglyMeasurable ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using abs_le_max_abs_abs (ha x) (hb x)

theorem centered_norm_le_half_span
    (g : X → ℝ) (a b : ℝ) (hab : a ≤ b)
    (ha : ∀ x, a ≤ g x) (hb : ∀ x, g x ≤ b) (x : X) :
    ‖g x - (a + b) / 2‖ ≤ (b - a) / 2 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [ha x, hb x]

theorem abs_integral_sub_le_span_tvDist
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : X → ℝ) (hg : Measurable g)
    (a b : ℝ) (hab : a ≤ b)
    (ha : ∀ x, a ≤ g x) (hb : ∀ x, g x ≤ b) :
    |(∫ x, g x ∂μ) - ∫ x, g x ∂ν| ≤
      (b - a) * UEOT.V3.TotalVariation.tvDist μ ν := by
  let c : ℝ := (a + b) / 2
  let centered : X → ℝ := g - fun _ => c
  have hgμ : Integrable g μ :=
    integrable_of_interval μ g hg a b ha hb
  have hgν : Integrable g ν :=
    integrable_of_interval ν g hg a b ha hb
  have hcμ : Integrable (fun _ : X => c) μ := integrable_const c
  have hcν : Integrable (fun _ : X => c) ν := integrable_const c
  have hcenterμ : Integrable centered μ := by
    simpa [centered] using hgμ.sub hcμ
  have hcenterν : Integrable centered ν := by
    simpa [centered] using hgν.sub hcν
  have hcenterSignedμ :
      μ.toSignedMeasure.Integrable centered := by
    simpa only [VectorMeasure.Integrable,
      Measure.variation_toSignedMeasure] using hcenterμ
  have hcenterSignedν :
      ν.toSignedMeasure.Integrable centered := by
    simpa only [VectorMeasure.Integrable,
      Measure.variation_toSignedMeasure] using hcenterν
  have hvec :
      (∫ᵛ x, centered x ∂<•UEOT.V3.VariationBridge.signedDiff μ ν) =
        (∫ x, centered x ∂μ) - ∫ x, centered x ∂ν := by
    unfold UEOT.V3.VariationBridge.signedDiff
    rw [VectorMeasure.integral_sub_vectorMeasure hcenterSignedμ hcenterSignedν]
    simp
  have hcenter_diff :
      (∫ x, centered x ∂μ) - ∫ x, centered x ∂ν =
        (∫ x, g x ∂μ) - ∫ x, g x ∂ν := by
    simp only [centered, Pi.sub_apply]
    rw [integral_sub hgμ hcμ, integral_sub hgν hcν]
    simp
  letI : IsFiniteMeasure
      (UEOT.V3.VariationBridge.signedDiff μ ν).variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  have hvar :
      ‖∫ᵛ x, centered x ∂<•UEOT.V3.VariationBridge.signedDiff μ ν‖ ≤
        ((b - a) / 2) *
          (UEOT.V3.VariationBridge.signedDiff μ ν).variation.real Set.univ := by
    have hbound :=
      VectorMeasure.norm_integral_le_of_norm_le_const
        (μ := UEOT.V3.VariationBridge.signedDiff μ ν)
        (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip)
        (f := centered)
        (C := (b - a) / 2)
        (ae_of_all _ fun x => by
          simpa [centered, c] using
            centered_norm_le_half_span g a b hab ha hb x)
    simpa using hbound
  rw [hvec, hcenter_diff, Real.norm_eq_abs] at hvar
  rw [← SignedMeasure.totalVariation_eq_variation,
    UEOT.V3.VariationBridge.signedDiff_totalVariation_univ_eq_two_tvDist] at hvar
  nlinarith [UEOT.V3.TotalVariation.tvDist_nonneg μ ν]


/-- Source-facing span of a bounded real observable. -/
noncomputable def span (g : X → ℝ) : ℝ :=
  sSup (Set.range g) - sInf (Set.range g)

/-- Exact P-MET-02 wrapper: for a bounded measurable real observable, the
expectation gap is controlled by its literal supremum-minus-infimum span. -/
theorem abs_integral_sub_le_span
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : X → ℝ) (hg : Measurable g)
    (hbelow : BddBelow (Set.range g))
    (habove : BddAbove (Set.range g)) :
    |(∫ x, g x ∂μ) - ∫ x, g x ∂ν| ≤
      span g * UEOT.V3.TotalVariation.tvDist μ ν := by
  let x₀ : X := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  have ha : ∀ x, sInf (Set.range g) ≤ g x := by
    intro x
    exact csInf_le hbelow (Set.mem_range_self x)
  have hb : ∀ x, g x ≤ sSup (Set.range g) := by
    intro x
    exact le_csSup habove (Set.mem_range_self x)
  have hab : sInf (Set.range g) ≤ sSup (Set.range g) :=
    (ha x₀).trans (hb x₀)
  simpa [span] using
    abs_integral_sub_le_span_tvDist
      μ ν g hg
      (sInf (Set.range g)) (sSup (Set.range g))
      hab ha hb

end UEOT.V3.TVSpan
