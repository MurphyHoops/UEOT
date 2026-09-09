import UEOT.V3.TotalVariation
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# P-MET-01 / P-MET-02 — signed-measure bridge

This module connects the source event-supremum definition of total variation
used by UEOT to Mathlib's signed/vector measure infrastructure.

No P-ID promotion is claimed here.  The eventual target is to identify the
probability-measure TV distance with one half of the variation mass of
`μ.toSignedMeasure - ν.toSignedMeasure`, then reuse Mathlib's variation
integral bounds.
-/

namespace UEOT.V3.VariationBridge

open MeasureTheory

universe uX

variable {X : Type uX} [MeasurableSpace X]

noncomputable def signedDiff
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    SignedMeasure X :=
  μ.toSignedMeasure - ν.toSignedMeasure

theorem signedDiff_apply
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Set X) (hA : MeasurableSet A) :
    signedDiff μ ν A = μ.real A - ν.real A := by
  unfold signedDiff
  exact Measure.toSignedMeasure_sub_apply hA

theorem abs_signedDiff_apply_eq_tvEvent
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Set X) (hA : MeasurableSet A) :
    |signedDiff μ ν A| = |μ.real A - ν.real A| := by
  rw [signedDiff_apply μ ν A hA]

theorem signedDiff_univ_eq_zero
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    signedDiff μ ν Set.univ = 0 := by
  rw [signedDiff_apply μ ν Set.univ MeasurableSet.univ]
  simp

theorem tvEvent_le_norm_signedDiff
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set X) (hA : MeasurableSet A) :
    |signedDiff μ ν A| ≤ UEOT.V3.TotalVariation.tvDist μ ν := by
  simpa [abs_signedDiff_apply_eq_tvEvent μ ν A hA] using
    UEOT.V3.TotalVariation.tvEvent_le μ ν A hA


theorem tvDist_le_signedDiff_totalVariation_univ
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    UEOT.V3.TotalVariation.tvDist μ ν ≤
      (signedDiff μ ν).totalVariation.real Set.univ := by
  unfold UEOT.V3.TotalVariation.tvDist
  refine csSup_le (UEOT.V3.TotalVariation.tvEventSet_nonempty μ ν) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  calc
    |μ.real A - ν.real A| = ‖signedDiff μ ν A‖ := by
      rw [signedDiff_apply μ ν A hA, Real.norm_eq_abs]
    _ ≤ (signedDiff μ ν).totalVariation.real A :=
      SignedMeasure.norm_le_totalVariation (signedDiff μ ν) A
    _ ≤ (signedDiff μ ν).totalVariation.real Set.univ :=
      measureReal_mono (Set.subset_univ A)


theorem signedDiff_posMass_eq_negMass
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (signedDiff μ ν).toJordanDecomposition.posPart.real Set.univ =
      (signedDiff μ ν).toJordanDecomposition.negPart.real Set.univ := by
  have hz := signedDiff_univ_eq_zero μ ν
  rw [SignedMeasure.apply_eq_posPart_real_sub_negPart_real
    (signedDiff μ ν) MeasurableSet.univ] at hz
  linarith

theorem tvDist_le_signedDiff_posMass
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    UEOT.V3.TotalVariation.tvDist μ ν ≤
      (signedDiff μ ν).toJordanDecomposition.posPart.real Set.univ := by
  unfold UEOT.V3.TotalVariation.tvDist
  refine csSup_le (UEOT.V3.TotalVariation.tvEventSet_nonempty μ ν) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  have hs :=
    SignedMeasure.apply_eq_posPart_real_sub_negPart_real
      (signedDiff μ ν) hA
  rw [signedDiff_apply μ ν A hA] at hs
  have hmass := signedDiff_posMass_eq_negMass μ ν
  have hp0 :
      0 ≤ (signedDiff μ ν).toJordanDecomposition.posPart.real A :=
    measureReal_nonneg
  have hn0 :
      0 ≤ (signedDiff μ ν).toJordanDecomposition.negPart.real A :=
    measureReal_nonneg
  have hp_le :
      (signedDiff μ ν).toJordanDecomposition.posPart.real A ≤
        (signedDiff μ ν).toJordanDecomposition.posPart.real Set.univ :=
    measureReal_mono (Set.subset_univ A)
  have hn_le :
      (signedDiff μ ν).toJordanDecomposition.negPart.real A ≤
        (signedDiff μ ν).toJordanDecomposition.negPart.real Set.univ :=
    measureReal_mono (Set.subset_univ A)
  rw [abs_le]
  constructor <;> linarith

theorem signedDiff_posMass_le_tvDist
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (signedDiff μ ν).toJordanDecomposition.posPart.real Set.univ ≤
      UEOT.V3.TotalVariation.tvDist μ ν := by
  let s := signedDiff μ ν
  obtain ⟨A, hA, hpos, hneg, hp, hn⟩ := s.toJordanDecomposition_spec
  have hA_nonneg : 0 ≤ s A :=
    s.nonneg_of_zero_le_restrict hpos
  have hpos_mass :
      s.toJordanDecomposition.posPart.real Set.univ = s A := by
    rw [hp, SignedMeasure.toMeasureOfZeroLE_real_apply hpos hA MeasurableSet.univ]
    simp
  have htv := UEOT.V3.TotalVariation.tvEvent_le μ ν A hA
  have hsA : s A = μ.real A - ν.real A := by
    simpa [s] using signedDiff_apply μ ν A hA
  rw [← hpos_mass, hsA] at hA_nonneg
  rw [← hpos_mass]
  simpa [abs_of_nonneg hA_nonneg] using htv

theorem tvDist_eq_signedDiff_posMass
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    UEOT.V3.TotalVariation.tvDist μ ν =
      (signedDiff μ ν).toJordanDecomposition.posPart.real Set.univ :=
  le_antisymm (tvDist_le_signedDiff_posMass μ ν)
    (signedDiff_posMass_le_tvDist μ ν)

end UEOT.V3.VariationBridge
