import UEOT.V3.TotalVariation
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.Tactic.Linarith

/-!
# P-INV-01 — binary testing lower bound and attainability

The frozen source considers two models with equal prior probability. If `A`
is the measurable decision region on which the test selects model 1, then the
average error is

`(1/2) * (P₀(A) + P₁(Aᶜ))`.

We prove both halves on a general measurable space. The universal lower bound
comes directly from source total variation. Attainability uses the finite-
measure Hahn decomposition for `P₁-P₀`: on the Hahn set the difference is
nonnegative, on its complement it is nonpositive. This is the measure-
theoretic form of the source proof's density-comparison event relative to
`P₀+P₁`.
-/

namespace UEOT.V3.BinaryTesting

open MeasureTheory
open UEOT.V3.TotalVariation

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- Equal-prior average error of the binary test that chooses model 1 on `A`
and model 0 on its complement. -/
noncomputable def binaryRisk (P₀ P₁ : Measure X) (A : Set X) : ℝ :=
  (1 / 2 : ℝ) * (P₀.real A + P₁.real Aᶜ)

/-- The source algebraic form of the equal-prior error. -/
theorem binaryRisk_eq_half_one_sub_diff
    (P₀ P₁ : Measure X)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (A : Set X) (hA : MeasurableSet A) :
    binaryRisk P₀ P₁ A =
      (1 / 2 : ℝ) * (1 - (P₁.real A - P₀.real A)) := by
  have hcompl := probReal_add_probReal_compl (μ := P₁) hA
  unfold binaryRisk
  linarith

/-- Every measurable binary test has error at least
`(1/2) * (1 - D_TV(P₀,P₁))`. -/
theorem binaryRisk_lower_bound
    (P₀ P₁ : Measure X)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (A : Set X) (hA : MeasurableSet A) :
    (1 / 2 : ℝ) * (1 - tvDist P₀ P₁) ≤ binaryRisk P₀ P₁ A := by
  have htv := tvEvent_le P₀ P₁ A hA
  rw [abs_sub_comm] at htv
  have hdiff : P₁.real A - P₀.real A ≤ tvDist P₀ P₁ :=
    (le_abs_self (P₁.real A - P₀.real A)).trans htv
  rw [binaryRisk_eq_half_one_sub_diff P₀ P₁ A hA]
  linarith

private theorem measureReal_le_of_le
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Set X) (h : μ A ≤ ν A) : μ.real A ≤ ν.real A := by
  exact ENNReal.toReal_mono (measure_ne_top ν A) h

/-- For two probability measures there is a measurable Hahn event whose
signed probability gap `P₁(A)-P₀(A)` attains source total variation. -/
theorem exists_event_gap_eq_tvDist
    (P₀ P₁ : Measure X)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] :
    ∃ S : Set X, MeasurableSet S ∧
      P₁.real S - P₀.real S = tvDist P₀ P₁ := by
  obtain ⟨S, hS⟩ := exists_isHahnDecomposition P₀ P₁
  have hpos : ∀ T : Set X, MeasurableSet T → T ⊆ S →
      P₀.real T ≤ P₁.real T := by
    intro T hT hTS
    have hraw : P₀ T ≤ P₁ T := by
      have hrestr := hS.le_on T
      simpa [Measure.restrict_apply hT, Set.inter_eq_left.mpr hTS] using hrestr
    exact measureReal_le_of_le P₀ P₁ T hraw
  have hneg : ∀ T : Set X, MeasurableSet T → T ⊆ Sᶜ →
      P₁.real T ≤ P₀.real T := by
    intro T hT hTS
    have hraw : P₁ T ≤ P₀ T := by
      have hrestr := hS.ge_on_compl T
      simpa [Measure.restrict_apply hT, Set.inter_eq_left.mpr hTS] using hrestr
    exact measureReal_le_of_le P₁ P₀ T hraw
  have hgap_nonneg : 0 ≤ P₁.real S - P₀.real S := by
    exact sub_nonneg.mpr (hpos S hS.measurableSet subset_rfl)
  have hsigned : ∀ A : Set X, MeasurableSet A →
      P₁.real A - P₀.real A ≤ P₁.real S - P₀.real S := by
    intro A hA
    have hA0 := measureReal_inter_add_sdiff (μ := P₀) (s := A) hS.measurableSet
    have hA1 := measureReal_inter_add_sdiff (μ := P₁) (s := A) hS.measurableSet
    have hS0 := measureReal_inter_add_sdiff (μ := P₀) (s := S) hA
    have hS1 := measureReal_inter_add_sdiff (μ := P₁) (s := S) hA
    have hpos_rest : P₀.real (S \ A) ≤ P₁.real (S \ A) :=
      hpos (S \ A) (MeasurableSet.diff hS.measurableSet hA) Set.sdiff_subset
    have hneg_inter : P₁.real (A \ S) ≤ P₀.real (A \ S) := by
      apply hneg (A \ S) (MeasurableSet.diff hA hS.measurableSet)
      intro x hx
      exact hx.2
    simp only [Set.inter_comm S A] at hS0 hS1
    linarith
  have hall : ∀ A : Set X, MeasurableSet A →
      |P₀.real A - P₁.real A| ≤ P₁.real S - P₀.real S := by
    intro A hA
    have hforward := hsigned A hA
    have hbackward := hsigned Aᶜ hA.compl
    have hcompl0 := probReal_add_probReal_compl (μ := P₀) hA
    have hcompl1 := probReal_add_probReal_compl (μ := P₁) hA
    rw [abs_le]
    constructor <;> linarith
  have htv_le : tvDist P₀ P₁ ≤ P₁.real S - P₀.real S := by
    unfold tvDist
    refine csSup_le (tvEventSet_nonempty P₀ P₁) ?_
    intro r hr
    rcases hr with ⟨A, hA, rfl⟩
    exact hall A hA
  have hgap_le : P₁.real S - P₀.real S ≤ tvDist P₀ P₁ := by
    have h := tvEvent_le P₀ P₁ S hS.measurableSet
    rw [abs_of_nonpos (sub_nonpos.mpr (hpos S hS.measurableSet subset_rfl))] at h
    linarith
  exact ⟨S, hS.measurableSet, le_antisymm hgap_le htv_le⟩

/-- **P-INV-01.** On a general measurable space, equal-prior binary testing
has minimum average error exactly `1/2 * (1 - D_TV(P₀,P₁))`. The theorem
returns a measurable optimal test together with its optimality against every
other measurable test. -/
theorem p_inv_01
    (P₀ P₁ : Measure X)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] :
    ∃ A : Set X, MeasurableSet A ∧
      binaryRisk P₀ P₁ A = (1 / 2 : ℝ) * (1 - tvDist P₀ P₁) ∧
      ∀ B : Set X, MeasurableSet B →
        binaryRisk P₀ P₁ A ≤ binaryRisk P₀ P₁ B := by
  obtain ⟨A, hA, hgap⟩ := exists_event_gap_eq_tvDist P₀ P₁
  refine ⟨A, hA, ?_, ?_⟩
  · rw [binaryRisk_eq_half_one_sub_diff P₀ P₁ A hA, hgap]
  · intro B hB
    rw [binaryRisk_eq_half_one_sub_diff P₀ P₁ A hA, hgap]
    exact binaryRisk_lower_bound P₀ P₁ B hB

end UEOT.V3.BinaryTesting
