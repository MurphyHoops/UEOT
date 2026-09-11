import UEOT.V3.BoundedLossSampling
import Mathlib.Tactic

/-!
# P-STAT-08 — two-sided bounded-loss concentration

This layer extends the verified one-sided `[0,1]` Hoeffding core to the lower
and two-sided deviations needed by the finite-candidate union bound.
-/

namespace UEOT.V3.BoundedLossTwoSided

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.BoundedLossSampling
open scoped BigOperators ENNReal NNReal

universe uΩ uZ uF

variable {Ω : Type uΩ} {Z : Type uZ} {F : Type uF}
variable [MeasurableSpace Ω] [MeasurableSpace Z]

/-- Lower-tail Hoeffding inequality for one fixed bounded loss. -/
theorem measure_empiricalRisk_lower_le
    {N : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Z)
    (loss : Z → ℝ) (hloss : Measurable loss)
    (hloss01 : ∀ z, loss z ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin N → Ω → Z)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = P)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω |
      empiricalRisk loss sample ω + u ≤ trueRisk P loss} ≤
      exp (-2 * (N : ℝ) * u ^ 2) := by
  let X : Fin N → Ω → ℝ := fun n ω => loss (sample n ω)
  let C : Fin N → Ω → ℝ := fun n ω => X n ω - trueRisk P loss
  let D : Fin N → Ω → ℝ := fun n ω => - C n ω
  have hXmeas : ∀ n, Measurable (X n) := fun n => hloss.comp (hmeas n)
  have hXindep : iIndepFun X μ := by
    simpa [X, Function.comp_def] using
      hindep.comp (fun _ => loss) (fun _ => hloss)
  have hCindep : iIndepFun C μ := by
    simpa [C, Function.comp_def] using
      hXindep.comp (fun _ x => x - trueRisk P loss)
        (fun _ => measurable_id.sub measurable_const)
  have hDindep : iIndepFun D μ := by
    change iIndepFun (fun n ω => - C n ω) μ
    exact hCindep.comp (fun _ x => -x) (fun _ => measurable_id.neg)
  have hmean : ∀ n, ∫ ω, X n ω ∂μ = trueRisk P loss := by
    intro n
    simpa [X] using
      integral_loss_sample_eq μ P loss hloss (sample n) (hmeas n) (hlaw n)
  have hsub : ∀ n ∈ (Finset.univ : Finset (Fin N)),
      HasSubgaussianMGF (C n) ((1 / 2 : ℝ≥0) ^ 2) μ := by
    intro n _hn
    have hs := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
      (μ := μ) (X := X n) (a := (0 : ℝ)) (b := (1 : ℝ))
      (hXmeas n).aemeasurable
      (ae_of_all μ fun ω => hloss01 (sample n ω))
    simpa [C, hmean n] using hs
  have hDsub : ∀ n ∈ (Finset.univ : Finset (Fin N)),
      HasSubgaussianMGF (D n) ((1 / 2 : ℝ≥0) ^ 2) μ := by
    intro n hn
    change HasSubgaussianMGF (- C n) ((1 / 2 : ℝ≥0) ^ 2) μ
    exact (hsub n hn).neg
  have htail := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (h_indep := hDindep)
    (s := (Finset.univ : Finset (Fin N)))
    (h_subG := hDsub)
    (ε := (N : ℝ) * u)
    (mul_nonneg (Nat.cast_nonneg N) hu)
  have hset :
      {ω | empiricalRisk loss sample ω + u ≤ trueRisk P loss} ⊆
      {ω | (N : ℝ) * u ≤
        ∑ n ∈ (Finset.univ : Finset (Fin N)), D n ω} := by
    intro ω hω
    change (∑ n : Fin N, loss (sample n ω)) / (N : ℝ) + u ≤
      trueRisk P loss at hω
    change (N : ℝ) * u ≤
      ∑ n ∈ (Finset.univ : Finset (Fin N)), D n ω
    simp only [D, C, X, neg_sub, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    field_simp [ne_of_gt hNreal] at hω ⊢
    linarith
  refine (measureReal_mono hset).trans ?_
  calc
    μ.real {ω | (N : ℝ) * u ≤
        ∑ n ∈ (Finset.univ : Finset (Fin N)), D n ω}
      ≤ exp (-((N : ℝ) * u) ^ 2 /
          (2 * ∑ n ∈ (Finset.univ : Finset (Fin N)), ((1 / 2 : ℝ≥0) ^ 2))) := htail
    _ = exp (-2 * (N : ℝ) * u ^ 2) := by
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
      field_simp [ne_of_gt hNreal]
      ring

/-- Two-sided Hoeffding bound for one fixed bounded loss. -/
theorem measure_empiricalRisk_bad_le
    {N : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Z)
    (loss : Z → ℝ) (hloss : Measurable loss)
    (hloss01 : ∀ z, loss z ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin N → Ω → Z)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = P)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u < |empiricalRisk loss sample ω - trueRisk P loss|} ≤
      2 * exp (-2 * (N : ℝ) * u ^ 2) := by
  let upper : Set Ω :=
    {ω | trueRisk P loss + u ≤ empiricalRisk loss sample ω}
  let lower : Set Ω :=
    {ω | empiricalRisk loss sample ω + u ≤ trueRisk P loss}
  have hbad :
      {ω | u < |empiricalRisk loss sample ω - trueRisk P loss|} ⊆
        upper ∪ lower := by
    intro ω hω
    change u < |empiricalRisk loss sample ω - trueRisk P loss| at hω
    change ω ∈ upper ∪ lower
    by_cases hord : trueRisk P loss ≤ empiricalRisk loss sample ω
    · left
      change trueRisk P loss + u ≤ empiricalRisk loss sample ω
      rw [abs_of_nonneg (sub_nonneg.mpr hord)] at hω
      linarith
    · right
      have hord' : empiricalRisk loss sample ω < trueRisk P loss := lt_of_not_ge hord
      change empiricalRisk loss sample ω + u ≤ trueRisk P loss
      rw [abs_of_nonpos (sub_nonpos.mpr hord'.le)] at hω
      linarith
  have hupper : μ.real upper ≤ exp (-2 * (N : ℝ) * u ^ 2) := by
    simpa [upper] using
      measure_empiricalRisk_upper_le hN μ P loss hloss hloss01
        sample hmeas hindep hlaw hu
  have hlower : μ.real lower ≤ exp (-2 * (N : ℝ) * u ^ 2) := by
    simpa [lower] using
      measure_empiricalRisk_lower_le hN μ P loss hloss hloss01
        sample hmeas hindep hlaw hu
  calc
    μ.real {ω | u < |empiricalRisk loss sample ω - trueRisk P loss|}
        ≤ μ.real (upper ∪ lower) := measureReal_mono hbad
    _ ≤ μ.real upper + μ.real lower := measureReal_union_le upper lower
    _ ≤ exp (-2 * (N : ℝ) * u ^ 2) + exp (-2 * (N : ℝ) * u ^ 2) :=
      add_le_add hupper hlower
    _ = 2 * exp (-2 * (N : ℝ) * u ^ 2) := by ring

/-- Finite-candidate union bound. Independence between candidates is not
required; only the validation observations are independent. -/
theorem measure_exists_candidate_bad_le
    [Fintype F]
    {N : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Z)
    (loss : F → Z → ℝ)
    (hloss : ∀ f, Measurable (loss f))
    (hloss01 : ∀ f z, loss f z ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin N → Ω → Z)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = P)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | ∃ f : F,
      u < |empiricalRisk (loss f) sample ω - trueRisk P (loss f)|} ≤
      (Fintype.card F : ℝ) *
        (2 * exp (-2 * (N : ℝ) * u ^ 2)) := by
  have hset :
      {ω | ∃ f : F,
        u < |empiricalRisk (loss f) sample ω - trueRisk P (loss f)|} =
      ⋃ f : F, {ω |
        u < |empiricalRisk (loss f) sample ω - trueRisk P (loss f)|} := by
    ext ω
    simp
  rw [hset]
  calc
    μ.real (⋃ f : F, {ω |
        u < |empiricalRisk (loss f) sample ω - trueRisk P (loss f)|})
      ≤ ∑ f : F, μ.real {ω |
          u < |empiricalRisk (loss f) sample ω - trueRisk P (loss f)|} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _f : F, (2 * exp (-2 * (N : ℝ) * u ^ 2)) := by
      exact Finset.sum_le_sum fun f _ =>
        measure_empiricalRisk_bad_le hN μ P (loss f) (hloss f)
          (hloss01 f) sample hmeas hindep hlaw hu
    _ = (Fintype.card F : ℝ) *
        (2 * exp (-2 * (N : ℝ) * u ^ 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      norm_cast

end UEOT.V3.BoundedLossTwoSided
