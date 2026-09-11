import UEOT.V3.FiniteCandidateDiscovery
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# P-STAT-08 sampling core — bounded losses

For one fixed candidate, a measurable loss in `[0,1]` evaluated on `N`
independent validation observations satisfies the same one-sided Hoeffding
bound used in the frozen P-STAT-08 proof.  Candidate-level union and ERM
selection are deliberately kept in later layers.
-/

namespace UEOT.V3.BoundedLossSampling

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal

universe uΩ uZ

variable {Ω : Type uΩ} {Z : Type uZ}
variable [MeasurableSpace Ω] [MeasurableSpace Z]

/-- Population risk of a measurable scalar loss. -/
noncomputable def trueRisk (P : Measure Z) (loss : Z → ℝ) : ℝ :=
  ∫ z, loss z ∂P

/-- Empirical risk on `N` validation observations. -/
noncomputable def empiricalRisk {N : ℕ}
    (loss : Z → ℝ) (sample : Fin N → Ω → Z) (ω : Ω) : ℝ :=
  (∑ n : Fin N, loss (sample n ω)) / (N : ℝ)

/-- Mapping a validation observation with law `P` through the loss preserves
its expected value as the population risk. -/
theorem integral_loss_sample_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Z)
    (loss : Z → ℝ) (hloss : Measurable loss)
    (X : Ω → Z) (hX : Measurable X)
    (hlaw : μ.map X = P) :
    ∫ ω, loss (X ω) ∂μ = trueRisk P loss := by
  unfold trueRisk
  rw [← hlaw]
  exact (integral_map hX.aemeasurable hloss.aestronglyMeasurable).symm

/-- One-sided Hoeffding inequality for the empirical risk of a fixed candidate. -/
theorem measure_empiricalRisk_upper_le
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
      trueRisk P loss + u ≤ empiricalRisk loss sample ω} ≤
      exp (-2 * (N : ℝ) * u ^ 2) := by
  let X : Fin N → Ω → ℝ := fun n ω => loss (sample n ω)
  let C : Fin N → Ω → ℝ := fun n ω => X n ω - μ[X n]
  have hXmeas : ∀ n, Measurable (X n) := fun n => hloss.comp (hmeas n)
  have hXindep : iIndepFun X μ := by
    simpa [X, Function.comp_def] using
      hindep.comp (fun _ => loss) (fun _ => hloss)
  have hCindep : iIndepFun C μ := by
    simpa [C, Function.comp_def] using
      hXindep.comp (fun n x => x - μ[X n])
        (fun _ => measurable_id.sub measurable_const)
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
    simpa [C] using hs
  have htail := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (h_indep := hCindep)
    (s := (Finset.univ : Finset (Fin N)))
    (h_subG := hsub)
    (ε := (N : ℝ) * u)
    (mul_nonneg (Nat.cast_nonneg N) hu)
  have hset :
      {ω | trueRisk P loss + u ≤ empiricalRisk loss sample ω} ⊆
      {ω | (N : ℝ) * u ≤
        ∑ n ∈ (Finset.univ : Finset (Fin N)), C n ω} := by
    intro ω hω
    change trueRisk P loss + u ≤
      (∑ n : Fin N, loss (sample n ω)) / (N : ℝ) at hω
    change (N : ℝ) * u ≤
      ∑ n ∈ (Finset.univ : Finset (Fin N)), C n ω
    simp only [C, X, Finset.sum_sub_distrib]
    simp_rw [hmean]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    field_simp [ne_of_gt hNreal] at hω ⊢
    linarith
  refine (measureReal_mono hset).trans ?_
  calc
    μ.real {ω | (N : ℝ) * u ≤
        ∑ n ∈ (Finset.univ : Finset (Fin N)), C n ω}
      ≤ exp (-((N : ℝ) * u) ^ 2 /
          (2 * ∑ n ∈ (Finset.univ : Finset (Fin N)), ((1 / 2 : ℝ≥0) ^ 2))) := htail
    _ = exp (-2 * (N : ℝ) * u ^ 2) := by
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
      field_simp [ne_of_gt hNreal]
      ring

end UEOT.V3.BoundedLossSampling
