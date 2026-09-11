import UEOT.V3.HilbertMeanConcentration
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# P-STAT-06 — Hilbert second-moment core

This module formalizes the key second-moment identities used in the frozen
RKHS empirical-mean concentration proof: independent centered Hilbert-valued
random variables have zero expected cross inner product, and the squared norm
of an empirical mean expands into the corresponding double inner-product sum.
-/

namespace UEOT.V3.HilbertMeanSecondMoment

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open scoped BigOperators

universe uΩ uH

variable {Ω : Type uΩ} {H : Type uH}
variable [MeasurableSpace Ω] [MeasurableSpace H]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [BorelSpace H]

/-- Two independent integrable centered Hilbert-valued random variables have
zero expected cross inner product. -/
theorem integral_inner_eq_zero_of_indep_centered
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → H)
    (hXY : X ⟂ᵢ[μ] Y)
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hX0 : (∫ ω, X ω ∂μ) = 0)
    (hY0 : (∫ ω, Y ω ∂μ) = 0) :
    (∫ ω, inner ℝ (X ω) (Y ω) ∂μ) = 0 := by
  have hfactor := hXY.integral_bilin hX hY (innerSL ℝ)
  simpa only [innerSL_apply_apply ℝ, hX0, hY0, map_zero] using hfactor

/-- In an independent finite family of centered Hilbert-valued random
variables, every off-diagonal cross inner product has expectation zero. -/
theorem integral_inner_eq_zero_of_iIndep_centered
    {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin N → Ω → H)
    (hindep : iIndepFun Z μ)
    (hint : ∀ i, Integrable (Z i) μ)
    (hmean : ∀ i, (∫ ω, Z i ω ∂μ) = 0)
    (i j : Fin N) (hij : i ≠ j) :
    (∫ ω, inner ℝ (Z i ω) (Z j ω) ∂μ) = 0 := by
  exact integral_inner_eq_zero_of_indep_centered μ (Z i) (Z j)
    (hindep.indepFun hij) (hint i) (hint j) (hmean i) (hmean j)

/-- Algebraic expansion of the squared Hilbert norm of an empirical mean.
This is the deterministic identity underlying the P-STAT-06 second-moment
calculation. -/
theorem norm_empiricalMean_sq_eq_double_sum
    {N : ℕ} (hN : 0 < N) (z : Fin N → H) :
    ‖empiricalMean z‖ ^ 2 =
      ((N : ℝ)⁻¹) ^ 2 * ∑ i : Fin N, ∑ j : Fin N, inner ℝ (z i) (z j) := by
  rw [← real_inner_self_eq_norm_sq]
  unfold empiricalMean
  rw [real_inner_smul_left, real_inner_smul_right]
  simp_rw [sum_inner, inner_sum]
  ring

/-- Exact second-moment estimate for an independent centered Hilbert family.
If each diagonal second moment is at most one, then the empirical mean has
second moment at most `1/N`.  This is the probabilistic core of the frozen
P-STAT-06 constant. -/
theorem integral_norm_empiricalMean_sq_le_one_div
    {N : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin N → Ω → H)
    (hindep : iIndepFun Z μ)
    (hint : ∀ i, Integrable (Z i) μ)
    (hmean : ∀ i, (∫ ω, Z i ω ∂μ) = 0)
    (hdiagInt : ∀ i, Integrable (fun ω => ‖Z i ω‖ ^ 2) μ)
    (hdiag : ∀ i, (∫ ω, ‖Z i ω‖ ^ 2 ∂μ) ≤ 1) :
    (∫ ω, ‖empiricalMean (fun i => Z i ω)‖ ^ 2 ∂μ) ≤
      1 / (N : ℝ) := by
  classical
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hinner : ∀ i j : Fin N,
      Integrable (fun ω => inner ℝ (Z i ω) (Z j ω)) μ := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa only [real_inner_self_eq_norm_sq] using hdiagInt i
    · have hbilin := (hindep.indepFun hij).integrable_bilin
        (hint i) (hint j) (innerSL ℝ)
      simpa only [innerSL_apply_apply ℝ] using hbilin
  have hdouble_le :
      (∑ i : Fin N, ∑ j : Fin N,
        ∫ ω, inner ℝ (Z i ω) (Z j ω) ∂μ) ≤ (N : ℝ) := by
    calc
      (∑ i : Fin N, ∑ j : Fin N,
          ∫ ω, inner ℝ (Z i ω) (Z j ω) ∂μ) =
          ∑ i : Fin N, ∫ ω, ‖Z i ω‖ ^ 2 ∂μ := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.sum_eq_single i]
            · simp only [real_inner_self_eq_norm_sq]
            · intro j _hj hji
              exact integral_inner_eq_zero_of_iIndep_centered μ Z hindep hint hmean i j
                (fun hij => hji hij.symm)
            · simp
      _ ≤ ∑ _i : Fin N, (1 : ℝ) := by
            exact Finset.sum_le_sum (fun i _hi => hdiag i)
      _ = (N : ℝ) := by simp
  calc
    (∫ ω, ‖empiricalMean (fun i => Z i ω)‖ ^ 2 ∂μ) =
        ∫ ω, ((N : ℝ)⁻¹) ^ 2 *
          (∑ i : Fin N, ∑ j : Fin N, inner ℝ (Z i ω) (Z j ω)) ∂μ := by
            apply integral_congr_ae
            exact ae_of_all μ (fun ω =>
              norm_empiricalMean_sq_eq_double_sum hN (fun i => Z i ω))
    _ = ((N : ℝ)⁻¹) ^ 2 *
        (∫ ω, ∑ i : Fin N, ∑ j : Fin N,
          inner ℝ (Z i ω) (Z j ω) ∂μ) := by
            rw [integral_const_mul]
    _ = ((N : ℝ)⁻¹) ^ 2 *
        (∑ i : Fin N, ∑ j : Fin N,
          ∫ ω, inner ℝ (Z i ω) (Z j ω) ∂μ) := by
            congr 1
            rw [integral_finsetSum]
            · apply Finset.sum_congr rfl
              intro i _hi
              rw [integral_finsetSum]
              exact fun j _hj => hinner i j
            · intro i _hi
              exact integrable_finsetSum _ (fun j _hj => hinner i j)
    _ ≤ ((N : ℝ)⁻¹) ^ 2 * (N : ℝ) := by
            exact mul_le_mul_of_nonneg_left hdouble_le (sq_nonneg _)
    _ = 1 / (N : ℝ) := by
            field_simp [ne_of_gt hNreal]

end UEOT.V3.HilbertMeanSecondMoment
