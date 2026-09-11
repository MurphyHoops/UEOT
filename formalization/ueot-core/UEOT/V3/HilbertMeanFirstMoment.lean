import UEOT.V3.HilbertMeanSecondMoment
import Mathlib.Probability.Moments.Variance

/-!
# P-STAT-06 — first-moment bridge

This module isolates the Jensen/Cauchy–Schwarz step used by the frozen
P-STAT-06 proof. On a probability space, the first moment of a real random
variable is at most the square root of its second moment. We derive this from
nonnegativity of variance, so no constant is lost.  The final theorem applies
that exact bridge to the centered Hilbert empirical mean and obtains `1/√N`.
-/

namespace UEOT.V3.HilbertMeanFirstMoment

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanSecondMoment
open scoped BigOperators

universe uΩ uH

variable {Ω : Type uΩ} [MeasurableSpace Ω]

/-- Probability-space first/second-moment bridge with the exact constant one:
`E[X] ≤ sqrt(E[X²])`. -/
theorem integral_le_sqrt_integral_sq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hX : AEStronglyMeasurable X μ)
    (hXsq : Integrable (fun ω => X ω ^ 2) μ) :
    (∫ ω, X ω ∂μ) ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂μ) := by
  have hmem : MemLp X 2 μ :=
    (memLp_two_iff_integrable_sq hX).2 hXsq
  have hvar : 0 ≤ variance X μ := variance_nonneg X μ
  rw [variance_eq_sub hmem] at hvar
  have hsq :
      (∫ ω, X ω ∂μ) ^ 2 ≤ ∫ ω, X ω ^ 2 ∂μ :=
    sub_nonneg.mp hvar
  exact Real.le_sqrt_of_sq_le hsq

variable {H : Type uH} [MeasurableSpace H]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [BorelSpace H]

/-- Exact first-moment estimate for an independent centered Hilbert empirical
mean.  This is the Jensen step in frozen P-STAT-06 with no constant loss. -/
theorem integral_norm_empiricalMean_le_one_div_sqrt
    {N : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin N → Ω → H)
    (hindep : iIndepFun Z μ)
    (hint : ∀ i, Integrable (Z i) μ)
    (hmean : ∀ i, (∫ ω, Z i ω ∂μ) = 0)
    (hdiagInt : ∀ i, Integrable (fun ω => ‖Z i ω‖ ^ 2) μ)
    (hdiag : ∀ i, (∫ ω, ‖Z i ω‖ ^ 2 ∂μ) ≤ 1) :
    (∫ ω, ‖empiricalMean (fun i => Z i ω)‖ ∂μ) ≤
      1 / Real.sqrt (N : ℝ) := by
  classical
  have hinner : ∀ i j : Fin N,
      Integrable (fun ω => inner ℝ (Z i ω) (Z j ω)) μ := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa only [real_inner_self_eq_norm_sq] using hdiagInt i
    · have hbilin := (hindep.indepFun hij).integrable_bilin
        (hint i) (hint j) (innerSL ℝ)
      simpa only [innerSL_apply_apply ℝ] using hbilin
  have hdouble : Integrable
      (fun ω => ∑ i : Fin N, ∑ j : Fin N, inner ℝ (Z i ω) (Z j ω)) μ := by
    exact integrable_finsetSum _ (fun i _hi =>
      integrable_finsetSum _ (fun j _hj => hinner i j))
  have hscaled : Integrable
      (fun ω => ((N : ℝ)⁻¹) ^ 2 *
        (∑ i : Fin N, ∑ j : Fin N, inner ℝ (Z i ω) (Z j ω))) μ :=
    Integrable.const_mul hdouble _
  have hnormSq : Integrable
      (fun ω => ‖empiricalMean (fun i => Z i ω)‖ ^ 2) μ := by
    exact Integrable.congr hscaled <| ae_of_all μ fun ω =>
      (norm_empiricalMean_sq_eq_double_sum hN (fun i => Z i ω)).symm
  have hsum : Integrable (fun ω => ∑ i : Fin N, Z i ω) μ :=
    integrable_finsetSum _ (fun i _hi => hint i)
  have hemp : Integrable (fun ω => empiricalMean (fun i => Z i ω)) μ := by
    unfold empiricalMean
    change Integrable (((N : ℝ)⁻¹) • (fun ω => ∑ i : Fin N, Z i ω)) μ
    exact hsum.smul ((N : ℝ)⁻¹)
  have hfirst := integral_le_sqrt_integral_sq μ
    (fun ω => ‖empiricalMean (fun i => Z i ω)‖)
    hemp.norm.aestronglyMeasurable hnormSq
  have hsecond := integral_norm_empiricalMean_sq_le_one_div
    hN μ Z hindep hint hmean hdiagInt hdiag
  calc
    (∫ ω, ‖empiricalMean (fun i => Z i ω)‖ ∂μ)
        ≤ Real.sqrt (∫ ω, ‖empiricalMean (fun i => Z i ω)‖ ^ 2 ∂μ) := hfirst
    _ ≤ Real.sqrt (1 / (N : ℝ)) := Real.sqrt_le_sqrt hsecond
    _ = 1 / Real.sqrt (N : ℝ) := by
      rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1), Real.sqrt_one]

end UEOT.V3.HilbertMeanFirstMoment
