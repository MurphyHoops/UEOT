import UEOT.V3.HilbertMeanFirstMoment
import UEOT.V3.HilbertMeanSourceVariance
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

/-!
# P-STAT-06 — source first-moment bridge

This module connects the generic centered-Hilbert first-moment estimate to the
canonical product-law source statistic.  The deterministic bridge records that
centering every sample coordinate by the common mean commutes exactly with the
empirical mean; the source theorem then transports independence, zero mean, and
the sharp unit second-moment bound from the marginals to the product law.

Bochner integrability of each marginal identity map is explicit.  This is the
minimal analytic condition needed for the mean embedding and avoids silently
adding separability/second-countability assumptions on the Hilbert space.
-/

namespace UEOT.V3.HilbertMeanSourceFirstMoment

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanFirstMoment
open UEOT.V3.HilbertMeanSourceVariance

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Centering each coordinate by a common Hilbert mean commutes exactly with
finite empirical averaging. -/
theorem empiricalMean_centered_eq_sub
    {N : ℕ} (hN : 0 < N) (ω : Fin N → H) (μH : H) :
    empiricalMean (fun i => ω i - μH) = empiricalMean ω - μH := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold empiricalMean
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [smul_sub]
  rw [← Nat.cast_smul_eq_nsmul ℝ N μH]
  rw [smul_smul]
  have hscale : ((N : ℝ)⁻¹ * (N : ℝ)) = 1 := by
    field_simp [hNreal]
  rw [hscale, one_smul]

/-- Exact source first moment for the canonical finite product law.  If every
marginal is supported in the Hilbert unit ball, is Bochner integrable, and has
common Bochner mean `μH`, then the expected empirical-mean error is at most
`1 / sqrt N`. -/
theorem source_meanError_first_moment_le_one_div_sqrt
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H)
    (hInt : ∀ j, Integrable (fun x : H => x) (μ j))
    (hmean : ∀ j, (∫ x : H, x ∂μ j) = μH)
    (hunit : ∀ j, ∀ᵐ x ∂μ j, ‖x‖ ≤ 1) :
    (∫ ω : Fin N → H, ‖empiricalMean ω - μH‖ ∂Measure.pi μ) ≤
      1 / Real.sqrt (N : ℝ) := by
  let P : Measure (Fin N → H) := Measure.pi μ
  let Z : Fin N → (Fin N → H) → H := fun i ω => ω i - μH
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  have hmargInt : ∀ i, Integrable (fun x : H => x - μH) (μ i) := by
    intro i
    exact (hInt i).sub (integrable_const μH)
  have hmargSqInt : ∀ i, Integrable (fun x : H => ‖x - μH‖ ^ 2) (μ i) := by
    intro i
    exact integrable_norm_sub_const_sq_of_ae_norm_le_one
      (μ i) μH (hInt i) (hunit i)
  have hindep : iIndepFun Z P := by
    dsimp [Z, P]
    simpa only [Function.comp_apply] using
      (iIndepFun_pi
        (μ := μ)
        (X := fun _i (x : H) => x - μH)
        (fun i => (hmargInt i).aestronglyMeasurable.aemeasurable))
  have hint : ∀ i, Integrable (Z i) P := by
    intro i
    simpa [Z, P] using (integrable_comp_eval (hmargInt i))
  have hmean0 : ∀ i, (∫ ω, Z i ω ∂P) = 0 := by
    intro i
    have hprod :
        (∫ ω : Fin N → H, ω i - μH ∂Measure.pi μ) =
          ∫ x : H, x - μH ∂μ i := by
      exact integral_comp_eval (hmargInt i).aestronglyMeasurable
    have hmarg0 : (∫ x : H, x - μH ∂μ i) = 0 := by
      rw [integral_sub (hInt i) (integrable_const μH), hmean i]
      simp
    rw [show (∫ ω, Z i ω ∂P) = ∫ x : H, x - μH ∂μ i by
      simpa [Z, P] using hprod]
    exact hmarg0
  have hdiagInt : ∀ i, Integrable (fun ω => ‖Z i ω‖ ^ 2) P := by
    intro i
    simpa [Z, P] using (integrable_comp_eval (hmargSqInt i))
  have hdiag : ∀ i, (∫ ω, ‖Z i ω‖ ^ 2 ∂P) ≤ 1 := by
    intro i
    have hprod :
        (∫ ω : Fin N → H, ‖ω i - μH‖ ^ 2 ∂Measure.pi μ) =
          ∫ x : H, ‖x - μH‖ ^ 2 ∂μ i := by
      exact integral_comp_eval (hmargSqInt i).aestronglyMeasurable
    rw [show (∫ ω, ‖Z i ω‖ ^ 2 ∂P) =
        ∫ x : H, ‖x - μH‖ ^ 2 ∂μ i by simpa [Z, P] using hprod]
    exact integral_norm_sub_mean_sq_le_one
      (μ i) μH (hInt i) (hmean i) (hunit i)
  have hgeneric := integral_norm_empiricalMean_le_one_div_sqrt
    hN P Z hindep hint hmean0 hdiagInt hdiag
  calc
    (∫ ω : Fin N → H, ‖empiricalMean ω - μH‖ ∂Measure.pi μ)
        = ∫ ω : Fin N → H, ‖empiricalMean (fun i => Z i ω)‖ ∂P := by
            apply integral_congr_ae
            exact ae_of_all P (fun ω => by
              rw [empiricalMean_centered_eq_sub hN ω μH]
              rfl)
    _ ≤ 1 / Real.sqrt (N : ℝ) := hgeneric

end UEOT.V3.HilbertMeanSourceFirstMoment
