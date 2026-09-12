import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# P-STAT-06 — rational conditional-MGF lift

`Kernel.HasSubgaussianMGF.of_rat` reduces the uncountable all-real MGF condition
to rational parameters.  This adapter packages the corresponding conditional
expectation form: global exponential integrability plus a trimmed conditional
MGF bound for every rational parameter implies `HasCondSubgaussianMGF`.
-/

namespace UEOT.V3.HilbertMeanConditionalSubGaussianLift

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω]
variable {m : MeasurableSpace Ω}
variable {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- Since conditional expectations and constants are `m`-strongly measurable,
a μ-a.e. conditional-MGF bound can be promoted to the trimmed measure. -/
theorem ae_trim_condExp_le_of_ae_condExp_le
    (hm : m ≤ (inferInstance : MeasurableSpace Ω)) {f : Ω → ℝ} {b : ℝ}
    (h : (μ[f | m]) ≤ᵐ[μ] (fun _ => b)) :
    (μ[f | m]) ≤ᵐ[μ.trim hm] (fun _ => b) := by
  exact StronglyMeasurable.ae_le_trim_of_stronglyMeasurable
    hm stronglyMeasurable_condExp stronglyMeasurable_const h

/-- Construct conditional sub-Gaussianity from rational conditional-expectation
MGF bounds. -/
theorem hasCondSubgaussianMGF_of_rat_condExp_le
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hm : m ≤ (inferInstance : MeasurableSpace Ω))
    (h_int : ∀ t : ℝ, Integrable (fun ω => exp (t * X ω)) μ)
    (h_rat : ∀ q : ℚ, ∀ᵐ ω ∂(μ.trim hm),
      (μ[fun y => exp ((q : ℝ) * X y) | m]) ω ≤
        exp ((c : ℝ) * (q : ℝ) ^ 2 / 2)) :
    HasCondSubgaussianMGF m hm X c μ := by
  apply Kernel.HasSubgaussianMGF.of_rat
  · intro t
    rw [condExpKernel_comp_trim (μ := μ) hm]
    exact h_int t
  · intro q
    have heq := condExp_ae_eq_trim_integral_condExpKernel hm (h_int (q : ℝ))
    filter_upwards [h_rat q, heq] with ω hbound hEq
    rw [hEq] at hbound
    simpa [mgf] using hbound

end UEOT.V3.HilbertMeanConditionalSubGaussianLift
