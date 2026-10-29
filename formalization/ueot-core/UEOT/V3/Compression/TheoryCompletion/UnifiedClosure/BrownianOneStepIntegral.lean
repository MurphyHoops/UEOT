import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianMartingaleSource

/-!
Original commitment: actual causal actions must consume the source, not independent noise certificates.
Existing result: the actual natural filtration supplies zero conditional increment mean and elapsed-time variance.
Premise reduced: derive conditional moments and exact one-step L2 isometry for a bounded past-measurable coefficient.
Model/witness: SAME source/process/clock; the coefficient sees only the interval START's natural past.
Consumer: simple predictable finite-partition integration; general Ito/Girsanov remain open.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOneStepIntegral
open MeasureTheory ProbabilityTheory
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- The literal one-step integral output, with no independently chosen version. -/
def oneStep (H : (ℝ≥0 → ℝ) → ℝ) (s t : ℝ≥0) : (ℝ≥0 → ℝ) → ℝ := H * increment s t

/-- Boundedness is L-infinity membership under the SAME source law. -/
theorem oneStep_memLp_two {H : (ℝ≥0 → ℝ) → ℝ} (hH : MemLp H ∞ sourceLaw) (s t : ℝ≥0) :
    MemLp (oneStep H s t) 2 sourceLaw :=
  (process_isPreBrownian.hasLaw_sub t s).hasGaussianLaw.memLp_two.mul hH

theorem oneStep_integrable {H : (ℝ≥0 → ℝ) → ℝ} (hH : MemLp H ∞ sourceLaw) (s t : ℝ≥0) :
    Integrable (oneStep H s t) sourceLaw :=
  (oneStep_memLp_two hH s t).integrable (by norm_num)

theorem oneStep_square_integrable {H : (ℝ≥0 → ℝ) → ℝ} (hH : MemLp H ∞ sourceLaw) (s t : ℝ≥0) :
    Integrable (fun ω => oneStep H s t ω ^ 2) sourceLaw :=
  (oneStep_memLp_two hH s t).integrable_sq

/-- At the interval end the actual returned output is naturally measurable;
this is the precise permission needed by a later nonoverlapping interval. -/
theorem oneStep_stronglyMeasurable_end {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) :
    StronglyMeasurable[naturalFiltration t] (oneStep H s t) :=
  (hHpast.mono (naturalFiltration.mono hst)).mul
    ((process_stronglyAdapted t).sub ((process_stronglyAdapted s).mono (naturalFiltration.mono hst)))

/-- Only past-measurable coefficients may be pulled out. Neither future
measurability nor independence of a scalar observation replaces this permission. -/
theorem oneStep_condExp_zero {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ sourceLaw) :
    sourceLaw[oneStep H s t | naturalFiltration s] =ᵐ[sourceLaw] fun _ => 0 := by
  apply (condExp_mul_of_stronglyMeasurable_left hHpast (oneStep_integrable hH s t)
    (increment_integrable s t)).trans
  filter_upwards [condExp_increment_zero s t hst] with ω hω
  simp only [Pi.mul_apply,hω,mul_zero]

/-- Source-derived conditional variance of the literal returned one-step
integral, with the actual elapsed-time clock. -/
theorem oneStep_condExp_square {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ sourceLaw) :
    sourceLaw[fun ω => oneStep H s t ω ^ 2 | naturalFiltration s] =ᵐ[sourceLaw]
      fun ω => H ω ^ 2 * ((t : ℝ)-(s : ℝ)) := by
  have he : (fun ω => oneStep H s t ω ^ 2) =
      (fun ω => H ω ^ 2) * (fun ω => increment s t ω ^ 2) := by
    funext ω
    simp only [oneStep,Pi.mul_apply,mul_pow]
  have hi : Integrable ((fun ω => H ω ^ 2) * (fun ω => increment s t ω ^ 2)) sourceLaw := by
    rw [← he]
    exact oneStep_square_integrable hH s t
  rw [he]
  apply (condExp_mul_of_stronglyMeasurable_left (hHpast.pow 2) hi
    (increment_square_integrable s t)).trans
  filter_upwards [condExp_increment_square s t hst] with ω hω
  simp only [Pi.mul_apply,Pi.pow_apply,hω]

theorem oneStep_mean_zero {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ sourceLaw) :
    (∫ ω, oneStep H s t ω ∂sourceLaw) = 0 := by
  rw [← integral_condExp (naturalFiltration.le s)]
  rw [integral_congr_ae (oneStep_condExp_zero s t hst hHpast hH),integral_zero]

/-- Exact one-step Ito isometry, derived for this actual source. It is not a
general stochastic-integral construction or a general Ito-formula claim. -/
theorem oneStep_isometry {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ sourceLaw) :
    (∫ ω, oneStep H s t ω ^ 2 ∂sourceLaw) =
      ((t : ℝ)-(s : ℝ)) * (∫ ω, H ω ^ 2 ∂sourceLaw) := by
  rw [← integral_condExp (naturalFiltration.le s)]
  rw [integral_congr_ae (oneStep_condExp_square s t hst hHpast hH),integral_mul_const,mul_comm]

/-- Nondegenerate witness from the same clock and source: the actual unit
coefficient on [0,1] produces second moment exactly one. -/
theorem unit_oneStep_second_moment :
    (∫ ω, oneStep (fun _ => 1) 0 1 ω ^ 2 ∂sourceLaw) = 1 := by
  rw [oneStep_isometry 0 1 (by norm_num) stronglyMeasurable_const (memLp_top_const 1)]
  simp

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOneStepIntegral
