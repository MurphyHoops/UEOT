import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianSimplePredictableIntegral

/-!
Original commitment: Ito's second-order clock term must come from actual source increment squares.
Existing result: SAME actual scalar continuous Brownian source, Gaussian fourth moment and natural-past independence.
Premise reduced: derive past-weighted centered squared-increment conditional moments and nonoverlap orthogonality.
Model/witness: scalar canonical sourceLaw/process/original naturalFiltration, deterministic s ≤ t, bounded H sees only Fs.
Consumer: actual partition quadratic variation and weighted compensator limits; vector/general filtered Ito remains open.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianQuadraticVariationSteps
open MeasureTheory ProbabilityTheory Set
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource BrownianOneStepIntegral
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- The Gaussian fourth moment belongs to the SAME actual continuous version,
by its proved fixed-time equality to the original canonical coordinates. -/
theorem increment_fourth_mean (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, increment s t ω ^ 4 ∂sourceLaw) = 3*((t : ℝ)-(s : ℝ))^2 := by
  have he : (fun ω => increment s t ω ^ 4) =ᵐ[sourceLaw] (fun ω => (ω t-ω s)^4) := by
    filter_upwards [process_eq_coordinate_ae s,process_eq_coordinate_ae t] with ω hs ht
    simp only [increment,hs,ht]
  rw [integral_congr_ae he,source_increment_fourth_moment]
  rw [coe_nndist,NNReal.dist_eq,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hst))]

theorem increment_memLp_four (s t : ℝ≥0) : MemLp (increment s t) 4 sourceLaw :=
  (process_isPreBrownian.hasLaw_sub t s).hasGaussianLaw.memLp (by norm_num)

theorem increment_fourth_integrable (s t : ℝ≥0) : Integrable (fun ω => increment s t ω ^ 4) sourceLaw := by
  simpa only [Real.norm_eq_abs,Even.pow_abs (by decide : Even (4 : ℕ))] using
    (increment_memLp_four s t).integrable_norm_pow (by decide : (4 : ℕ) ≠ 0)

/-- Actual centered square error, not a supplied quadratic variation value. -/
def centeredSquare (s t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  increment s t ω ^ 2-((t : ℝ)-(s : ℝ))

theorem centeredSquare_memLp_two (s t : ℝ≥0) : MemLp (centeredSquare s t) 2 sourceLaw := by
  have hs : MemLp (fun ω => increment s t ω ^ 2) 2 sourceLaw := by
    apply (memLp_two_iff_integrable_sq ((measurable_increment s t).pow_const 2).aestronglyMeasurable).mpr
    simpa only [← pow_mul] using increment_fourth_integrable s t
  exact hs.sub (memLp_const _)

theorem centeredSquare_condExp_zero (s t : ℝ≥0) (hst : s ≤ t) :
    sourceLaw[centeredSquare s t | naturalFiltration s] =ᵐ[sourceLaw] fun _ => 0 := by
  have hs := condExp_sub (increment_square_integrable s t)
    (integrable_const ((t : ℝ)-(s : ℝ))) (naturalFiltration s)
  apply hs.trans
  rw [condExp_const (naturalFiltration.le s)]
  filter_upwards [condExp_increment_square s t hst] with ω hω
  simp only [Pi.sub_apply,hω,sub_self]

theorem centeredSquare_variance (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, centeredSquare s t ω ^ 2 ∂sourceLaw) = 2*((t : ℝ)-(s : ℝ))^2 := by
  have he : (fun ω => centeredSquare s t ω ^ 2) =
      (fun ω => increment s t ω ^ 4) -
        (fun ω => 2*((t : ℝ)-(s : ℝ))*increment s t ω ^ 2) +
        (fun _ => ((t : ℝ)-(s : ℝ))^2) := by
    ext ω
    simp only [Pi.add_apply,Pi.sub_apply,centeredSquare]
    ring
  rw [he]
  change (∫ ω, (increment s t ω ^ 4-2*((t : ℝ)-(s : ℝ))*increment s t ω ^ 2)+((t : ℝ)-(s : ℝ))^2 ∂sourceLaw) = _
  have hlin : Integrable (fun ω => 2*((t : ℝ)-(s : ℝ))*increment s t ω ^ 2) sourceLaw :=
    (increment_square_integrable s t).const_mul _
  rw [integral_add (f := fun ω => increment s t ω ^ 4-2*((t : ℝ)-(s : ℝ))*increment s t ω ^ 2)
    (g := fun _ => ((t : ℝ)-(s : ℝ))^2) ((increment_fourth_integrable s t).sub hlin) (integrable_const _),
    integral_sub (increment_fourth_integrable s t) hlin,
    integral_const_mul,increment_fourth_mean s t hst,increment_square_mean s t hst]
  simp only [integral_const,probReal_univ,one_smul]
  ring

theorem centeredSquare_condExp_square (s t : ℝ≥0) (hst : s ≤ t) :
    sourceLaw[fun ω => centeredSquare s t ω ^ 2 | naturalFiltration s] =ᵐ[sourceLaw]
      fun _ => 2*((t : ℝ)-(s : ℝ))^2 := by
  exact (condExp_increment_function s t hst (fun x => (x^2-((t : ℝ)-(s : ℝ)))^2) (by fun_prop)).trans
    (ae_of_all sourceLaw (fun _ => centeredSquare_variance s t hst))

/-- Actual permitted predictable weight multiplying the actual source's
centered square; no future coefficient or covariance certificate is supplied. -/
def weightedError (H : (ℝ≥0 → ℝ) → ℝ) (s t : ℝ≥0) : (ℝ≥0 → ℝ) → ℝ := H * centeredSquare s t

theorem weightedError_memLp_two {H : (ℝ≥0 → ℝ) → ℝ} (hH : MemLp H ∞ sourceLaw) (s t : ℝ≥0) :
    MemLp (weightedError H s t) 2 sourceLaw :=
  (centeredSquare_memLp_two s t).mul hH

theorem weightedError_stronglyMeasurable_end {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) :
    StronglyMeasurable[naturalFiltration t] (weightedError H s t) :=
  (hHpast.mono (naturalFiltration.mono hst)).mul
    ((((process_stronglyAdapted t).sub ((process_stronglyAdapted s).mono
      (naturalFiltration.mono hst))).pow 2).sub stronglyMeasurable_const)

theorem weightedError_condExp_zero {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ sourceLaw) :
    sourceLaw[weightedError H s t | naturalFiltration s] =ᵐ[sourceLaw] fun _ => 0 := by
  apply (condExp_mul_of_stronglyMeasurable_left hHpast
    ((weightedError_memLp_two hH s t).integrable one_le_two)
    ((centeredSquare_memLp_two s t).integrable one_le_two)).trans
  filter_upwards [centeredSquare_condExp_zero s t hst] with ω hω
  simp only [Pi.mul_apply,hω,mul_zero]

theorem weightedError_condExp_square {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ sourceLaw) :
    sourceLaw[fun ω => weightedError H s t ω ^ 2 | naturalFiltration s] =ᵐ[sourceLaw]
      fun ω => H ω ^ 2 * (2*((t : ℝ)-(s : ℝ))^2) := by
  have he : (fun ω => weightedError H s t ω ^ 2) =
      (fun ω => H ω ^ 2) * (fun ω => centeredSquare s t ω ^ 2) := by
    ext ω
    simp only [weightedError,Pi.mul_apply,mul_pow]
  have hi : Integrable ((fun ω => H ω ^ 2) * (fun ω => centeredSquare s t ω ^ 2)) sourceLaw := by
    rw [← he]
    exact (weightedError_memLp_two hH s t).integrable_sq
  rw [he]
  apply (condExp_mul_of_stronglyMeasurable_left (hHpast.pow 2) hi
    (centeredSquare_memLp_two s t).integrable_sq).trans
  filter_upwards [centeredSquare_condExp_square s t hst] with ω hω
  simp only [Pi.mul_apply,Pi.pow_apply,hω]

theorem weightedError_variance {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ sourceLaw) :
    (∫ ω, weightedError H s t ω ^ 2 ∂sourceLaw) =
      (2*((t : ℝ)-(s : ℝ))^2) * (∫ ω, H ω ^ 2 ∂sourceLaw) := by
  rw [← integral_condExp (naturalFiltration.le s),
    integral_congr_ae (weightedError_condExp_square s t hst hHpast hH),integral_mul_const,mul_comm]

theorem weightedError_mean_zero {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ sourceLaw) :
    (∫ ω, weightedError H s t ω ∂sourceLaw) = 0 := by
  rw [← integral_condExp (naturalFiltration.le s),
    integral_congr_ae (weightedError_condExp_zero s t hst hHpast hH),integral_zero]

/-- Orthogonality is derived from original END/START permissions and actual
conditional mean zero, including touching or zero-length intervals. -/
theorem weightedError_nonoverlap {H K : (ℝ≥0 → ℝ) → ℝ} (s t u v : ℝ≥0)
    (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hKpast : StronglyMeasurable[naturalFiltration u] K)
    (hH : MemLp H ∞ sourceLaw) (hK : MemLp K ∞ sourceLaw) :
    (∫ ω, weightedError H s t ω * weightedError K u v ω ∂sourceLaw) = 0 := by
  have hi := (weightedError_memLp_two hH s t).integrable_mul (weightedError_memLp_two hK u v)
  have hm := (weightedError_stronglyMeasurable_end s t hst hHpast).mono (naturalFiltration.mono htu)
  have hc := condExp_mul_of_stronglyMeasurable_left hm hi
    ((weightedError_memLp_two hK u v).integrable one_le_two)
  have hz : sourceLaw[weightedError H s t * weightedError K u v | naturalFiltration u] =ᵐ[sourceLaw] fun _ => 0 := by
    apply hc.trans
    filter_upwards [weightedError_condExp_zero u v huv hKpast hK] with ω hω
    simp only [Pi.mul_apply,hω,mul_zero]
  simp only [Pi.mul_def] at hz
  rw [← integral_condExp (naturalFiltration.le u),integral_congr_ae hz,integral_zero]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianQuadraticVariationSteps
