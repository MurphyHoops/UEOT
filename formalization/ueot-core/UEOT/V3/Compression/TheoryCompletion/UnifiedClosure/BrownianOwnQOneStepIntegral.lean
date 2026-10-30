import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedGirsanovSource

/-!
Original commitment: controlled-source integration must use the actual shifted noise under its OWN normalized measure.
Existing result: SAME bounded full input constructs Q and W, with Gaussian increments independent of ENTIRE original Fs past.
Premise reduced: derive actual Q conditional variance and bounded START coefficient one-step conditional moments/isometry.
Model/witness: original Fs permissions, actual W_f and Q_f, arbitrary ordered deterministic times including repeated/zero clocks.
Consumer/boundary: actual Q finite predictable integral; original P integral is not relabeled and general Q extension/Ito stay separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQOneStepIntegral
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs
open BrownianBoundedControlSource BrownianBoundedExponentialLimitSource BrownianBoundedGirsanovSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
private theorem gaussian_second_moment (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal 0 v)=(v : ℝ) := by
  have h := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa only [id_eq,integral_id_gaussianReal,sub_zero] using h

variable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K)

/-- Literal returned integral against actual Q-Brownian increments. -/
def oneStep (H : (ℝ≥0 → ℝ) → ℝ) (s t : ℝ≥0) : (ℝ≥0 → ℝ) → ℝ :=
  H*fullIncrement T f K s t

include hK hbound

/-- Existing original source-bounded permitted coefficients remain bounded
under this actual Q by absolute continuity, not a new coefficient field. -/
theorem coefficient_bounded_Q {H : (ℝ≥0 → ℝ) → ℝ} (hH : MemLp H ∞ sourceLaw) :
    MemLp H ∞ (fullLaw T f) := by
  let _ := fullLaw_probability T f K hK hbound
  obtain ⟨C,hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
    (show eLpNormEssSup H sourceLaw<⊤ by simpa only [eLpNorm_exponent_top] using hH.2)
  apply MemLp.of_bound (hH.aestronglyMeasurable.mono_ac (fullLaw_absolutelyContinuous T f)) (C : ℝ)
  have hP : ∀ᵐ ω ∂sourceLaw, ‖H ω‖₊≤C := hC
  filter_upwards [(fullLaw_absolutelyContinuous T f).ae_le hP] with ω h
  exact_mod_cast h

theorem increment_memLp_two (s t : ℝ≥0) : MemLp (fullIncrement T f K s t) 2 (fullLaw T f) :=
  (full_isPreBrownian T f K hK hbound).hasLaw_sub t s |>.hasGaussianLaw.memLp_two


theorem increment_square_mean (s t : ℝ≥0) (hst : s≤t) :
    (∫ ω, fullIncrement T f K s t ω^2 ∂fullLaw T f)=(t : ℝ)-(s : ℝ) := by
  calc
    _ = ∫ x : ℝ, x^2 ∂gaussianReal 0 (nndist (t : ℝ) (s : ℝ)) :=
      ((full_isPreBrownian T f K hK hbound).hasLaw_sub t s).integral_comp (by fun_prop)
    _ = (nndist (t : ℝ) (s : ℝ) : ℝ) := gaussian_second_moment _
    _ = _ := by
      rw [coe_nndist,Real.dist_eq,abs_of_nonneg]
      exact sub_nonneg.mpr (by exact_mod_cast hst)

theorem increment_condExp_square (s t : ℝ≥0) (hst : s≤t) :
    (fullLaw T f)[fun ω => fullIncrement T f K s t ω^2 | naturalFiltration s]=ᵐ[fullLaw T f]
      fun _ => (t : ℝ)-(s : ℝ) := by
  let _ := fullLaw_probability T f K hK hbound
  have hi : Indep (MeasurableSpace.comap (fullIncrement T f K s t) inferInstance) (naturalFiltration s) (fullLaw T f) := by
    rw [naturalFiltration,Filtration.natural_eq_comap]
    exact full_increment_indep_original_past T f K hK hbound s t hst
  have hm : @Measurable (ℝ≥0 → ℝ) ℝ (MeasurableSpace.comap (fullIncrement T f K s t) inferInstance)
      inferInstance (fullIncrement T f K s t) := measurable_iff_comap_le.mpr le_rfl
  have hg : Measurable (fullIncrement T f K s t) :=
    ((shiftedProcess_stronglyAdapted T f K t).mono (naturalFiltration.le t)).measurable.sub
      ((shiftedProcess_stronglyAdapted T f K s).mono (naturalFiltration.le s)).measurable
  have h := condExp_indep_eq hg.comap_le (naturalFiltration.le s) (hm.pow_const 2).stronglyMeasurable hi
  exact h.trans (Eventually.of_forall (fun _ => increment_square_mean T f K hK hbound s t hst))

theorem oneStep_memLp_two {H : (ℝ≥0 → ℝ) → ℝ} (hH : MemLp H ∞ (fullLaw T f)) (s t : ℝ≥0) :
    MemLp (oneStep T f K H s t) 2 (fullLaw T f) :=
  (increment_memLp_two T f K hK hbound s t).mul hH

omit hK hbound in
theorem oneStep_past_end {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s≤t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) :
    StronglyMeasurable[naturalFiltration t] (oneStep T f K H s t) :=
  (hHpast.mono (naturalFiltration.mono hst)).mul
    ((shiftedProcess_stronglyAdapted T f K t).sub
      ((shiftedProcess_stronglyAdapted T f K s).mono (naturalFiltration.mono hst)))

/-- START-only measurability is essential. This theorem does not grant
permission to coefficients observing the future increment. -/
theorem oneStep_condExp_zero {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s≤t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ (fullLaw T f)) :
    (fullLaw T f)[oneStep T f K H s t | naturalFiltration s]=ᵐ[fullLaw T f] fun _ => 0 := by
  let _ := fullLaw_probability T f K hK hbound
  apply (condExp_mul_of_stronglyMeasurable_left hHpast
    ((oneStep_memLp_two T f K hK hbound hH s t).integrable one_le_two)
    ((increment_memLp_two T f K hK hbound s t).integrable one_le_two)).trans
  filter_upwards [full_increment_condExp_zero T f K hK hbound s t hst] with ω h
  simp only [Pi.mul_apply,h,mul_zero]

theorem oneStep_condExp_square {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s≤t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ (fullLaw T f)) :
    (fullLaw T f)[fun ω => oneStep T f K H s t ω^2 | naturalFiltration s]=ᵐ[fullLaw T f]
      fun ω => H ω^2*((t : ℝ)-(s : ℝ)) := by
  let _ := fullLaw_probability T f K hK hbound
  have he : (fun ω => oneStep T f K H s t ω^2)=(fun ω => H ω^2)*(fun ω => fullIncrement T f K s t ω^2) := by
    funext ω
    simp only [oneStep,Pi.mul_apply,mul_pow]
  have hi : Integrable ((fun ω => H ω^2)*(fun ω => fullIncrement T f K s t ω^2)) (fullLaw T f) := by
    rw [← he]
    exact (oneStep_memLp_two T f K hK hbound hH s t).integrable_sq
  rw [he]
  apply (condExp_mul_of_stronglyMeasurable_left (hHpast.pow 2) hi
    (increment_memLp_two T f K hK hbound s t).integrable_sq).trans
  filter_upwards [increment_condExp_square T f K hK hbound s t hst] with ω h
  simp only [Pi.mul_apply,Pi.pow_apply,h]

theorem oneStep_mean_zero {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s≤t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ (fullLaw T f)) :
    (∫ ω, oneStep T f K H s t ω ∂fullLaw T f)=0 := by
  let _ := fullLaw_probability T f K hK hbound
  rw [← integral_condExp (naturalFiltration.le s)]
  rw [integral_congr_ae (oneStep_condExp_zero T f K hK hbound s t hst hHpast hH),integral_zero]

/-- Actual one-step isometry under OWN final measure and ORIGINAL past. -/
theorem oneStep_isometry {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0) (hst : s≤t)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ (fullLaw T f)) :
    (∫ ω, oneStep T f K H s t ω^2 ∂fullLaw T f)=((t : ℝ)-(s : ℝ))*(∫ ω, H ω^2 ∂fullLaw T f) := by
  let _ := fullLaw_probability T f K hK hbound
  rw [← integral_condExp (naturalFiltration.le s)]
  rw [integral_congr_ae (oneStep_condExp_square T f K hK hbound s t hst hHpast hH),integral_mul_const,mul_comm]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQOneStepIntegral
