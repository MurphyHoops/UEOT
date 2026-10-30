import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalTransitionSource

/-!
Original commitment: SAME physical restoring OU must consume original transition kernel under its original physical Brownian past.
Existing result: pathwise elapsed physical transition and actual measurable Gaussian future-noise law/whole original-Fs independence.
Premise reduced: derive actual physical innovation variance, disintegration and bounded-Borel conditional kernel, not an input conditional-law field.
Model/witness: SAME P/B/state, original naturalFiltration, k>0, arbitrary sigma/x0 and s≤t incl equal/zero clocks and zero noise.
Consumer/boundary: physical original P-REC-02 chain; law matches original kernel, but old timechanged state and physical state are not samplewise identified.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalConditionalKernelSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open OUPhysicalVolterraSource OUPhysicalFutureNoise OUPhysicalTransitionSource OUConditionalInnovationSource OUQuadraticDynkinSource OUTransitionKernelSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def physicalInnovation (k σ : ℝ) (s t : ℝ≥0) (ω : ℝ≥0→ℝ) : ℝ :=
  (Real.exp (-k*(t-s : ℝ≥0))*σ)*futureNoise k s (t-s) ω

theorem physicalInnovation_measurable (k σ : ℝ) (s t : ℝ≥0) : Measurable (physicalInnovation k σ s t) :=
  measurable_const.mul (futureNoise_measurable k s (t-s))

theorem physical_transition_decomposition (k σ x₀ : ℝ) (hk : 0≤k) (s t : ℝ≥0) (hst : s≤t) (ω : ℝ≥0→ℝ) :
    state k σ x₀ t ω=decay k s t*state k σ x₀ s ω+physicalInnovation k σ s t ω := by
  have h:=physical_elapsed_transition k σ x₀ hk s (t-s) ω
  rw[NNReal.coe_sub hst,add_sub_cancel] at h
  simpa only[physicalInnovation,decay,NNReal.coe_sub hst] using h

private theorem transitionVariance_elapsed (k σ : ℝ) (hk : 0<k) (s t : ℝ≥0) (hst : s≤t) :
    transitionVariance k σ 0 (t-s)=transitionVariance k σ s t := by
  apply NNReal.coe_injective
  rw[transitionVariance_coe k σ hk 0 (t-s) (by positivity),transitionVariance_coe k σ hk s t hst,
    NNReal.coe_sub hst,NNReal.coe_zero,sub_zero]

/-- Same physical future noise, scaled by its actual decay, has precisely
THE ORIGINAL kernel's variance; no fitted or desired Gaussian law is entered. -/
theorem physicalInnovation_hasLaw (k σ : ℝ) (hk : 0<k) (s t : ℝ≥0) (hst : s≤t) :
    HasLaw (physicalInnovation k σ s t) (gaussianReal 0 (transitionVariance k σ s t)) sourceLaw := by
  have h:=gaussianReal_const_mul (futureNoise_hasLaw k hk s (t-s)) (Real.exp (-k*(t-s : ℝ≥0))*σ)
  have hv : (NNReal.mk ((Real.exp (-k*(t-s : ℝ≥0))*σ)^2) (sq_nonneg _))*ouClock k (t-s)=transitionVariance k σ s t := by
    rw[←transitionVariance_elapsed k σ hk s t hst]
    unfold transitionVariance
    congr 1
    apply NNReal.coe_injective
    have hc0 : ouClock k 0=0 := by simp [ouClock]
    rw[coe_nndist,Real.dist_eq,hc0,NNReal.coe_zero,sub_zero,abs_of_nonneg (ouClock k (t-s)).coe_nonneg]
  change HasLaw (fun ω=>(Real.exp (-k*(t-s : ℝ≥0))*σ)*futureNoise k s (t-s) ω)
    (gaussianReal 0 (transitionVariance k σ s t)) sourceLaw
  simpa only[mul_zero,hv] using h

theorem physicalInnovation_indep_whole_past (k σ : ℝ) (s t : ℝ≥0) :
    IndepFun (physicalInnovation k σ s t) (fun ω (r : Iic s)=>process r ω) sourceLaw :=
  (futureNoise_indep_whole_past k s (t-s)).comp (measurable_const.mul measurable_id) measurable_id

/-- Actual disintegration under ENTIRE ORIGINAL physical Fs, retaining arbitrary past observations. -/
theorem physicalInnovation_condDistrib (k σ : ℝ) (hk : 0<k) (s t : ℝ≥0) (hst : s≤t) :
    @condDistrib (ℝ≥0→ℝ) (ℝ≥0→ℝ) ℝ inferInstance inferInstance inferInstance
      inferInstance (naturalFiltration s) (physicalInnovation k σ s t) id sourceLaw inferInstance
    =ᵐ[@Measure.map (ℝ≥0→ℝ) (ℝ≥0→ℝ) inferInstance (naturalFiltration s) id sourceLaw]
      @Kernel.const (ℝ≥0→ℝ) ℝ (naturalFiltration s) inferInstance (gaussianReal 0 (transitionVariance k σ s t)) := by
  have hid : @Measurable (ℝ≥0→ℝ) (ℝ≥0→ℝ) inferInstance (naturalFiltration s) id := measurable_id'' (naturalFiltration.le s)
  have hida : @AEMeasurable (ℝ≥0→ℝ) (ℝ≥0→ℝ) (naturalFiltration s) inferInstance id sourceLaw :=
    ⟨id,hid,Eventually.of_forall (fun _=>rfl)⟩
  have hi : Indep (MeasurableSpace.comap (physicalInnovation k σ s t) inferInstance) (naturalFiltration s) sourceLaw := by
    rw[naturalFiltration,Filtration.natural_eq_comap]
    exact physicalInnovation_indep_whole_past k σ s t
  have hi' : @IndepFun (ℝ≥0→ℝ) (ℝ≥0→ℝ) ℝ inferInstance (naturalFiltration s) inferInstance id (physicalInnovation k σ s t) sourceLaw := by
    change Indep (MeasurableSpace.comap id (naturalFiltration s)) (MeasurableSpace.comap (physicalInnovation k σ s t) inferInstance) sourceLaw
    rw[MeasurableSpace.comap_id]
    exact hi.symm
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hid (physicalInnovation_measurable k σ s t)
  rw[Measure.compProd_const,←(physicalInnovation_hasLaw k σ hk s t hst).map_eq]
  exact @IndepFun.map_prod_eq_prod_map_map (ℝ≥0→ℝ) (ℝ≥0→ℝ) ℝ inferInstance sourceLaw id (physicalInnovation k σ s t)
    (naturalFiltration s) inferInstance inferInstance hida (physicalInnovation_measurable k σ s t).aemeasurable hi'

/-- The ORIGINAL kernel now describes the actual PHYSICAL restoring state,
conditioned on the WHOLE original Brownian physical past. -/
theorem physical_condExp_kernel (k σ x₀ : ℝ) (hk : 0<k) (s t : ℝ≥0) (hst : s≤t)
    (φ : ℝ→ℝ) (hφ : Measurable φ) (K : ℝ) (hb : ∀ x,‖φ x‖≤K) :
    sourceLaw[fun ω=>φ (state k σ x₀ t ω)|naturalFiltration s]=ᵐ[sourceLaw]
      fun ω=>∫y,φ y ∂transitionKernel k σ s t (state k σ x₀ s ω) := by
  have hid : @Measurable (ℝ≥0→ℝ) (ℝ≥0→ℝ) inferInstance (naturalFiltration s) id := measurable_id'' (naturalFiltration.le s)
  have hida : @AEMeasurable (ℝ≥0→ℝ) (ℝ≥0→ℝ) (naturalFiltration s) inferInstance id sourceLaw :=
    ⟨id,hid,Eventually.of_forall (fun _=>rfl)⟩
  let F : (ℝ≥0→ℝ)×ℝ→ℝ := fun p=>φ (decay k s t*state k σ x₀ s p.1+p.2)
  have hF : @StronglyMeasurable ((ℝ≥0→ℝ)×ℝ) ℝ inferInstance ((naturalFiltration s).prod inferInstance) F :=
    (hφ.comp ((measurable_const.mul ((state_stronglyAdapted k σ x₀ s).measurable.comp measurable_fst)).add measurable_snd)).stronglyMeasurable
  have hU : Measurable (state k σ x₀ s) := ((state_stronglyAdapted k σ x₀ s).mono (naturalFiltration.le s)).measurable
  have hFi : Integrable (fun ω=>F (id ω,physicalInnovation k σ s t ω)) sourceLaw := by
    apply (integrable_const K).mono' (hφ.comp ((measurable_const.mul hU).add (physicalInnovation_measurable k σ s t))).aestronglyMeasurable
    exact Eventually.of_forall (fun ω=>hb _)
  have hc:=condExp_prod_ae_eq_integral_condDistrib hid (physicalInnovation_measurable k σ s t).aemeasurable hF hFi
  rw[MeasurableSpace.comap_id] at hc
  have hker:=@ae_of_ae_map (ℝ≥0→ℝ) (ℝ≥0→ℝ) inferInstance (naturalFiltration s) sourceLaw id hida _
    (physicalInnovation_condDistrib k σ hk s t hst)
  have he : (fun ω=>F (id ω,physicalInnovation k σ s t ω))=(fun ω=>φ (state k σ x₀ t ω)) := by
    funext ω
    exact congrArg φ (physical_transition_decomposition k σ x₀ hk.le s t hst ω).symm
  rw[he] at hc
  filter_upwards[hc,hker] with ω hc hker
  rw[hker] at hc
  exact hc.trans (transitionKernel_integral k σ s t φ hφ (state k σ x₀ s ω)).symm

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalConditionalKernelSource
