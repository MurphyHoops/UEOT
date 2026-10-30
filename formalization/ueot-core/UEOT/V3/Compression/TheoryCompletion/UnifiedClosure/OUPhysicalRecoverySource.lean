import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalConditionalKernelSource

/-!
Original commitment: original recovery must consume SAME actually driven restoring physical OU, not only a separate timechanged law.
Existing result: physical integral equation and whole ORIGINAL-Fs transition kernel are derived on the same canonical B/P.
Premise reduced: derive physical actual law/moments/Dynkin certificate and feed ORIGINAL p_rec_02; identity-reuse valid old quadratic analytic results.
Model/witness: physical state k>0, any noise/initial state, all finite nonnegative horizons, genuine sigma≠0 positive transition uncertainty.
Consumer/boundary: ORIGINAL RecoveryDynkin.p_rec_02; no samplewise equality with timechangedOU, no general nonlinear-SDE existence/uniqueness or arbitrary-filtered source claim.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalRecoverySource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open OUPhysicalVolterraSource OUPhysicalConditionalKernelSource OUConditionalInnovationSource OUTransitionKernelSource OUSemigroupSource OUQuadraticDynkinSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def physicalLaw (k σ x₀ t : ℝ) : Measure ℝ := sourceLaw.map (state k σ x₀ (Real.toNNReal t))

/-- Literal fixed initial state pushes forward to the original Dirac law. -/
theorem physicalLaw_initial (k σ x₀ : ℝ) : physicalLaw k σ x₀ 0=Measure.dirac x₀ := by
  unfold physicalLaw
  have he : state k σ x₀ (Real.toNNReal 0)=(fun _ : ℝ≥0→ℝ=>x₀) := by
    funext ω
    simpa only [Real.toNNReal_zero,NNReal.coe_zero] using state_initial k σ x₀ ω
  rw[he]
  simp

theorem physical_hasLaw (k σ x₀ : ℝ) (hk : 0<k) (t : ℝ≥0) :
    HasLaw (state k σ x₀ t) (transitionKernel k σ 0 t x₀) sourceLaw := by
  rw[transitionKernel_apply]
  have h:=gaussianReal_const_add (physicalInnovation_hasLaw k σ hk 0 t (by positivity)) (decay k 0 t*x₀)
  rw[zero_add] at h
  apply h.congr
  filter_upwards [] with ω
  rw[physical_transition_decomposition k σ x₀ hk.le 0 t (by positivity)]
  simp only [NNReal.coe_zero,state_initial]

/-- This is a law identity proved from actual physical mechanism/conditional
noise. It is deliberately NOT an identity between the two sample paths. -/
theorem physicalLaw_eq_existing_ouLaw (k σ x₀ : ℝ) (hk : 0<k) (t : ℝ) :
    physicalLaw k σ x₀ t=ouLaw sourceLaw process k σ x₀ t :=
  (physical_hasLaw k σ x₀ hk (Real.toNNReal t)).map_eq.trans (actualOU_hasLaw k σ x₀ (Real.toNNReal t)).map_eq.symm

theorem physicalLaw_probability (k σ x₀ t : ℝ) : IsProbabilityMeasure (physicalLaw k σ x₀ t) :=
  Measure.isProbabilityMeasure_map (((state_stronglyAdapted k σ x₀ (Real.toNNReal t)).mono (naturalFiltration.le _)).measurable.aemeasurable)

theorem physicalLaw_quadratic_integrable (k σ x₀ t : ℝ) (hk : 0<k) :
    Integrable (fun x : ℝ=>x^2) (physicalLaw k σ x₀ t) := by
  rw[physicalLaw_eq_existing_ouLaw k σ x₀ hk]
  exact ou_law_quadratic_integrable process_isPreBrownian k σ x₀ t

theorem physicalLaw_quadratic_moment (k σ x₀ t : ℝ) (hk : 0<k) (ht : 0≤t) :
    (∫ x,x^2 ∂physicalLaw k σ x₀ t)=quadraticMean k σ x₀ t := by
  rw[physicalLaw_eq_existing_ouLaw k σ x₀ hk]
  exact ou_law_quadratic_moment process_isPreBrownian k σ x₀ hk t ht

theorem physicalLaw_expected_generator (k σ x₀ t : ℝ) (hk : 0<k) :
    (∫ x,quadraticGenerator k σ x ∂physicalLaw k σ x₀ t)=-2*k*(∫ x,x^2 ∂physicalLaw k σ x₀ t)+σ^2 := by
  rw[physicalLaw_eq_existing_ouLaw k σ x₀ hk]
  exact ou_law_expected_generator process_isPreBrownian k σ x₀ t

/-- The ORIGINAL certificate is actually constructed for this physical
pushforward. Existing exact same law/analytic quadratic derivation is reused. -/
theorem physical_quadratic_dynkin (k σ x₀ T : ℝ) (hk : 0<k) (hT : 0≤T) :
    UEOT.V3.RecoveryDynkin.DynkinExpectationCertificate
      (fun t=>∫ x,x^2 ∂physicalLaw k σ x₀ t)
      (fun t=>∫ x,quadraticGenerator k σ x ∂physicalLaw k σ x₀ t) T := by
  simpa only[physicalLaw_eq_existing_ouLaw k σ x₀ hk] using ou_quadratic_dynkin process_isPreBrownian k σ x₀ T hk hT

/-- ORIGINAL p_rec_02 now consumes the actual PHYSICAL source law and its
source-derived certificate, with the original positive restoring/noise floor. -/
theorem physical_source_p_rec_02 (k σ x₀ T : ℝ) (hk : 0<k) (hT : 0≤T) :
    ∀ t ∈Icc 0 T,(∫ x,x^2 ∂physicalLaw k σ x₀ t)≤
      Real.exp (-(2*k)*t)*x₀^2+σ^2/(2*k)*(1-Real.exp (-(2*k)*t)) := by
  suffices H : ∀ t ∈Icc 0 T,(∫ x,x^2 ∂physicalLaw k σ x₀ t)≤
      (Real.exp (-(2*k)*t)*x₀^2+σ^2/(2*k)*(1-Real.exp (-(2*k)*t)))/1 by simpa only[div_one] using H
  apply UEOT.V3.RecoveryDynkin.p_rec_02 (physicalLaw k σ x₀) (fun x=>x^2) (quadraticGenerator k σ) (fun x=>x^2) x₀
    (2*k) (σ^2) 1 T (by positivity) (sq_nonneg _) (by norm_num) hT
  · intro t _;exact physicalLaw_probability k σ x₀ t
  · intro t _;exact physicalLaw_quadratic_integrable k σ x₀ t hk
  · intro t _
    let := physicalLaw_probability k σ x₀ t
    exact ((physicalLaw_quadratic_integrable k σ x₀ t hk).const_mul _).add (integrable_const _)
  · intro t _;exact physicalLaw_quadratic_integrable k σ x₀ t hk
  · exact physical_quadratic_dynkin k σ x₀ T hk hT
  · rw[physicalLaw_quadratic_moment k σ x₀ 0 hk (by norm_num)]
    simp[quadraticMean]
  · intro x;dsimp[quadraticGenerator];ring_nf;rfl
  · intro x;simp

theorem physical_positive_transition_noise (k σ : ℝ) (hk : 0<k) (hσ : σ≠0) (s t : ℝ≥0) (hst : s<t) :
    0<(transitionVariance k σ s t : ℝ) := transitionVariance_pos k σ hk hσ s t hst

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalRecoverySource
