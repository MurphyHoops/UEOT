import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTargetIntegral

/-!
Original commitment: one actual control run must use a FIXED probability law at every read/integration horizon.
Existing result: fixed ownQ_b/W_b has original Fs moments for ALL times and native dtU×Q elementary integral for every U.
Premise reduced: derive actual bounded original-predictable target-g membership/integration on arbitrary U while density horizon A and Q_b remain FIXED.
Model/witness: source b,K on A; test g,L on U with original Fs permissions, no ordering of A,U and no Lp cross-horizon transport; both zero boundaries retained.
Consumer/boundary: same-Q controlled C2 at all read times, discounting/occupation/infiniteReward; neither full-Q predictable density nor source ItoRun is supplied.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQHorizonTargetIntegral
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianBoundedPredictableApproximation BrownianBoundedControlSource
open BrownianBoundedExponentialLimitSource BrownianOwnQTimeInput BrownianOwnQIntegralClosure BrownianOwnQBoundedInput
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory InnerProductSpace RealInnerProductSpace
noncomputable section
variable (A : ℝ≥0) (b : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw A, |(b : Lp ℝ 2 (inputLaw A)) p|≤K)
    (U : ℝ≥0) (g : fullPredictableL2 U) (L : ℝ) (hL : 0≤L)
    (hG : ∀ᵐ p ∂inputLaw U, |(g : Lp ℝ 2 (inputLaw U)) p|≤L)
include hK hB hL hG

omit hG in
theorem targetInput_memLp_two : MemLp (boundedRepresentative U g L) 2 (inputLawQ A b U) := by
  let _ := fullLaw_probability A b K hK hB
  have : IsFiniteMeasure (inputLawQ A b U) := by unfold inputLawQ; infer_instance
  exact MemLp.of_bound ((boundedRepresentative_predictable U g L).mono predictableSigma_le).aestronglyMeasurable
    L (Eventually.of_forall (boundedRepresentative_bound U g L hL))

/-- Native dt×Q class of the actual selected predictable representative. -/
def targetInputValueQ : Lp ℝ 2 (inputLawQ A b U) :=
  (targetInput_memLp_two A b K hK hB U g L hL).toLp (boundedRepresentative U g L)

omit hG in
theorem targetInputValueQ_coe : targetInputValueQ A b K hK hB U g L hL=ᵐ[inputLawQ A b U] boundedRepresentative U g L :=
  (targetInput_memLp_two A b K hK hB U g L hL).coeFn_toLp

/-- Actual real progressive control is the SAME input class under its OWN
product law; a raw old-P Lp coercion is not granted progressive permission. -/
theorem targetInputValueQ_returns_control : targetInputValueQ A b K hK hB U g L hL=ᵐ[inputLawQ A b U]
    fun p => control U g L p.1 p.2 := by
  apply (targetInputValueQ_coe A b K hK hB U g L hL).trans
  apply (inputLawQ_absolutelyContinuous A b U).ae_le
  exact (boundedRepresentative_ae U g L hG).symm.trans (control_input_ae U g L hG).symm

/-- THESE actual original selected tables converge in dt×Q to SAME g's
representative. The Q conclusion follows by AC, subsequence DCT and SAME L. -/
theorem target_inputs_tendsto : Tendsto (fun n => inputValueQ A b K hK hB (approximation U g L hL hG n))
    atTop (𝓝 (targetInputValueQ A b K hK hB U g L hL)) := by
  let _ := fullLaw_probability A b K hK hB
  have : IsFiniteMeasure (inputLawQ A b U) := by unfold inputLawQ; infer_instance
  let r := approximation U g L hL hG
  let R := fun n => integrand (r n).clock (r n).coefficient
  let G := boundedRepresentative U g L
  have hm (n : ℕ) : MemLp (R n) 2 (inputLawQ A b U) :=
    BrownianOwnQTimeInput.integrand_memLp_two A b K hK hB (r n)
  have hg := targetInput_memLp_two A b K hK hB U g L hL
  have hRBound (n : ℕ) (p : ℝ × (ℝ≥0 → ℝ)) : ‖R n p‖≤L :=
    BrownianLeftMultiplierInputs.recordCoefficient_bound (r n) L hL
      (fun i ω => by simpa only [Real.norm_eq_abs] using approximation_bound U g L hL hG n i ω) p
  have hP : TendstoInMeasure (inputLaw U) R atTop G :=
    (tendstoInMeasure_of_tendsto_Lp (approximation_tendsto U g L hL hG)).congr
      (fun n => (BrownianTimeIntegrand.integrand_memLp_two U (r n).clock (r n).coefficient (r n).coefficient_bounded).coeFn_toLp)
      (boundedRepresentative_ae U g L hG)
  have hSquare : Tendsto (fun n => ∫ p, (R n p-G p)^2 ∂inputLawQ A b U) atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms,hms,hAE⟩ := (hP.comp hns).exists_seq_tendsto_ae
    refine ⟨ms,?_⟩
    have hlim : ∀ᵐ p ∂inputLawQ A b U, Tendsto (fun n => (R (ns (ms n)) p-G p)^2) atTop (𝓝 0) := by
      filter_upwards [(inputLawQ_absolutelyContinuous A b U).ae_le hAE] with p hp
      have h := (hp.sub_const (G p)).pow 2
      simpa only [Function.comp_def,sub_self,zero_pow (by decide : (2 : ℕ)≠0)] using h
    have hb (n : ℕ) : ∀ᵐ p ∂inputLawQ A b U, ‖(R (ns (ms n)) p-G p)^2‖≤(2*L)^2 := by
      apply Eventually.of_forall
      intro p
      rw [norm_pow]
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      exact (norm_sub_le _ _).trans (by linarith [hRBound (ns (ms n)) p,boundedRepresentative_bound U g L hL p])
    simpa only [integral_zero,Pi.pow_apply,Pi.sub_apply,G] using tendsto_integral_of_dominated_convergence (fun _ => (2*L)^2)
      (fun n => ((hm (ns (ms n))).aestronglyMeasurable.sub hg.aestronglyMeasurable).pow 2)
      (integrable_const _) hb hlim
  let E := fun n => inputValueQ A b K hK hB (r n)-targetInputValueQ A b K hK hB U g L hL
  have hnorm (n : ℕ) : ‖E n‖^2=∫ p, (R n p-G p)^2 ∂inputLawQ A b U := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (inputValueQ A b K hK hB (r n)) (targetInputValueQ A b K hK hB U g L hL),
      (hm n).coeFn_toLp,targetInputValueQ_coe A b K hK hB U g L hL] with p hs hr hg
    change ⟪E n p,E n p⟫_ℝ=(R n p-G p)^2
    change E n p=inputValueQ A b K hK hB (r n) p-targetInputValueQ A b K hK hB U g L hL p at hs
    change inputValueQ A b K hK hB (r n) p=R n p at hr
    change targetInputValueQ A b K hK hB U g L hL p=G p at hg
    rw [hs,hr,hg]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have hsNorm : Tendsto (fun n => ‖E n‖^2) atTop (𝓝 0) := (tendsto_congr' (Eventually.of_forall hnorm)).mpr hSquare
  have h := Real.continuous_sqrt.tendsto (0 : ℝ) |>.comp hsNorm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using h

/-- Membership is proved from the actual selected table limit, not supplied
as an input assumption and not asserted for all predictable Q classes. -/
theorem targetInput_mem_domain : targetInputValueQ A b K hK hB U g L hL∈integralDomain A b K hK hB U := by
  apply (elementarySpan A b K hK hB U).isClosed_topologicalClosure.mem_of_tendsto
    (target_inputs_tendsto A b K hK hB U g L hL hG)
  exact Eventually.of_forall (fun n => (elementarySpan A b K hK hB U).le_topologicalClosure
    (elementaryPoint A b K hK hB (approximation U g L hL hG n)).property)

def targetInputQ : integralDomain A b K hK hB U :=
  ⟨targetInputValueQ A b K hK hB U g L hL,targetInput_mem_domain A b K hK hB U g L hL hG⟩

/-- Actual Q stochastic integral of the SAME bounded target g, constructed
by the native isometry rather than relabeling predictableIntegral under P. -/
def targetIntegralQ : Lp ℝ 2 (fullLaw A b) := integral A b K hK hB U (targetInputQ A b K hK hB U g L hL hG)

theorem target_outputs_tendsto : Tendsto (fun n => outputValueQ A b K hK hB (approximation U g L hL hG n))
    atTop (𝓝 (targetIntegralQ A b K hK hB U g L hL hG)) :=
  literal_outputs_tendsto A b K hK hB _ _ (target_inputs_tendsto A b K hK hB U g L hL hG)

theorem targetIntegralQ_norm : ‖targetIntegralQ A b K hK hB U g L hL hG‖=‖targetInputValueQ A b K hK hB U g L hL‖ :=
  integral_norm A b K hK hB U (targetInputQ A b K hK hB U g L hL hG)

theorem targetIntegralQ_integrable : Integrable (targetIntegralQ A b K hK hB U g L hL hG : (ℝ≥0 → ℝ) → ℝ) (fullLaw A b) := by
  let _ := fullLaw_probability A b K hK hB
  exact (Lp.memLp (targetIntegralQ A b K hK hB U g L hL hG)).integrable one_le_two

/-- True zero mean of the CONSTRUCTED Q integral from literal Q finite
integrals and native L2 continuity, independent of any desired terminal field. -/
theorem targetIntegralQ_mean_zero : (∫ ω, targetIntegralQ A b K hK hB U g L hL hG ω ∂fullLaw A b)=0 := by
  let _ := fullLaw_probability A b K hK hB
  let u : Lp ℝ 2 (fullLaw A b) := (memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ))
  have hu : u=ᵐ[fullLaw A b] fun _ => (1 : ℝ) := (memLp_const (1 : ℝ)).coeFn_toLp
  have hz (n : ℕ) : ⟪u,outputValueQ A b K hK hB (approximation U g L hL hG n)⟫_ℝ=0 := by
    rw [L2.inner_def]
    have he : (fun ω => ⟪u ω,outputValueQ A b K hK hB (approximation U g L hL hG n) ω⟫_ℝ)=ᵐ[fullLaw A b]
        BrownianOwnQSimpleIntegral.simpleIntegral A b K (approximation U g L hL hG n) := by
      filter_upwards [hu,(BrownianOwnQSimpleIntegral.simpleIntegral_memLp_two A b K hK hB
        (approximation U g L hL hG n)).coeFn_toLp] with ω hu ho
      change outputValueQ A b K hK hB (approximation U g L hL hG n) ω=
        BrownianOwnQSimpleIntegral.simpleIntegral A b K (approximation U g L hL hG n) ω at ho
      rw [hu,ho]
      simp [RCLike.inner_apply]
    rw [integral_congr_ae he]
    exact BrownianOwnQSimpleIntegral.simpleIntegral_mean_zero A b K hK hB (approximation U g L hL hG n)
  have ht := ((innerSL ℝ u).continuous.tendsto (targetIntegralQ A b K hK hB U g L hL hG)).comp (target_outputs_tendsto A b K hK hB U g L hL hG)
  have hzFn : (fun n => ⟪u,outputValueQ A b K hK hB (approximation U g L hL hG n)⟫_ℝ)=(fun _ : ℕ => (0 : ℝ)) := funext hz
  change Tendsto (fun n => ⟪u,outputValueQ A b K hK hB (approximation U g L hL hG n)⟫_ℝ)
    atTop (𝓝 ⟪u,targetIntegralQ A b K hK hB U g L hL hG⟫_ℝ) at ht
  rw [hzFn] at ht
  have hzTarget : ⟪u,targetIntegralQ A b K hK hB U g L hL hG⟫_ℝ=0 := (tendsto_nhds_unique tendsto_const_nhds ht).symm
  rw [L2.inner_def] at hzTarget
  have he : (fun ω => ⟪u ω,targetIntegralQ A b K hK hB U g L hL hG ω⟫_ℝ)=ᵐ[fullLaw A b] targetIntegralQ A b K hK hB U g L hL hG := by
    filter_upwards [hu] with ω hu
    rw [hu]
    simp [RCLike.inner_apply]
  rwa [integral_congr_ae he] at hzTarget

omit g hG in
/-- Actual bounded target construction returns the SAME literal finite
Q output when its ORIGINAL predictable input is that actual table class. -/
theorem targetIntegralQ_returns_literal (r : ElementaryInput U)
    (hR : ∀ᵐ p ∂inputLaw U, |(literalPredictableInput r : Lp ℝ 2 (inputLaw U)) p|≤L) :
    targetIntegralQ A b K hK hB U (literalPredictableInput r) L hL hR=outputValueQ A b K hK hB r := by
  have hP : boundedRepresentative U (literalPredictableInput r) L=ᵐ[inputLaw U] integrand r.clock r.coefficient :=
    (boundedRepresentative_ae U (literalPredictableInput r) L hR).symm.trans
      (BrownianTimeIntegrand.integrand_memLp_two U r.clock r.coefficient r.coefficient_bounded).coeFn_toLp
  have hQ : boundedRepresentative U (literalPredictableInput r) L=ᵐ[inputLawQ A b U] integrand r.clock r.coefficient :=
    (inputLawQ_absolutelyContinuous A b U).ae_le hP
  have hInputs : targetInputValueQ A b K hK hB U (literalPredictableInput r) L hL=inputValueQ A b K hK hB r := by
    apply Lp.ext
    exact (targetInputValueQ_coe A b K hK hB U (literalPredictableInput r) L hL).trans
      (hQ.trans (BrownianOwnQTimeInput.integrand_memLp_two A b K hK hB r).coeFn_toLp.symm)
  have hDomain : targetInputQ A b K hK hB U (literalPredictableInput r) L hL hR=
      representedInput A b K hK hB r := Subtype.ext hInputs
  unfold targetIntegralQ
  rw [hDomain,BrownianOwnQIntegralClosure.integral_returns_literal]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQHorizonTargetIntegral
