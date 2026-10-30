import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQBoundedInput

/-!
Original commitment: the original ItoRun test integrand differs from the control defining Q and still needs a real Q integral.
Existing result: fixed control b owns actual Q/W, original Fs permissions and native dt×Q elementary-closure isometry.
Premise reduced: derive Q-domain membership and actual Q integral of an independently declared bounded ORIGINAL predictable target g from its computed tables.
Model/witness: SAME fixed b,K,Q/W and horizon T; target g,L may differ, original START permissions preserved, T=0 included.
Consumer/boundary: g=σV'(X) in actual controlled Dynkin/occupation; neither deployment b/Q nor full-Q predictable density is changed/assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTargetIntegral
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianBoundedPredictableApproximation BrownianBoundedControlSource
open BrownianBoundedExponentialLimitSource BrownianOwnQTimeInput BrownianOwnQIntegralClosure BrownianOwnQBoundedInput
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory InnerProductSpace RealInnerProductSpace
noncomputable section
variable (T : ℝ≥0) (b : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw T, |(b : Lp ℝ 2 (inputLaw T)) p|≤K)
    (g : fullPredictableL2 T) (L : ℝ) (hL : 0≤L)
    (hG : ∀ᵐ p ∂inputLaw T, |(g : Lp ℝ 2 (inputLaw T)) p|≤L)
include hK hB hL hG

omit hG in
theorem targetInput_memLp_two : MemLp (boundedRepresentative T g L) 2 (inputLawQ T b T) := by
  let _ := fullLaw_probability T b K hK hB
  have : IsFiniteMeasure (inputLawQ T b T) := by unfold inputLawQ; infer_instance
  exact MemLp.of_bound ((boundedRepresentative_predictable T g L).mono predictableSigma_le).aestronglyMeasurable
    L (Eventually.of_forall (boundedRepresentative_bound T g L hL))

/-- Native dt×Q class of the actual selected predictable representative. -/
def targetInputValueQ : Lp ℝ 2 (inputLawQ T b T) :=
  (targetInput_memLp_two T b K hK hB g L hL).toLp (boundedRepresentative T g L)

omit hG in
theorem targetInputValueQ_coe : targetInputValueQ T b K hK hB g L hL=ᵐ[inputLawQ T b T] boundedRepresentative T g L :=
  (targetInput_memLp_two T b K hK hB g L hL).coeFn_toLp

/-- Actual real progressive control is the SAME input class under its OWN
product law; a raw old-P Lp coercion is not granted progressive permission. -/
theorem targetInputValueQ_returns_control : targetInputValueQ T b K hK hB g L hL=ᵐ[inputLawQ T b T]
    fun p => control T g L p.1 p.2 := by
  apply (targetInputValueQ_coe T b K hK hB g L hL).trans
  apply (inputLawQ_absolutelyContinuous T b T).ae_le
  exact (boundedRepresentative_ae T g L hG).symm.trans (control_input_ae T g L hG).symm

/-- THESE actual original selected tables converge in dt×Q to SAME g's
representative. The Q conclusion follows by AC, subsequence DCT and SAME L. -/
theorem target_inputs_tendsto : Tendsto (fun n => inputValueQ T b K hK hB (approximation T g L hL hG n))
    atTop (𝓝 (targetInputValueQ T b K hK hB g L hL)) := by
  let _ := fullLaw_probability T b K hK hB
  have : IsFiniteMeasure (inputLawQ T b T) := by unfold inputLawQ; infer_instance
  let r := approximation T g L hL hG
  let R := fun n => integrand (r n).clock (r n).coefficient
  let G := boundedRepresentative T g L
  have hm (n : ℕ) : MemLp (R n) 2 (inputLawQ T b T) :=
    BrownianOwnQTimeInput.integrand_memLp_two T b K hK hB (r n)
  have hg := targetInput_memLp_two T b K hK hB g L hL
  have hRBound (n : ℕ) (p : ℝ × (ℝ≥0 → ℝ)) : ‖R n p‖≤L :=
    BrownianLeftMultiplierInputs.recordCoefficient_bound (r n) L hL
      (fun i ω => by simpa only [Real.norm_eq_abs] using approximation_bound T g L hL hG n i ω) p
  have hP : TendstoInMeasure (inputLaw T) R atTop G :=
    (tendstoInMeasure_of_tendsto_Lp (approximation_tendsto T g L hL hG)).congr
      (fun n => (BrownianTimeIntegrand.integrand_memLp_two T (r n).clock (r n).coefficient (r n).coefficient_bounded).coeFn_toLp)
      (boundedRepresentative_ae T g L hG)
  have hSquare : Tendsto (fun n => ∫ p, (R n p-G p)^2 ∂inputLawQ T b T) atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms,hms,hAE⟩ := (hP.comp hns).exists_seq_tendsto_ae
    refine ⟨ms,?_⟩
    have hlim : ∀ᵐ p ∂inputLawQ T b T, Tendsto (fun n => (R (ns (ms n)) p-G p)^2) atTop (𝓝 0) := by
      filter_upwards [(inputLawQ_absolutelyContinuous T b T).ae_le hAE] with p hp
      have h := (hp.sub_const (G p)).pow 2
      simpa only [Function.comp_def,sub_self,zero_pow (by decide : (2 : ℕ)≠0)] using h
    have hb (n : ℕ) : ∀ᵐ p ∂inputLawQ T b T, ‖(R (ns (ms n)) p-G p)^2‖≤(2*L)^2 := by
      apply Eventually.of_forall
      intro p
      rw [norm_pow]
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      exact (norm_sub_le _ _).trans (by linarith [hRBound (ns (ms n)) p,boundedRepresentative_bound T g L hL p])
    simpa only [integral_zero,Pi.pow_apply,Pi.sub_apply,G] using tendsto_integral_of_dominated_convergence (fun _ => (2*L)^2)
      (fun n => ((hm (ns (ms n))).aestronglyMeasurable.sub hg.aestronglyMeasurable).pow 2)
      (integrable_const _) hb hlim
  let E := fun n => inputValueQ T b K hK hB (r n)-targetInputValueQ T b K hK hB g L hL
  have hnorm (n : ℕ) : ‖E n‖^2=∫ p, (R n p-G p)^2 ∂inputLawQ T b T := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (inputValueQ T b K hK hB (r n)) (targetInputValueQ T b K hK hB g L hL),
      (hm n).coeFn_toLp,targetInputValueQ_coe T b K hK hB g L hL] with p hs hr hg
    change ⟪E n p,E n p⟫_ℝ=(R n p-G p)^2
    change E n p=inputValueQ T b K hK hB (r n) p-targetInputValueQ T b K hK hB g L hL p at hs
    change inputValueQ T b K hK hB (r n) p=R n p at hr
    change targetInputValueQ T b K hK hB g L hL p=G p at hg
    rw [hs,hr,hg]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have hsNorm : Tendsto (fun n => ‖E n‖^2) atTop (𝓝 0) := (tendsto_congr' (Eventually.of_forall hnorm)).mpr hSquare
  have h := Real.continuous_sqrt.tendsto (0 : ℝ) |>.comp hsNorm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using h

/-- Membership is proved from the actual selected table limit, not supplied
as an input assumption and not asserted for all predictable Q classes. -/
theorem targetInput_mem_domain : targetInputValueQ T b K hK hB g L hL∈integralDomain T b K hK hB T := by
  apply (elementarySpan T b K hK hB T).isClosed_topologicalClosure.mem_of_tendsto
    (target_inputs_tendsto T b K hK hB g L hL hG)
  exact Eventually.of_forall (fun n => (elementarySpan T b K hK hB T).le_topologicalClosure
    (elementaryPoint T b K hK hB (approximation T g L hL hG n)).property)

def targetInputQ : integralDomain T b K hK hB T :=
  ⟨targetInputValueQ T b K hK hB g L hL,targetInput_mem_domain T b K hK hB g L hL hG⟩

/-- Actual Q stochastic integral of the SAME bounded target g, constructed
by the native isometry rather than relabeling predictableIntegral under P. -/
def targetIntegralQ : Lp ℝ 2 (fullLaw T b) := integral T b K hK hB T (targetInputQ T b K hK hB g L hL hG)

theorem target_outputs_tendsto : Tendsto (fun n => outputValueQ T b K hK hB (approximation T g L hL hG n))
    atTop (𝓝 (targetIntegralQ T b K hK hB g L hL hG)) :=
  literal_outputs_tendsto T b K hK hB _ _ (target_inputs_tendsto T b K hK hB g L hL hG)

theorem targetIntegralQ_norm : ‖targetIntegralQ T b K hK hB g L hL hG‖=‖targetInputValueQ T b K hK hB g L hL‖ :=
  integral_norm T b K hK hB T (targetInputQ T b K hK hB g L hL hG)

theorem targetIntegralQ_integrable : Integrable (targetIntegralQ T b K hK hB g L hL hG : (ℝ≥0 → ℝ) → ℝ) (fullLaw T b) := by
  let _ := fullLaw_probability T b K hK hB
  exact (Lp.memLp (targetIntegralQ T b K hK hB g L hL hG)).integrable one_le_two

/-- True zero mean of the CONSTRUCTED Q integral from literal Q finite
integrals and native L2 continuity, independent of any desired terminal field. -/
theorem targetIntegralQ_mean_zero : (∫ ω, targetIntegralQ T b K hK hB g L hL hG ω ∂fullLaw T b)=0 := by
  let _ := fullLaw_probability T b K hK hB
  let u : Lp ℝ 2 (fullLaw T b) := (memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ))
  have hu : u=ᵐ[fullLaw T b] fun _ => (1 : ℝ) := (memLp_const (1 : ℝ)).coeFn_toLp
  have hz (n : ℕ) : ⟪u,outputValueQ T b K hK hB (approximation T g L hL hG n)⟫_ℝ=0 := by
    rw [L2.inner_def]
    have he : (fun ω => ⟪u ω,outputValueQ T b K hK hB (approximation T g L hL hG n) ω⟫_ℝ)=ᵐ[fullLaw T b]
        BrownianOwnQSimpleIntegral.simpleIntegral T b K (approximation T g L hL hG n) := by
      filter_upwards [hu,(BrownianOwnQSimpleIntegral.simpleIntegral_memLp_two T b K hK hB
        (approximation T g L hL hG n)).coeFn_toLp] with ω hu ho
      change outputValueQ T b K hK hB (approximation T g L hL hG n) ω=
        BrownianOwnQSimpleIntegral.simpleIntegral T b K (approximation T g L hL hG n) ω at ho
      rw [hu,ho]
      simp [RCLike.inner_apply]
    rw [integral_congr_ae he]
    exact BrownianOwnQSimpleIntegral.simpleIntegral_mean_zero T b K hK hB (approximation T g L hL hG n)
  have ht := ((innerSL ℝ u).continuous.tendsto (targetIntegralQ T b K hK hB g L hL hG)).comp (target_outputs_tendsto T b K hK hB g L hL hG)
  have hzFn : (fun n => ⟪u,outputValueQ T b K hK hB (approximation T g L hL hG n)⟫_ℝ)=(fun _ : ℕ => (0 : ℝ)) := funext hz
  change Tendsto (fun n => ⟪u,outputValueQ T b K hK hB (approximation T g L hL hG n)⟫_ℝ)
    atTop (𝓝 ⟪u,targetIntegralQ T b K hK hB g L hL hG⟫_ℝ) at ht
  rw [hzFn] at ht
  have hzTarget : ⟪u,targetIntegralQ T b K hK hB g L hL hG⟫_ℝ=0 := (tendsto_nhds_unique tendsto_const_nhds ht).symm
  rw [L2.inner_def] at hzTarget
  have he : (fun ω => ⟪u ω,targetIntegralQ T b K hK hB g L hL hG ω⟫_ℝ)=ᵐ[fullLaw T b] targetIntegralQ T b K hK hB g L hL hG := by
    filter_upwards [hu] with ω hu
    rw [hu]
    simp [RCLike.inner_apply]
  rwa [integral_congr_ae he] at hzTarget

omit g hG in
/-- Actual bounded target construction returns the SAME literal finite
Q output when its ORIGINAL predictable input is that actual table class. -/
theorem targetIntegralQ_returns_literal (r : ElementaryInput T)
    (hR : ∀ᵐ p ∂inputLaw T, |(literalPredictableInput r : Lp ℝ 2 (inputLaw T)) p|≤L) :
    targetIntegralQ T b K hK hB (literalPredictableInput r) L hL hR=outputValueQ T b K hK hB r := by
  have hP : boundedRepresentative T (literalPredictableInput r) L=ᵐ[inputLaw T] integrand r.clock r.coefficient :=
    (boundedRepresentative_ae T (literalPredictableInput r) L hR).symm.trans
      (BrownianTimeIntegrand.integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp
  have hQ : boundedRepresentative T (literalPredictableInput r) L=ᵐ[inputLawQ T b T] integrand r.clock r.coefficient :=
    (inputLawQ_absolutelyContinuous T b T).ae_le hP
  have hInputs : targetInputValueQ T b K hK hB (literalPredictableInput r) L hL=inputValueQ T b K hK hB r := by
    apply Lp.ext
    exact (targetInputValueQ_coe T b K hK hB (literalPredictableInput r) L hL).trans
      (hQ.trans (BrownianOwnQTimeInput.integrand_memLp_two T b K hK hB r).coeFn_toLp.symm)
  have hDomain : targetInputQ T b K hK hB (literalPredictableInput r) L hL hR=
      representedInput T b K hK hB r := Subtype.ext hInputs
  unfold targetIntegralQ
  rw [hDomain,BrownianOwnQIntegralClosure.integral_returns_literal]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTargetIntegral
