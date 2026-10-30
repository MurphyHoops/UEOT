import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQIntegralClosure
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLeftMultiplierInputs

/-!
Original commitment: the actual bounded original predictable control must enter its OWN Q-integral domain, not a renamed closure assumption.
Existing result: SAME original selected K-bounded tables converge in dt×P; actual Q elementary-span closure owns an isometric integral.
Premise reduced: derive actual dt×Q convergence of THESE tables to the SAME clipped predictable representative/control and construct domain membership.
Model/witness: same native fullPredictableL2 f, same K, own Q/W, original real control, T=0 without division; no new approximant-exists field.
Consumer/boundary: actual Q integral of SAME bounded control; its identity with native P integral minus energy follows next, not assumed here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQBoundedInput
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianBoundedPredictableApproximation BrownianBoundedControlSource
open BrownianBoundedExponentialLimitSource BrownianOwnQTimeInput BrownianOwnQIntegralClosure
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory InnerProductSpace RealInnerProductSpace
noncomputable section
variable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K)

/-- Actual measure binding at every integration horizon. -/
theorem inputLawQ_density (U : ℝ≥0) : inputLawQ T f U=
    (inputLaw U).withDensity (fun p => ENNReal.ofReal (fullDensity T f p.2)) :=
  prod_withDensity_right (fullDensity_measurable T f).ennreal_ofReal

theorem inputLawQ_absolutelyContinuous (U : ℝ≥0) : inputLawQ T f U≪inputLaw U := by
  rw [inputLawQ_density]
  exact withDensity_absolutelyContinuous _ _

include hK hbound

theorem boundedInput_memLp_two : MemLp (boundedRepresentative T f K) 2 (inputLawQ T f T) := by
  let _ := fullLaw_probability T f K hK hbound
  have : IsFiniteMeasure (inputLawQ T f T) := by unfold inputLawQ; infer_instance
  exact MemLp.of_bound ((boundedRepresentative_predictable T f K).mono predictableSigma_le).aestronglyMeasurable
    K (Eventually.of_forall (boundedRepresentative_bound T f K hK))

/-- Native dt×Q class of the actual selected predictable representative. -/
def boundedInputValueQ : Lp ℝ 2 (inputLawQ T f T) :=
  (boundedInput_memLp_two T f K hK hbound).toLp (boundedRepresentative T f K)

theorem boundedInputValueQ_coe : boundedInputValueQ T f K hK hbound=ᵐ[inputLawQ T f T] boundedRepresentative T f K :=
  (boundedInput_memLp_two T f K hK hbound).coeFn_toLp

/-- Actual real progressive control is the SAME input class under its OWN
product law; a raw old-P Lp coercion is not granted progressive permission. -/
theorem boundedInputValueQ_returns_control : boundedInputValueQ T f K hK hbound=ᵐ[inputLawQ T f T]
    fun p => control T f K p.1 p.2 := by
  apply (boundedInputValueQ_coe T f K hK hbound).trans
  apply (inputLawQ_absolutelyContinuous T f T).ae_le
  exact (boundedRepresentative_ae T f K hbound).symm.trans (control_input_ae T f K hbound).symm

/-- THESE actual original selected tables converge in dt×Q to SAME f's
representative. The Q conclusion follows by AC, subsequence DCT and SAME K. -/
theorem actual_inputs_tendsto : Tendsto (fun n => inputValueQ T f K hK hbound (approximation T f K hK hbound n))
    atTop (𝓝 (boundedInputValueQ T f K hK hbound)) := by
  let _ := fullLaw_probability T f K hK hbound
  have : IsFiniteMeasure (inputLawQ T f T) := by unfold inputLawQ; infer_instance
  let r := approximation T f K hK hbound
  let R := fun n => integrand (r n).clock (r n).coefficient
  let g := boundedRepresentative T f K
  have hm (n : ℕ) : MemLp (R n) 2 (inputLawQ T f T) :=
    BrownianOwnQTimeInput.integrand_memLp_two T f K hK hbound (r n)
  have hg := boundedInput_memLp_two T f K hK hbound
  have hRBound (n : ℕ) (p : ℝ × (ℝ≥0 → ℝ)) : ‖R n p‖≤K :=
    BrownianLeftMultiplierInputs.recordCoefficient_bound (r n) K hK
      (fun i ω => by simpa only [Real.norm_eq_abs] using approximation_bound T f K hK hbound n i ω) p
  have hP : TendstoInMeasure (inputLaw T) R atTop g :=
    (tendstoInMeasure_of_tendsto_Lp (approximation_tendsto T f K hK hbound)).congr
      (fun n => (BrownianTimeIntegrand.integrand_memLp_two T (r n).clock (r n).coefficient (r n).coefficient_bounded).coeFn_toLp)
      (boundedRepresentative_ae T f K hbound)
  have hSquare : Tendsto (fun n => ∫ p, (R n p-g p)^2 ∂inputLawQ T f T) atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms,hms,hAE⟩ := (hP.comp hns).exists_seq_tendsto_ae
    refine ⟨ms,?_⟩
    have hlim : ∀ᵐ p ∂inputLawQ T f T, Tendsto (fun n => (R (ns (ms n)) p-g p)^2) atTop (𝓝 0) := by
      filter_upwards [(inputLawQ_absolutelyContinuous T f T).ae_le hAE] with p hp
      have h := (hp.sub_const (g p)).pow 2
      simpa only [Function.comp_def,sub_self,zero_pow (by decide : (2 : ℕ)≠0)] using h
    have hb (n : ℕ) : ∀ᵐ p ∂inputLawQ T f T, ‖(R (ns (ms n)) p-g p)^2‖≤(2*K)^2 := by
      apply Eventually.of_forall
      intro p
      rw [norm_pow]
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      exact (norm_sub_le _ _).trans (by linarith [hRBound (ns (ms n)) p,boundedRepresentative_bound T f K hK p])
    simpa only [integral_zero,Pi.pow_apply,Pi.sub_apply,g] using tendsto_integral_of_dominated_convergence (fun _ => (2*K)^2)
      (fun n => ((hm (ns (ms n))).aestronglyMeasurable.sub hg.aestronglyMeasurable).pow 2)
      (integrable_const _) hb hlim
  let E := fun n => inputValueQ T f K hK hbound (r n)-boundedInputValueQ T f K hK hbound
  have hnorm (n : ℕ) : ‖E n‖^2=∫ p, (R n p-g p)^2 ∂inputLawQ T f T := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (inputValueQ T f K hK hbound (r n)) (boundedInputValueQ T f K hK hbound),
      (hm n).coeFn_toLp,boundedInputValueQ_coe T f K hK hbound] with p hs hr hg
    change ⟪E n p,E n p⟫_ℝ=(R n p-g p)^2
    change E n p=inputValueQ T f K hK hbound (r n) p-boundedInputValueQ T f K hK hbound p at hs
    change inputValueQ T f K hK hbound (r n) p=R n p at hr
    change boundedInputValueQ T f K hK hbound p=g p at hg
    rw [hs,hr,hg]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have hsNorm : Tendsto (fun n => ‖E n‖^2) atTop (𝓝 0) := (tendsto_congr' (Eventually.of_forall hnorm)).mpr hSquare
  have h := Real.continuous_sqrt.tendsto (0 : ℝ) |>.comp hsNorm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using h

/-- Membership is proved from the actual selected table limit, not supplied
as an input assumption and not asserted for all predictable Q classes. -/
theorem boundedInput_mem_domain : boundedInputValueQ T f K hK hbound∈integralDomain T f K hK hbound T := by
  apply (elementarySpan T f K hK hbound T).isClosed_topologicalClosure.mem_of_tendsto
    (actual_inputs_tendsto T f K hK hbound)
  exact Eventually.of_forall (fun n => (elementarySpan T f K hK hbound T).le_topologicalClosure
    (elementaryPoint T f K hK hbound (approximation T f K hK hbound n)).property)

def boundedInputQ : integralDomain T f K hK hbound T :=
  ⟨boundedInputValueQ T f K hK hbound,boundedInput_mem_domain T f K hK hbound⟩

/-- Actual Q stochastic integral of the SAME bounded control, constructed
by the native isometry rather than relabeling predictableIntegral under P. -/
def boundedIntegralQ : Lp ℝ 2 (fullLaw T f) := integral T f K hK hbound T (boundedInputQ T f K hK hbound)

theorem actual_outputs_tendsto : Tendsto (fun n => outputValueQ T f K hK hbound (approximation T f K hK hbound n))
    atTop (𝓝 (boundedIntegralQ T f K hK hbound)) :=
  literal_outputs_tendsto T f K hK hbound _ _ (actual_inputs_tendsto T f K hK hbound)

theorem boundedIntegralQ_norm : ‖boundedIntegralQ T f K hK hbound‖=‖boundedInputValueQ T f K hK hbound‖ :=
  integral_norm T f K hK hbound T (boundedInputQ T f K hK hbound)

theorem boundedIntegralQ_integrable : Integrable (boundedIntegralQ T f K hK hbound : (ℝ≥0 → ℝ) → ℝ) (fullLaw T f) := by
  let _ := fullLaw_probability T f K hK hbound
  exact (Lp.memLp (boundedIntegralQ T f K hK hbound)).integrable one_le_two

/-- True zero mean of the CONSTRUCTED Q integral from literal Q finite
integrals and native L2 continuity, independent of any desired terminal field. -/
theorem boundedIntegralQ_mean_zero : (∫ ω, boundedIntegralQ T f K hK hbound ω ∂fullLaw T f)=0 := by
  let _ := fullLaw_probability T f K hK hbound
  let u : Lp ℝ 2 (fullLaw T f) := (memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ))
  have hu : u=ᵐ[fullLaw T f] fun _ => (1 : ℝ) := (memLp_const (1 : ℝ)).coeFn_toLp
  have hz (n : ℕ) : ⟪u,outputValueQ T f K hK hbound (approximation T f K hK hbound n)⟫_ℝ=0 := by
    rw [L2.inner_def]
    have he : (fun ω => ⟪u ω,outputValueQ T f K hK hbound (approximation T f K hK hbound n) ω⟫_ℝ)=ᵐ[fullLaw T f]
        BrownianOwnQSimpleIntegral.simpleIntegral T f K (approximation T f K hK hbound n) := by
      filter_upwards [hu,(BrownianOwnQSimpleIntegral.simpleIntegral_memLp_two T f K hK hbound
        (approximation T f K hK hbound n)).coeFn_toLp] with ω hu ho
      change outputValueQ T f K hK hbound (approximation T f K hK hbound n) ω=
        BrownianOwnQSimpleIntegral.simpleIntegral T f K (approximation T f K hK hbound n) ω at ho
      rw [hu,ho]
      simp [RCLike.inner_apply]
    rw [integral_congr_ae he]
    exact BrownianOwnQSimpleIntegral.simpleIntegral_mean_zero T f K hK hbound (approximation T f K hK hbound n)
  have ht := ((innerSL ℝ u).continuous.tendsto (boundedIntegralQ T f K hK hbound)).comp (actual_outputs_tendsto T f K hK hbound)
  have hzFn : (fun n => ⟪u,outputValueQ T f K hK hbound (approximation T f K hK hbound n)⟫_ℝ)=(fun _ : ℕ => (0 : ℝ)) := funext hz
  change Tendsto (fun n => ⟪u,outputValueQ T f K hK hbound (approximation T f K hK hbound n)⟫_ℝ)
    atTop (𝓝 ⟪u,boundedIntegralQ T f K hK hbound⟫_ℝ) at ht
  rw [hzFn] at ht
  have hzTarget : ⟪u,boundedIntegralQ T f K hK hbound⟫_ℝ=0 := (tendsto_nhds_unique tendsto_const_nhds ht).symm
  rw [L2.inner_def] at hzTarget
  have he : (fun ω => ⟪u ω,boundedIntegralQ T f K hK hbound ω⟫_ℝ)=ᵐ[fullLaw T f] boundedIntegralQ T f K hK hbound := by
    filter_upwards [hu] with ω hu
    rw [hu]
    simp [RCLike.inner_apply]
  rwa [integral_congr_ae he] at hzTarget

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQBoundedInput
