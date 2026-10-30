import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQFullIntegralSource

/-!
Original commitment: genuine unbounded original-START Q-L2 coefficients need actual same-W literal integration, not a bounded-input coercion.
Existing result: full native original-predictable own-Q domain equals actual closure and returns original finite bounded literal outputs.
Premise reduced: actual past H in Q-L2 produces interval input; real bounded clips of H converge to SAME input and literal outputs identify actual HΔW by AE subsequence uniqueness.
Model/witness: SAME Q_A/W, original Fs_s permission, s≤t≤U with U>A allowed; H need not be P-L2 or Q-essentially bounded.
Consumer/boundary: actual unbounded W_s coefficient and own-Q martingale/energy; no lookahead coefficients, natural-filtration equality or continuous modification asserted.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQUnboundedIntervalSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs BrownianIntegralClosure
open BrownianBoundedControlSource BrownianBoundedGirsanovSource BrownianBoundedExponentialLimitSource BrownianContinuousAdaptedInputs
open BrownianOwnQTimeInput BrownianOwnQPredictableDensity BrownianOwnQFullIntegralSource
open BrownianOwnQConditionalStep BrownianOwnQTimeTruncation BrownianOwnQOneStepIntegral
open BrownianIntegralConditionalStep BrownianIntegralLiteralIntervals
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory RealInnerProductSpace
noncomputable section
variable (A : ℝ≥0) (f : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hF : ∀ᵐ p ∂inputLaw A, |(f : Lp ℝ 2 (inputLaw A)) p|≤K)

include hK hF

theorem interval_memLp_two {H : (ℝ≥0→ℝ)→ℝ} (hH : MemLp H 2 (fullLaw A f)) (U s t : ℝ≥0) :
    MemLp (intervalIntegrand H s t) 2 (inputLawQ A f U) := by
  let _:=fullLaw_probability A f K hK hF
  have hi : MemLp ((Ioc (s : ℝ) (t : ℝ)).indicator (fun _ : ℝ=>(1 : ℝ))) ∞ (timeLaw U) :=
    (memLp_top_const 1).indicator measurableSet_Ioc
  exact (hH.comp_snd (timeLaw U)).mul (hi.comp_fst (fullLaw A f))

def intervalInputQ (U s t : ℝ≥0) (H : (ℝ≥0→ℝ)→ℝ)
    (hp : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H 2 (fullLaw A f)) : fullPredictableL2Q A f U :=
  ⟨(interval_memLp_two A f K hK hF hH U s t).toLp (intervalIntegrand H s t),
    mem_lpMeas_iff_aestronglyMeasurable.mpr ((intervalIntegrand_predictable s t hp).aestronglyMeasurable.congr
      (interval_memLp_two A f K hK hF hH U s t).coeFn_toLp.symm)⟩

theorem intervalInputQ_coe (U s t : ℝ≥0) (H : (ℝ≥0→ℝ)→ℝ)
    (hp : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H 2 (fullLaw A f)) :
    (intervalInputQ A f K hK hF U s t H hp hH : Lp ℝ 2 (inputLawQ A f U))=ᵐ[inputLawQ A f U] intervalIntegrand H s t :=
  (interval_memLp_two A f K hK hF hH U s t).coeFn_toLp

omit hK hF in
private theorem clip_bound (n : ℕ) (x : ℝ) : ‖clip n x‖≤(n : ℝ) := by
  rw[Real.norm_eq_abs,abs_le]
  have hn : 0≤(n : ℝ) := Nat.cast_nonneg n
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩
omit hK hF in
private theorem clip_fixed (c x : ℝ) (h : |x|≤c) : clip c x=x := by
  rcases abs_le.mp h with ⟨hl,hu⟩
  simp only[clip,min_eq_right hu,max_eq_right hl]
omit hK hF in
private theorem clip_past {H : (ℝ≥0→ℝ)→ℝ} {s : ℝ≥0} (hp : StronglyMeasurable[naturalFiltration s] H) (n : ℕ) :
    StronglyMeasurable[naturalFiltration s] (fun ω=>clip n (H ω)) :=
  (continuous_const.max (continuous_const.min continuous_id)).comp_stronglyMeasurable hp
omit hK hF in
private theorem clip_top_P {H : (ℝ≥0→ℝ)→ℝ} {s : ℝ≥0} (hp : StronglyMeasurable[naturalFiltration s] H) (n : ℕ) :
    MemLp (fun ω=>clip n (H ω)) ∞ sourceLaw :=
  MemLp.of_bound (((clip_past hp n).mono (naturalFiltration.le s)).aestronglyMeasurable) n
    (Eventually.of_forall (fun ω=>clip_bound n (H ω)))

/-- Constructed integral literally returns H times SAME actual Q-Brownian
increment for every START-measurable Q-L2 H, WITHOUT a bounded-H premise. -/
theorem integral_returns_unbounded_step (U s t : ℝ≥0) (hst : s≤t) (htU : t≤U)
    (H : (ℝ≥0→ℝ)→ℝ) (hp : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H 2 (fullLaw A f)) :
    (fullIntegral A f K hK hF U (intervalInputQ A f K hK hF U s t H hp hH) : (ℝ≥0→ℝ)→ℝ)=ᵐ[fullLaw A f] oneStep A f K H s t := by
  let g:=intervalInputQ A f K hK hF U s t H hp hH
  let r (n : ℕ) := intervalRecord U s t hst htU (fun ω=>clip n (H ω)) (clip_past hp n) (clip_top_P hp n)
  have he (n : ℕ) : inputValueQ A f K hK hF (r n)=clippedInputQ A f K hK hF U g n := by
    apply Lp.ext
    filter_upwards [interval_input_coe A f K hK hF U s t hst htU (fun ω=>clip n (H ω)) (clip_past hp n) (clip_top_P hp n),
      clippedInputQ_coe A f K hK hF U g n,representativeQ_ae A f U g,intervalInputQ_coe A f K hK hF U s t H hp hH] with p hr hc hg hi
    change inputValueQ A f K hK hF (r n) p=intervalIntegrand (fun ω=>clip n (H ω)) s t p at hr
    rw[hr,hc]
    change intervalIntegrand (fun ω=>clip n (H ω)) s t p=clip n (representativeQ A f U g p)
    rw[←hg,hi]
    by_cases h : p.1∈Ioc (s : ℝ) (t : ℝ)
    · simp[intervalIntegrand,h]
    · simp only[intervalIntegrand,Set.indicator_of_notMem h,zero_mul]
      exact (clip_fixed n 0 (by simpa only [abs_zero] using Nat.cast_nonneg (α:=ℝ) n)).symm
  have ht : Tendsto (fun n=>inputValueQ A f K hK hF (r n)) atTop (𝓝 g.val) :=
    (tendsto_congr' (Eventually.of_forall he)).mpr (clippedInputQ_tendsto A f K hK hF U g)
  have hf : Tendsto (fun n=>elementaryInputQ A f K hK hF (r n)) atTop (𝓝 g) := tendsto_subtype_rng.mpr ht
  have ho : Tendsto (fun n=>fullIntegral A f K hK hF U (elementaryInputQ A f K hK hF (r n))) atTop
      (𝓝 (fullIntegral A f K hK hF U g)) := ((fullIntegral A f K hK hF U).continuous.tendsto g).comp hf
  simp only[fullIntegral_returns_literal] at ho
  obtain ⟨ns,hns,hAE⟩:=(tendstoInMeasure_of_tendsto_Lp ho).exists_seq_tendsto_ae
  have hc : ∀ᵐ ω ∂fullLaw A f,∀ n,outputValueQ A f K hK hF (r n) ω=oneStep A f K (fun ω=>clip n (H ω)) s t ω := by
    apply ae_all_iff.mpr
    intro n
    rw[show outputValueQ A f K hK hF (r n)=
      (oneStep_memLp_two A f K hK hF (coefficient_bounded_Q A f K hK hF (clip_top_P hp n)) s t).toLp
        (oneStep A f K (fun ω=>clip n (H ω)) s t) from
        BrownianOwnQIntegralMartingale.interval_output A f K hK hF U s t hst htU _ (clip_past hp n) (clip_top_P hp n)]
    exact (oneStep_memLp_two A f K hK hF (coefficient_bounded_Q A f K hK hF (clip_top_P hp n)) s t).coeFn_toLp
  filter_upwards[hAE,hc] with ω hω hcoe
  have hl : Tendsto (fun n : ℕ=>oneStep A f K (fun ω=>clip n (H ω)) s t ω) atTop (𝓝 (oneStep A f K H s t ω)) := by
    obtain ⟨N,hN⟩:=exists_nat_ge |H ω|
    apply tendsto_const_nhds.congr'
    filter_upwards[eventually_ge_atTop N] with n hn
    simp only[oneStep,Pi.mul_apply]
    rw[clip_fixed n (H ω) (hN.trans (by exact_mod_cast hn))]
  exact tendsto_nhds_unique hω ((tendsto_congr' (Eventually.of_forall (fun n=>hcoe (ns n)))).mpr (hl.comp hns.tendsto_atTop))

/-- True L2 integrability of the actual unbounded literal output is a
CONSEQUENCE of its constructed Q-integral identity, not an input field. -/
theorem unbounded_step_memLp_two (U s t : ℝ≥0) (hst : s≤t) (htU : t≤U)
    (H : (ℝ≥0→ℝ)→ℝ) (hp : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H 2 (fullLaw A f)) :
    MemLp (oneStep A f K H s t) 2 (fullLaw A f) :=
  (memLp_congr_ae (integral_returns_unbounded_step A f K hK hF U s t hst htU H hp hH)).mp (Lp.memLp _)

/-- The actual integrator's past value has genuine Q-L2 by its derived Gaussian law. -/
theorem shifted_memLp_two (s : ℝ≥0) : MemLp (shiftedProcess A f K s) 2 (fullLaw A f) :=
  ((full_isPreBrownian A f K hK hF).hasLaw_eval s).hasGaussianLaw.memLp_two

theorem shifted_square_mean (s : ℝ≥0) : (∫ ω,shiftedProcess A f K s ω^2 ∂fullLaw A f)=(s : ℝ) := by
  have he : (∫ω,shiftedProcess A f K s ω^2 ∂fullLaw A f)=(∫x : ℝ,x^2 ∂gaussianReal 0 s) :=
    ((full_isPreBrownian A f K hK hF).hasLaw_eval s).integral_comp (f:=fun x : ℝ=>x^2) (by fun_prop)
  rw[he]
  have h:=variance_id_gaussianReal (μ:=0) (v:=s)
  rw[variance_eq_integral measurable_id.aemeasurable] at h
  simpa only[id_eq,integral_id_gaussianReal,sub_zero] using h

/-- Positive-time W_s is genuinely essentially unbounded under SAME Q;
its L2 input cannot be obtained by falsely supplying a bounded-H producer. -/
theorem shifted_not_memLp_top (s : ℝ≥0) (hs : 0<s) : ¬MemLp (shiftedProcess A f K s) ∞ (fullLaw A f) := by
  intro h
  obtain ⟨C,hC⟩:=eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
    (show eLpNormEssSup (shiftedProcess A f K s) (fullLaw A f)<⊤ by simpa only[eLpNorm_exponent_top] using h.2)
  have hb : ∀ᵐ ω ∂fullLaw A f, |shiftedProcess A f K s ω|≤(C : ℝ) := by
    filter_upwards[hC] with ω hω
    simpa only[Real.norm_eq_abs] using (show ‖shiftedProcess A f K s ω‖≤(C : ℝ) by exact_mod_cast hω)
  have hg : ∀ᵐ x ∂gaussianReal 0 s,|x|≤(C : ℝ) :=
    (((full_isPreBrownian A f K hK hF).hasLaw_eval s).ae_iff (by fun_prop)).mp hb
  have hv : ∀ᵐ x ∂(volume : Measure ℝ),|x|≤(C : ℝ) := (gaussianReal_absolutelyContinuous' 0 (ne_of_gt hs)).ae_le hg
  have hz : volume (Ioc ((C : ℝ)+1) ((C : ℝ)+2))=0 :=
    measure_mono_null (by
      intro x hx
      change ¬(|x|≤(C : ℝ))
      intro h
      have hh : x≤(C : ℝ) := (le_abs_self x).trans h
      linarith[hx.1]) (ae_iff.mp hv)
  rw[Real.volume_Ioc,show ((C : ℝ)+2)-((C : ℝ)+1)=1 by ring] at hz
  norm_num at hz

def brownianPastInput (U s t : ℝ≥0) : fullPredictableL2Q A f U :=
  intervalInputQ A f K hK hF U s t (shiftedProcess A f K s) (shiftedProcess_stronglyAdapted A f K s) (shifted_memLp_two A f K hK hF s)

theorem brownianPastIntegral_literal (U s t : ℝ≥0) (hst : s≤t) (htU : t≤U) :
    (fullIntegral A f K hK hF U (brownianPastInput A f K hK hF U s t) : (ℝ≥0→ℝ)→ℝ)=ᵐ[fullLaw A f]
      fun ω=>shiftedProcess A f K s ω*fullIncrement A f K s t ω :=
  integral_returns_unbounded_step A f K hK hF U s t hst htU _ (shiftedProcess_stronglyAdapted A f K s) (shifted_memLp_two A f K hK hF s)

omit hK hF in
private theorem lp_norm_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) (X : Lp ℝ 2 μ) : ‖X‖^2=∫ ω,X ω^2 ∂μ := by
  rw[←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only[real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

/-- Actual second moment of the returned unbounded-coefficient integral,
computed from SAME input's own-Q energy and actual W_s moment. -/
theorem brownianPastIntegral_energy (U s t : ℝ≥0) (hst : s≤t) (htU : t≤U) :
    (∫ ω,fullIntegral A f K hK hF U (brownianPastInput A f K hK hF U s t) ω^2 ∂fullLaw A f)=
      ((t : ℝ)-(s : ℝ))*(s : ℝ) := by
  rw[←lp_norm_sq,fullIntegral_norm]
  change ‖(brownianPastInput A f K hK hF U s t : Lp ℝ 2 (inputLawQ A f U))‖^2=_
  rw[lp_norm_sq]
  have he : (fun p=>(brownianPastInput A f K hK hF U s t : Lp ℝ 2 (inputLawQ A f U)) p^2)=ᵐ[inputLawQ A f U]
      fun p=>intervalIntegrand (shiftedProcess A f K s) s t p^2 :=
    (intervalInputQ_coe A f K hK hF U s t _ (shiftedProcess_stronglyAdapted A f K s) (shifted_memLp_two A f K hK hF s)).mono (fun _ h=>congrArg (fun x : ℝ=>x^2) h)
  rw[integral_congr_ae he,BrownianOwnQTimeInput.interval_energy A f K hK hF _ U s t hst htU,shifted_square_mean A f K hK hF s]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQUnboundedIntervalSource
