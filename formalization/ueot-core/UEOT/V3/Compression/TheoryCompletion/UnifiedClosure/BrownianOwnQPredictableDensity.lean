import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQHorizonTargetIntegral
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQIntegralMartingale

/-!
Original commitment: the ACTUAL own-Q integral must consume all original-filtration predictable L2 inputs, not an externally supplied closure membership.
Existing result: actual own-Q elementary closure isometry/process and original-P bounded target inputs in that SAME Q closure are derived.
Premise reduced: native Q-predictable representative, bounded clipping and actual Q-L2 dominated convergence derive exact equality with native lpMeas.
Model/witness: SAME fixed Q_A/W/original Fs, any finite integration horizon U incl U>A and U0; no natural-filtration equality or independent noise.
Consumer/boundary: actual full predictable own-Q integral, originalFs martingale/cutoff energy; continuous modification/unbounded literal interval consumer remain separate successors.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQPredictableDensity
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs BrownianIntegralClosure
open BrownianBoundedExponentialLimitSource BrownianOwnQTimeInput BrownianOwnQIntegralClosure BrownianOwnQBoundedInput
open BrownianOwnQHorizonTargetIntegral BrownianContinuousAdaptedInputs BrownianBoundedPredictableApproximation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory RealInnerProductSpace
noncomputable section
variable (A : ℝ≥0) (f : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hF : ∀ᵐ p ∂inputLaw A, |(f : Lp ℝ 2 (inputLaw A)) p|≤K)

/-- Independently defined full domain: native ORIGINAL predictable sigma, actual dtU times SAME Q. -/
def fullPredictableL2Q (U : ℝ≥0) : Submodule ℝ (Lp ℝ 2 (inputLawQ A f U)) :=
  lpMeas ℝ ℝ predictableSigma 2 (inputLawQ A f U)

theorem fullPredictableL2Q_closed (U : ℝ≥0) : IsClosed (fullPredictableL2Q A f U : Set (Lp ℝ 2 (inputLawQ A f U))) :=
  isClosed_aestronglyMeasurable predictableSigma_le

def representativeQ (U : ℝ≥0) (g : fullPredictableL2Q A f U) : ℝ×(ℝ≥0→ℝ)→ℝ :=
  (mem_lpMeas_iff_aestronglyMeasurable.mp g.property).mk (g : Lp ℝ 2 (inputLawQ A f U))

theorem representativeQ_predictable (U : ℝ≥0) (g : fullPredictableL2Q A f U) :
    StronglyMeasurable[predictableSigma] (representativeQ A f U g) :=
  (mem_lpMeas_iff_aestronglyMeasurable.mp g.property).stronglyMeasurable_mk

theorem representativeQ_ae (U : ℝ≥0) (g : fullPredictableL2Q A f U) :
    (g : Lp ℝ 2 (inputLawQ A f U))=ᵐ[inputLawQ A f U] representativeQ A f U g :=
  (mem_lpMeas_iff_aestronglyMeasurable.mp g.property).ae_eq_mk

private theorem clip_cont (c : ℝ) : Continuous (clip c) := continuous_const.max (continuous_const.min continuous_id)
private theorem clip_bound (c : ℝ) (hc : 0≤c) (x : ℝ) : ‖clip c x‖≤c := by
  rw[Real.norm_eq_abs,abs_le]
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩
private theorem clip_fixed (c x : ℝ) (h : |x|≤c) : clip c x=x := by
  rcases abs_le.mp h with ⟨hl,hu⟩
  simp only[clip,min_eq_right hu,max_eq_right hl]
private theorem clip_norm_le (c : ℝ) (hc : 0≤c) (x : ℝ) : ‖clip c x‖≤‖x‖ := by
  rw[Real.norm_eq_abs,Real.norm_eq_abs,abs_le]
  constructor
  · exact (le_min (by linarith[abs_nonneg x]) (neg_abs_le x)).trans (le_max_right _ _)
  · exact max_le (by linarith[abs_nonneg x]) ((min_le_right _ _).trans (le_abs_self x))

def clipped (U : ℝ≥0) (g : fullPredictableL2Q A f U) (n : ℕ) : ℝ×(ℝ≥0→ℝ)→ℝ :=
  fun p=>clip (n : ℝ) (representativeQ A f U g p)

theorem clipped_predictable (U : ℝ≥0) (g : fullPredictableL2Q A f U) (n : ℕ) :
    StronglyMeasurable[predictableSigma] (clipped A f U g n) :=
  (clip_cont n).comp_stronglyMeasurable (representativeQ_predictable A f U g)

include hK hF

omit hK hF in
private theorem clipped_memLp_P (U : ℝ≥0) (g : fullPredictableL2Q A f U) (n : ℕ) :
    MemLp (clipped A f U g n) 2 (inputLaw U) :=
  MemLp.of_bound ((clipped_predictable A f U g n).mono predictableSigma_le).aestronglyMeasurable n
    (Eventually.of_forall (fun _=>clip_bound _ (Nat.cast_nonneg n) _))

/-- Bounded actual Q representative becomes a legitimate bounded native P
input solely as an approximation device. It is never substituted for g. -/
def clippedInputP (U : ℝ≥0) (g : fullPredictableL2Q A f U) (n : ℕ) : fullPredictableL2 U :=
  ⟨(clipped_memLp_P A f U g n).toLp (clipped A f U g n),
    mem_lpMeas_iff_aestronglyMeasurable.mpr (((clipped_predictable A f U g n).aestronglyMeasurable).congr (clipped_memLp_P A f U g n).coeFn_toLp.symm)⟩

omit hK hF in
theorem clippedInputP_bound (U : ℝ≥0) (g : fullPredictableL2Q A f U) (n : ℕ) :
    ∀ᵐ p ∂inputLaw U, |(clippedInputP A f U g n : Lp ℝ 2 (inputLaw U)) p|≤(n : ℝ) := by
  filter_upwards [(clipped_memLp_P A f U g n).coeFn_toLp] with p hp
  change (clippedInputP A f U g n : Lp ℝ 2 (inputLaw U)) p=clipped A f U g n p at hp
  rw[hp]
  change |clip (n : ℝ) (representativeQ A f U g p)|≤(n : ℝ)
  simpa only[Real.norm_eq_abs] using clip_bound (n : ℝ) (Nat.cast_nonneg n) (representativeQ A f U g p)

private theorem clipped_memLp_Q (U : ℝ≥0) (g : fullPredictableL2Q A f U) (n : ℕ) :
    MemLp (clipped A f U g n) 2 (inputLawQ A f U) := by
  let _:=fullLaw_probability A f K hK hF
  have : IsFiniteMeasure (inputLawQ A f U) := by unfold inputLawQ;infer_instance
  exact MemLp.of_bound ((clipped_predictable A f U g n).mono predictableSigma_le).aestronglyMeasurable n
    (Eventually.of_forall (fun _=>clip_bound _ (Nat.cast_nonneg n) _))

def clippedInputQ (U : ℝ≥0) (g : fullPredictableL2Q A f U) (n : ℕ) : Lp ℝ 2 (inputLawQ A f U) :=
  (clipped_memLp_Q A f K hK hF U g n).toLp (clipped A f U g n)

theorem clippedInputQ_coe (U : ℝ≥0) (g : fullPredictableL2Q A f U) (n : ℕ) :
    clippedInputQ A f K hK hF U g n=ᵐ[inputLawQ A f U] clipped A f U g n :=
  (clipped_memLp_Q A f K hK hF U g n).coeFn_toLp

/-- Every actual bounded clip enters the EXISTING own-Q closure by the
already proved bounded target-input consumer, not an external density field. -/
theorem clippedInputQ_mem_domain (U : ℝ≥0) (g : fullPredictableL2Q A f U) (n : ℕ) :
    clippedInputQ A f K hK hF U g n∈integralDomain A f K hK hF U := by
  let q:=clippedInputP A f U g n
  have hb:=clippedInputP_bound A f U g n
  have he : clippedInputQ A f K hK hF U g n=targetInputValueQ A f K hK hF U q n (Nat.cast_nonneg n) := by
    apply Lp.ext
    have hp : BrownianBoundedPredictableApproximation.boundedRepresentative U q n=ᵐ[inputLaw U] clipped A f U g n :=
      (boundedRepresentative_ae U q n hb).symm.trans (clipped_memLp_P A f U g n).coeFn_toLp
    filter_upwards [(clipped_memLp_Q A f K hK hF U g n).coeFn_toLp,
      targetInputValueQ_coe A f K hK hF U q n (Nat.cast_nonneg n),
      (inputLawQ_absolutelyContinuous A f U).ae_le hp] with p hc ht hp
    change clippedInputQ A f K hK hF U g n p=clipped A f U g n p at hc
    rw[hc,ht,hp]
  rw[he]
  exact targetInput_mem_domain A f K hK hF U q n (Nat.cast_nonneg n) hb

/-- Actual Q-L2 convergence to SAME g, from exact native predictable
representative, eventual pointwise clipping identity and genuine L2 domination. -/
theorem clippedInputQ_tendsto (U : ℝ≥0) (g : fullPredictableL2Q A f U) :
    Tendsto (fun n=>clippedInputQ A f K hK hF U g n) atTop (𝓝 (g : Lp ℝ 2 (inputLawQ A f U))) := by
  let R:=representativeQ A f U g
  have hR : MemLp R 2 (inputLawQ A f U) := (memLp_congr_ae (representativeQ_ae A f U g)).mp (Lp.memLp g.val)
  have hc (n : ℕ) : MemLp (clipped A f U g n) 2 (inputLawQ A f U) := clipped_memLp_Q A f K hK hF U g n
  have hlim (p : ℝ×(ℝ≥0→ℝ)) : Tendsto (fun n=>clipped A f U g n p) atTop (𝓝 (R p)) := by
    obtain ⟨N,hN⟩:=exists_nat_ge |R p|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (clip_fixed n (R p) (hN.trans (by exact_mod_cast hn))).symm
  have hs : Tendsto (fun n=>∫ p,(clipped A f U g n p-R p)^2 ∂inputLawQ A f U) atTop (𝓝 0) := by
    have hb (n : ℕ) : ∀ᵐ p ∂inputLawQ A f U, ‖(clipped A f U g n p-R p)^2‖≤4*(R p)^2 := by
      exact Eventually.of_forall (fun p=>by
        rw[norm_pow]
        have hclip : ‖clipped A f U g n p‖≤‖R p‖ := clip_norm_le n (Nat.cast_nonneg n) (R p)
        have h:‖clipped A f U g n p-R p‖≤2*‖R p‖ :=
          (norm_sub_le _ _).trans (by linarith)
        have he:=(sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*‖R p‖)).mpr h
        simpa only[mul_pow,Real.norm_eq_abs,sq_abs,show (2 : ℝ)^2=4 by norm_num] using he)
    have ht : ∀ᵐ p ∂inputLawQ A f U,Tendsto (fun n=>(clipped A f U g n p-R p)^2) atTop (𝓝 0) :=
      Eventually.of_forall (fun p=>by simpa only[sub_self,zero_pow (by decide : (2 : ℕ)≠0)] using ((hlim p).sub_const (R p)).pow 2)
    simpa only[integral_zero,Pi.pow_apply,Pi.sub_apply] using tendsto_integral_of_dominated_convergence (fun p=>4*(R p)^2)
      (fun n=>((hc n).aestronglyMeasurable.sub hR.aestronglyMeasurable).pow 2) (hR.integrable_sq.const_mul 4) hb ht
  have hn (n : ℕ) : ‖clippedInputQ A f K hK hF U g n-g.val‖^2=
      ∫ p,(clipped A f U g n p-R p)^2 ∂inputLawQ A f U := by
    rw[←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (clippedInputQ A f K hK hF U g n) g.val,(hc n).coeFn_toLp,representativeQ_ae A f U g] with p hs hc hg
    change (clippedInputQ A f K hK hF U g n-g.val) p=clippedInputQ A f K hK hF U g n p-g.val p at hs
    change clippedInputQ A f K hK hF U g n p=clipped A f U g n p at hc
    rw[hs,hc,hg]
    simp[Real.norm_eq_abs,sq_abs,R]
  rw[tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun n=>‖clippedInputQ A f K hK hF U g n-g.val‖^2) atTop (𝓝 0) := (tendsto_congr' (Eventually.of_forall hn)).mpr hs
  have h:=Real.continuous_sqrt.tendsto (0 : ℝ) |>.comp hsq
  simpa only[Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using h

/-- The reverse inclusion is now proved for EVERY native original-predictable Q-L2 class. -/
theorem fullPredictableL2Q_le_domain (U : ℝ≥0) : fullPredictableL2Q A f U≤ integralDomain A f K hK hF U := by
  intro g hg
  exact (elementarySpan A f K hK hF U).isClosed_topologicalClosure.mem_of_tendsto
    (clippedInputQ_tendsto A f K hK hF U ⟨g,hg⟩) (Eventually.of_forall (clippedInputQ_mem_domain A f K hK hF U ⟨g,hg⟩))

theorem elementary_input_predictable_Q {U : ℝ≥0} (r : ElementaryInput U) :
    inputValueQ A f K hK hF r∈fullPredictableL2Q A f U := by
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  have hm : StronglyMeasurable[predictableSigma] (integrand r.clock r.coefficient) := by
    have h : StronglyMeasurable[predictableSigma] (∑ i : Fin r.n,intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ)) :=
      Finset.stronglyMeasurable_sum Finset.univ (fun i _=>intervalIntegrand_predictable (r.clock i.castSucc) (r.clock i.succ) (r.coefficient_past i))
    convert! h using 1
    ext p
    simp only[integrand,Finset.sum_apply]
  exact hm.aestronglyMeasurable.congr (BrownianOwnQTimeInput.integrand_memLp_two A f K hK hF r).coeFn_toLp.symm

theorem domain_le_fullPredictableL2Q (U : ℝ≥0) : integralDomain A f K hK hF U≤fullPredictableL2Q A f U := by
  apply (elementarySpan A f K hK hF U).topologicalClosure_minimal _ (fullPredictableL2Q_closed A f U)
  rw[BrownianOwnQIntegralClosure.elementarySpan_eq_span]
  exact Submodule.span_le.mpr (by rintro _ ⟨r,rfl⟩;exact elementary_input_predictable_Q A f K hK hF r)

/-- Exact equality is DERIVED, never used to define the native full domain. -/
theorem integralDomain_eq_fullPredictableL2Q (U : ℝ≥0) : integralDomain A f K hK hF U=fullPredictableL2Q A f U :=
  le_antisymm (domain_le_fullPredictableL2Q A f K hK hF U) (fullPredictableL2Q_le_domain A f K hK hF U)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQPredictableDensity
