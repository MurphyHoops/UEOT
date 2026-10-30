import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianDeterministicGaussianIntegral
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUConditionalInnovationSource

/-!
Original commitment: physical OU needs actual exponential Brownian integral Gaussian law and clock variance on SAME canonical source.
Existing result: actual deterministic finite Gaussian left tables/native L2 integral and its mean/dt second moment are derived.
Premise reduced: compute the actual clipped exponential input/integral and derive its precise Gaussian law and original OU clock variance.
Model/witness: canonical source P/B, finite T, k≥0 bounded clipped weight equal exp(ks) on[0,T]; k>0 original clock law, k0 kept separately.
Consumer/boundary: actual physical Volterra/native integral identity and original conditional kernel/recovery next; no samplewise equality with old timechanged OU or desired Gaussian source is assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUExponentialGaussianIntegral
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianTimeIntegrand BrownianDeterministicGaussianIntegral OUQuadraticDynkinSource OUConditionalInnovationSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def weight (T : ℝ≥0) (k : ℝ) (u : ℝ≥0) : ℝ := Real.exp (k*(min u T : ℝ≥0))
theorem weight_continuous (T : ℝ≥0) (k : ℝ) : Continuous (weight T k) := by unfold weight; fun_prop

theorem weight_bound (T : ℝ≥0) (k : ℝ) (hk : 0≤k) (u : ℝ≥0) : ‖weight T k u‖≤Real.exp (k*T) := by
  unfold weight
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (show ((min u T : ℝ≥0) : ℝ)≤(T : ℝ) from min_le_right _ _) hk

def value (T : ℝ≥0) (k : ℝ) (hk : 0≤k) : Lp ℝ 2 sourceLaw :=
  integralValue T (weight T k) (weight_continuous T k) (Real.exp (k*T)) (Real.exp_pos _).le (weight_bound T k hk)

theorem value_gaussian (T : ℝ≥0) (k : ℝ) (hk : 0≤k) : HasGaussianLaw (value T k hk : (ℝ≥0→ℝ)→ℝ) sourceLaw :=
  integralValue_gaussian T (weight T k) (weight_continuous T k) (Real.exp (k*T)) (Real.exp_pos _).le (weight_bound T k hk)

theorem value_mean (T : ℝ≥0) (k : ℝ) (hk : 0≤k) : (∫ ω,value T k hk ω ∂sourceLaw)=0 :=
  integralValue_mean T (weight T k) (weight_continuous T k) (Real.exp (k*T)) (Real.exp_pos _).le (weight_bound T k hk)

theorem value_input (T : ℝ≥0) (k : ℝ) (hk : 0≤k) :
    (input T (weight T k) (weight_continuous T k) (Real.exp (k*T)) (Real.exp_pos _).le (weight_bound T k hk) : Lp ℝ 2 (BrownianTimeIntegrand.inputLaw T))=ᵐ[BrownianTimeIntegrand.inputLaw T]
      fun p => Real.exp (k*p.1) := by
  filter_upwards [input_coe T (weight T k) (weight_continuous T k) (Real.exp (k*T)) (Real.exp_pos _).le (weight_bound T k hk),
    BrownianPredictableInputs.time_support_ae T] with p hp ht
  rw [hp]
  unfold weight
  rw [min_eq_left ((Real.toNNReal_le_iff_le_coe).mpr ht.2),Real.coe_toNNReal _ ht.1.le]

/-- The native isometry computes the actual variance clock; no desired
Gaussian variance is entered as a field. Recovery's legitimate k>0 is explicit. -/
theorem value_second_moment (T : ℝ≥0) (k : ℝ) (hk : 0<k) :
    (∫ ω,value T k hk.le ω^2 ∂sourceLaw)=(ouClock k T : ℝ) := by
  rw [show (∫ ω,value T k hk.le ω^2 ∂sourceLaw)=
      ∫ s,weight T k (Real.toNNReal s)^2 ∂timeLaw T from
    integralValue_second_moment T (weight T k) (weight_continuous T k) (Real.exp (k*T)) (Real.exp_pos _).le (weight_bound T k hk.le)]
  have he : (fun s : ℝ => weight T k (Real.toNNReal s)^2)=ᵐ[timeLaw T] fun s => Real.exp ((2*k)*s) := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Icc (0 : ℝ) (T : ℝ)) measurableSet_Icc] with s hs
    unfold weight
    rw [min_eq_left ((Real.toNNReal_le_iff_le_coe).mpr hs.2),Real.coe_toNNReal _ hs.1,← Real.exp_nat_mul]
    congr 1
    ring
  rw [integral_congr_ae he,ouClock_coe k hk T]
  change (∫ s in Icc (0 : ℝ) (T : ℝ),Real.exp ((2*k)*s))=_
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le T.coe_nonneg]
  have hd (s : ℝ) : HasDerivAt (fun u => Real.exp ((2*k)*u)) ((2*k)*Real.exp ((2*k)*s)) s := by
    simpa only [id_eq,mul_one,one_mul,mul_comm] using (((hasDerivAt_id s).const_mul (2*k)).exp)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_hs : s∈uIcc (0 : ℝ) (T : ℝ)) => hd s)
    ((continuous_const.mul (Real.continuous_exp.comp (show Continuous (fun s : ℝ => (2*k)*s) from continuous_const.mul continuous_id))).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [mul_zero,Real.exp_zero] at hi
  apply (eq_div_iff (by positivity : 2*k≠0)).mpr
  nlinarith

theorem value_hasLaw (T : ℝ≥0) (k : ℝ) (hk : 0<k) :
    HasLaw (value T k hk.le) (gaussianReal 0 (ouClock k T)) sourceLaw := by
  have hv : variance (value T k hk.le : (ℝ≥0→ℝ)→ℝ) sourceLaw=(ouClock k T : ℝ) := by
    rw [variance_eq_sub (Lp.memLp (value T k hk.le))]
    change (∫ ω,value T k hk.le ω^2 ∂sourceLaw)-(∫ ω,value T k hk.le ω ∂sourceLaw)^2=_
    rw [value_second_moment T k hk,value_mean,zero_pow (by decide : (2 : ℕ)≠0),sub_zero]
  refine ⟨(Lp.aestronglyMeasurable (value T k hk.le)).aemeasurable,?_⟩
  rw [(value_gaussian T k hk.le).map_eq_gaussianReal,value_mean,hv,Real.toNNReal_coe]

/-- k=0 is the physical Brownian boundary. Old timechanged ouClock0=0 is
NOT used for this positive-time actual native integral. -/
theorem zero_rate_second_moment (T : ℝ≥0) : (∫ ω,value T 0 le_rfl ω^2 ∂sourceLaw)=(T : ℝ) := by
  rw [show (∫ ω,value T 0 le_rfl ω^2 ∂sourceLaw)=∫ s,weight T 0 (Real.toNNReal s)^2 ∂timeLaw T from
    integralValue_second_moment T (weight T 0) (weight_continuous T 0) (Real.exp (0*T)) (Real.exp_pos _).le (weight_bound T 0 le_rfl)]
  simp [weight,timeLaw,Measure.real,Real.volume_Icc]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUExponentialGaussianIntegral
