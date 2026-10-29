import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import UEOT.V3.RecoveryDynkin

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-!
Original commitment: continuous stochastic recovery must follow from the actual process.
Existing endpoint: `RecoveryDynkin.p_rec_02` consumes a Dynkin AC/ae-derivative certificate.
Premise reduced: construct that certificate from time-changed Brownian quadratic moments.
Model/witness: k>0, supplied real Brownian source, nonzero noise; Brownian existence remains OPEN.
Consumer: the same original P-REC-02, with actual source laws and squared distance to zero.

This conditional source adoption reuses the externally checked experiment
`whole-theory-audit-20261029/p11-independent/OUQuadraticDynkinSource.lean`
(SHA256 e874bc29526cfbec0cde3459c7ece2ca54a4df75ce4971c46569f43501bdc906).
It constructs the quadratic Dynkin output rather than accepting it as a premise.
Brownian-source realization, a conditional-transition/semigroup bridge, a
pathwise SDE identity, general C² Itô and Girsanov remain separate whole-theory
obligations. In particular, this module does not close P11.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A source-derived quadratic moment; no Dynkin/Itô conclusion is an input. -/
theorem brownian_quadratic_moment (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    (∫ ω, (B t ω)^2 ∂P) = (t : ℝ) := by
  simpa [covariance, hB.integral_eval, pow_two] using hB.covariance_eval t t

/-- Real affine source family, with all moment/integrability obligations derived
from Brownian finite-dimensional laws. -/
theorem affine_brownian_quadratic_moment
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) (m s : ℝ) :
    (∫ ω, (m+s*B t ω)^2 ∂P) = m^2+s^2*(t : ℝ) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hb : Integrable (B t) P := hB.integrable_eval t
  have hb2 : Integrable (fun ω => (B t ω)^2) P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.integrable_sq
  have heq : (fun ω => (m+s*B t ω)^2) =
      (fun ω => m^2 + (2*m*s)*(B t ω) + s^2*(B t ω)^2) := by
    funext ω; ring
  have hc : Integrable (fun _ω : Ω => m^2) P := integrable_const _
  have hl : Integrable (fun ω => (2*m*s)*(B t ω)) P := hb.const_mul _
  have hq : Integrable (fun ω => s^2*(B t ω)^2) P := hb2.const_mul _
  rw [heq]
  change (∫ ω, ((fun _ω : Ω => m^2) + (fun ω => (2*m*s)*(B t ω))) ω +
    (fun ω => s^2*(B t ω)^2) ω ∂P) = _
  rw [integral_add (hc.add hl) hq]
  simp only [Pi.add_apply]
  rw [integral_add hc hl]
  rw [integral_const_mul, integral_const_mul, hB.integral_eval,
    brownian_quadratic_moment hB t]
  simp


end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource


namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource
open scoped NNReal

noncomputable def ouClock (k : ℝ) (t : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal ((Real.exp (2*k*(t : ℝ))-1)/(2*k))

noncomputable def ouSource (B : ℝ≥0 → Ω → ℝ) (k s x0 : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-k*(t : ℝ))*x0 + (Real.exp (-k*(t : ℝ))*s)*B (ouClock k t) ω

/-- Explicit continuous-time OU candidate's quadratic moment, derived from the
same source Brownian law, not taken as a process certificate. The quadratic
right-time generator is derived below; conditional-transition/semigroup and
pathwise SDE bridges remain separate obligations. -/
theorem ou_source_quadratic_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (k s x0 : ℝ) (hk : 0 < k) (t : ℝ≥0) :
    (∫ ω, (ouSource B k s x0 t ω)^2 ∂P) =
      Real.exp (-2*k*(t : ℝ))*x0^2 + s^2/(2*k)*(1-Real.exp (-2*k*(t : ℝ))) := by
  have ht : 0 ≤ (t : ℝ) := t.coe_nonneg
  have hc : 0 ≤ (Real.exp (2*k*(t : ℝ))-1)/(2*k) :=
    div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))) (by positivity)
  change (∫ ω, (Real.exp (-k*(t : ℝ))*x0 +
    (Real.exp (-k*(t : ℝ))*s)*B (ouClock k t) ω)^2 ∂P) = _
  rw [affine_brownian_quadratic_moment hB]
  simp only [ouClock, Real.coe_toNNReal _ hc, mul_pow]
  have he : Real.exp (-k*(t : ℝ))^2 = Real.exp (-2*k*(t : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  have hp : Real.exp (-2*k*(t : ℝ))*Real.exp (2*k*(t : ℝ))=1 := by
    rw [← Real.exp_add]
    have hz : (-2*k*(t : ℝ))+(2*k*(t : ℝ)) = 0 := by ring
    rw [hz, Real.exp_zero]
  have hp' := congrArg (fun q : ℝ => s^2*q) hp
  field_simp [ne_of_gt hk]
  simp only [neg_mul] at hp'
  nlinarith

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource
open Set Filter
open scoped NNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

noncomputable def ouLaw (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (k s x0 t : ℝ) : Measure ℝ :=
  P.map (ouSource B k s x0 (Real.toNNReal t))

noncomputable def quadraticMean (k s x0 t : ℝ) : ℝ :=
  Real.exp (-2*k*t)*x0^2+s^2/(2*k)*(1-Real.exp (-2*k*t))

noncomputable def quadraticGenerator (k s x : ℝ) : ℝ := -2*k*x^2+s^2

lemma ou_source_aemeasurable (hB : IsPreBrownianReal B P) (k s x0 : ℝ) (t : ℝ≥0) :
    AEMeasurable (ouSource B k s x0 t) P := by
  exact aemeasurable_const.add (aemeasurable_const.mul (hB.aemeasurable _))

lemma ou_law_probability (hB : IsPreBrownianReal B P) (k s x0 t : ℝ) :
    IsProbabilityMeasure (ouLaw P B k s x0 t) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact Measure.isProbabilityMeasure_map (ou_source_aemeasurable hB k s x0 _)

lemma ou_law_quadratic_integrable (hB : IsPreBrownianReal B P) (k s x0 t : ℝ) :
    Integrable (fun x : ℝ => x^2) (ouLaw P B k s x0 t) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hG : MemLp (B (ouClock k (Real.toNNReal t))) 2 P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
  have hX : MemLp (ouSource B k s x0 (Real.toNNReal t)) 2 P := by
    unfold ouSource
    have hc : MemLp (fun _ω : Ω => Real.exp (-k*(Real.toNNReal t : ℝ))*x0) 2 P :=
      memLp_const _
    have hs : MemLp (fun ω => (Real.exp (-k*(Real.toNNReal t : ℝ))*s)*
      B (ouClock k (Real.toNNReal t)) ω) 2 P := hG.const_mul _
    exact hc.add hs
  have hphi : AEStronglyMeasurable (fun x : ℝ => x^2)
      (P.map (ouSource B k s x0 (Real.toNNReal t))) := by fun_prop
  exact (integrable_map_measure hphi (ou_source_aemeasurable hB k s x0 _)).2 hX.integrable_sq

lemma ou_law_quadratic_moment (hB : IsPreBrownianReal B P)
    (k s x0 : ℝ) (hk : 0 < k) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x, x^2 ∂ouLaw P B k s x0 t) = quadraticMean k s x0 t := by
  rw [ouLaw, integral_map (ou_source_aemeasurable hB k s x0 _) (by fun_prop)]
  simpa only [quadraticMean, Real.coe_toNNReal _ ht] using
    ou_source_quadratic_moment hB k s x0 hk (Real.toNNReal t)

lemma quadraticMean_hasDerivAt (k s x0 t : ℝ) (hk : 0 < k) :
    HasDerivAt (quadraticMean k s x0)
      (-2*k*quadraticMean k s x0 t+s^2) t := by
  have he := ((hasDerivAt_id t).const_mul (-2*k)).exp
  have hd := (he.mul_const (x0^2)).add
    ((hasDerivAt_const t (s^2/(2*k))).mul ((hasDerivAt_const t 1).sub he))
  convert hd using 1 <;> try rfl
  dsimp [quadraticMean]
  field_simp [ne_of_gt hk]
  ring

lemma ou_law_expected_generator (hB : IsPreBrownianReal B P)
    (k s x0 t : ℝ) :
    (∫ x, quadraticGenerator k s x ∂ouLaw P B k s x0 t) =
      -2*k*(∫ x, x^2 ∂ouLaw P B k s x0 t)+s^2 := by
  let := ou_law_probability hB k s x0 t
  change (∫ x, -2*k*x^2+s^2 ∂ouLaw P B k s x0 t) = _
  rw [integral_add ((ou_law_quadratic_integrable hB k s x0 t).const_mul _)
    (integrable_const _), integral_const_mul]
  simp

/-- Dynkin output is constructed for the actual time-changed Brownian source
and the actual quadratic drift, rather than supplied as a premise. -/
theorem ou_quadratic_dynkin (hB : IsPreBrownianReal B P)
    (k s x0 T : ℝ) (hk : 0 < k) (hT : 0 ≤ T) :
    UEOT.V3.RecoveryDynkin.DynkinExpectationCertificate
      (fun t => ∫ x, x^2 ∂ouLaw P B k s x0 t)
      (fun t => ∫ x, quadraticGenerator k s x ∂ouLaw P B k s x0 t) T := by
  have hEq : ∀ t, 0 ≤ t →
      (∫ x, x^2 ∂ouLaw P B k s x0 t) = quadraticMean k s x0 t :=
    fun t ht => ou_law_quadratic_moment hB k s x0 hk t ht
  constructor
  · apply ContDiffOn.absolutelyContinuousOnInterval
    apply (show ContDiffOn ℝ 1 (quadraticMean k s x0) (uIcc 0 T) from by
      unfold quadraticMean; fun_prop).congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact hEq t ht.1
  · filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht hne
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hne)
    have hevent : (fun t => ∫ x, x^2 ∂ouLaw P B k s x0 t) =ᶠ[𝓝 t]
        quadraticMean k s x0 := by
      filter_upwards [Ioi_mem_nhds htpos] with u hu
      exact hEq u hu.le
    rw [(quadraticMean_hasDerivAt k s x0 t hk).congr_of_eventuallyEq hevent |>.deriv,
      ou_law_expected_generator hB, hEq t ht.1]

/-- The original P-REC-02 consumes a source-derived certificate for this
continuous nonzero-noise family. The fully general C²/Itô/SDE source task remains. -/
theorem actual_source_p_rec_02 (hB : IsPreBrownianReal B P)
    (k s x0 T : ℝ) (hk : 0 < k) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T,
      (∫ x, x^2 ∂ouLaw P B k s x0 t) ≤
        Real.exp (-(2*k)*t)*x0^2+s^2/(2*k)*(1-Real.exp (-(2*k)*t)) := by
  suffices H : ∀ t ∈ Icc 0 T,
      (∫ x, x^2 ∂ouLaw P B k s x0 t) ≤
        (Real.exp (-(2*k)*t)*x0^2+s^2/(2*k)*(1-Real.exp (-(2*k)*t)))/1 by
    simpa only [div_one] using H
  apply UEOT.V3.RecoveryDynkin.p_rec_02 (ouLaw P B k s x0)
    (fun x => x^2) (quadraticGenerator k s) (fun x => x^2) x0
    (2*k) (s^2) 1 T (by positivity) (sq_nonneg _) (by norm_num) hT
  · intro t _; exact ou_law_probability hB k s x0 t
  · intro t _; exact ou_law_quadratic_integrable hB k s x0 t
  · intro t _
    let := ou_law_probability hB k s x0 t
    exact ((ou_law_quadratic_integrable hB k s x0 t).const_mul _).add (integrable_const _)
  · intro t _; exact ou_law_quadratic_integrable hB k s x0 t
  · exact ou_quadratic_dynkin hB k s x0 T hk hT
  · rw [ou_law_quadratic_moment hB k s x0 hk 0 (by norm_num)]
    simp [quadraticMean]
  · intro x; dsimp [quadraticGenerator]; ring_nf; rfl
  · intro x; simp

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource
open Set Filter
open scoped NNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The source has continuous paths whenever its actual driving Brownian
source does; no stochastic-integral or SDE representation is assumed here. -/
theorem ou_source_continuous (hB : IsBrownianReal B P) (k s x0 : ℝ) :
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => ouSource B k s x0 t ω) := by
  have hc : Continuous (ouClock k) := by unfold ouClock; fun_prop
  filter_upwards [hB.cont] with ω hω
  unfold ouSource
  have h0 : Continuous (fun t : ℝ≥0 => Real.exp (-k*(t : ℝ))*x0) := by fun_prop
  have h1 : Continuous (fun t : ℝ≥0 => Real.exp (-k*(t : ℝ))*s) := by fun_prop
  exact h0.add (h1.mul (hω.comp hc))

/-- The quadratic generator is identified by the actual source's infinitesimal
right-time transition expectation at every initial state, rather than assigned
independently of the process. This is only the quadratic observable domain. -/
theorem quadratic_generator_from_source (hB : IsPreBrownianReal B P)
    (k s x0 : ℝ) (hk : 0 < k) :
    HasDerivWithinAt (fun t => ∫ x, x^2 ∂ouLaw P B k s x0 t)
      (quadraticGenerator k s x0) (Ici 0) 0 := by
  have hd := (quadraticMean_hasDerivAt k s x0 0 hk).hasDerivWithinAt (s := Ici 0)
  have he := hd.congr_of_mem (fun t ht => ou_law_quadratic_moment hB k s x0 hk t ht)
    (by simp : (0 : ℝ) ∈ Ici 0)
  simpa [quadraticMean, quadraticGenerator] using he

/-- Positive execution noise gives a genuine random spread at positive time;
this source family is not a zero-noise or constant-process demonstration. -/
theorem nonzero_noise_positive_moment (hB : IsPreBrownianReal B P)
    (k s : ℝ) (hk : 0 < k) (hs : s ≠ 0) (t : ℝ≥0) (ht : 0 < t) :
    0 < ∫ ω, (ouSource B k s 0 t ω)^2 ∂P := by
  rw [ou_source_quadratic_moment hB k s 0 hk t]
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
  apply mul_pos (div_pos (sq_pos_of_ne_zero hs) (by positivity))
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have ht' : 0 < (t : ℝ) := ht
  nlinarith

/-- Nonempty parameter choices and a nonzero moment for every declared
Brownian source; existence of Brownian itself remains a separate obligation. -/
theorem positive_noise_parameter_witness (hB : IsPreBrownianReal B P) :
    (∃ k s : ℝ, 0 < k ∧ s ≠ 0 ∧
      0 < ∫ ω, (ouSource B k s 0 (1 : ℝ≥0) ω)^2 ∂P) := by
  exact ⟨1, 1, by norm_num, by norm_num,
    nonzero_noise_positive_moment hB 1 1 (by norm_num) (by norm_num) 1 (by norm_num)⟩

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The actual source starts at x0, not merely at a law with the same energy. -/
theorem ou_law_initial_dirac (hB : IsPreBrownianReal B P) (k s x0 : ℝ) :
    ouLaw P B k s x0 0 = Measure.dirac x0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hz : ouSource B k s x0 (0 : ℝ≥0) =ᵐ[P] fun _ => x0 := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    simp [ouSource, ouClock, hω]
  unfold ouLaw
  simp only [Real.toNNReal_zero]
  rw [Measure.map_congr hz]
  simp

/-- The quadratic observable is exactly squared distance to the recovery point. -/
theorem square_eq_distance_to_zero (x : ℝ) : x^2 = dist x 0 ^ 2 := by
  simp [sq_abs]
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The actual mean is derived from the same driving source, so a positive
centered second moment is an actual variance statement. -/
theorem ou_source_mean (hB : IsPreBrownianReal B P) (k s x0 : ℝ) (t : ℝ≥0) :
    (∫ ω, ouSource B k s x0 t ω ∂P) = Real.exp (-k*(t : ℝ))*x0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  change (∫ ω, Real.exp (-k*(t : ℝ))*x0 +
    (Real.exp (-k*(t : ℝ))*s)*B (ouClock k t) ω ∂P) = _
  rw [integral_add (integrable_const _) ((hB.integrable_eval _).const_mul _)]
  have hz : (∫ ω, (Real.exp (-k*(t : ℝ))*s)*B (ouClock k t) ω ∂P) = 0 := by
    rw [integral_const_mul,hB.integral_eval,mul_zero]
  rw [hz]
  simp

/-- The source variance is independent of the arbitrary actual initial state;
positive variance therefore cannot be attributed to a random initial seed. -/
theorem ou_source_variance (hB : IsPreBrownianReal B P) (k s x0 : ℝ)
    (hk : 0 < k) (t : ℝ≥0) :
    variance (ouSource B k s x0 t) P = s^2/(2*k)*(1-Real.exp (-2*k*(t : ℝ))) := by
  rw [variance_eq_integral (ou_source_aemeasurable hB k s x0 t),ou_source_mean hB]
  have hc (ω : Ω) : ouSource B k s x0 t ω - Real.exp (-k*(t : ℝ))*x0 =
      ouSource B k s 0 t ω := by unfold ouSource; ring
  simp_rw [hc]
  rw [ou_source_quadratic_moment hB k s 0 hk t]
  simp

theorem nonzero_noise_positive_variance (hB : IsPreBrownianReal B P)
    (k s x0 : ℝ) (hk : 0 < k) (hs : s ≠ 0) (t : ℝ≥0) (ht : 0 < t) :
    0 < variance (ouSource B k s x0 t) P := by
  rw [ou_source_variance hB k s x0 hk t]
  have h := nonzero_noise_positive_moment hB k s hk hs t ht
  rw [ou_source_quadratic_moment hB k s 0 hk t] at h
  simpa using h

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource
