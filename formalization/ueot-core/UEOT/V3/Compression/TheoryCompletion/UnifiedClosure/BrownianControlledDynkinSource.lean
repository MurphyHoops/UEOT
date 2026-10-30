import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledReadTimeSource
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
Original commitment: actual controlled generator expectation must supply original Dynkin AC and ae derivative, not an external analytic field.
Existing result: ONE fixed ownQ_A has actual controlled C2 expectation at EVERY U and actual bounded real control/initial state.
Premise reduced: derive measurable/bounded expected generator, real primitive, native AC and ae derivative despite possibly discontinuous predictable control.
Model/witness: actual X=x0+σB under SAME Q_A and action b/K, bounded first/second derivatives, arbitrary finite real R≥0 including zero.
Consumer/boundary: original DynkinExpectationCertificate, deterministic discount and actual ItoRun occupation source; no continuous-control, general-vector or infinite-reward conclusion assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledDynkinSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianTimeIntegrand BrownianPredictableInputs BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianBoundedC2DynkinSource BrownianControlledTestInput BrownianControlledC2Source BrownianControlledReadTimeSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem ac_congr {f g : ℝ → ℝ} {a c : ℝ} (hf : AbsolutelyContinuousOnInterval f a c)
    (he : EqOn f g (uIcc a c)) : AbsolutelyContinuousOnInterval g a c := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ,hδ,hδf⟩ := hf ε hε
  refine ⟨δ,hδ,fun E hE hlen => ?_⟩
  have hsum : (∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2))=
      ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← he (hE.left i hi).left,← he (hE.left i hi).right]
  rw [hsum]
  exact hδf E hE hlen

def expectedTest (A : ℝ≥0) (b : fullPredictableL2 A) (x₀ σ : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, φ (state x₀ σ t ω) ∂fullLaw A b

def expectedGenerator (A : ℝ≥0) (b : fullPredictableL2 A) (K x₀ σ : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, controlledGenerator σ φ (state x₀ σ t ω) (control A b K t ω) ∂fullLaw A b

def generatorBound (K σ C₁ C₂ : ℝ) : ℝ := |σ| * K * C₁+(σ^2/2)*C₂

variable (A : ℝ≥0) (b : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw A, |(b : Lp ℝ 2 (inputLaw A)) p|≤K)
    (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C₁ C₂ : ℝ) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (hb₁ : ∀ x, ‖deriv φ x‖≤C₁) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖≤C₂)
include hK hB hφ

theorem expectedGenerator_measurable : Measurable (expectedGenerator A b K x₀ σ φ) := by
  let _ := fullLaw_probability A b K hK hB
  have hm : Measurable (fun p : ℝ × (ℝ≥0 → ℝ) => controlledGenerator σ φ (state x₀ σ p.1 p.2) (control A b K p.1 p.2)) :=
    ((measurable_const.mul (control_joint A b K)).mul
      ((hφ.continuous_deriv (by norm_num : (1 : WithTop ℕ∞)≤2)).measurable.comp (state_joint x₀ σ))).add
      (measurable_const.mul ((hφ.continuous_iteratedDeriv' 2).measurable.comp (state_joint x₀ σ)))
  exact hm.stronglyMeasurable.integral_prod_right.measurable

include hb₁ hb₂
omit hB hφ in
theorem generator_point_bound (t : ℝ) (ω : ℝ≥0 → ℝ) :
    ‖controlledGenerator σ φ (state x₀ σ t ω) (control A b K t ω)‖≤generatorBound K σ C₁ C₂ := by
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul,norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (control_bound A b K hK _ _) (norm_nonneg σ))
      (hb₁ _) (norm_nonneg _) (by positivity)
  · rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ)≤σ^2/2)]
    exact mul_le_mul_of_nonneg_left (hb₂ _) (by positivity)

omit hφ in
theorem expectedGenerator_bound (t : ℝ) : ‖expectedGenerator A b K x₀ σ φ t‖≤generatorBound K σ C₁ C₂ := by
  let _ := fullLaw_probability A b K hK hB
  have h := norm_integral_le_of_norm_le_const (μ := fullLaw A b)
    (Eventually.of_forall (generator_point_bound A b K hK x₀ σ φ C₁ C₂ hb₁ hb₂ t))
  simpa only [expectedGenerator,probReal_univ,mul_one] using h

theorem expectedGenerator_intervalIntegrable (a c : ℝ) :
    IntervalIntegrable (expectedGenerator A b K x₀ σ φ) volume a c := by
  let _ : IsFiniteMeasure (volume.restrict (uIoc a c)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min a c) (max a c)))
    infer_instance
  rw [intervalIntegrable_iff]
  exact Integrable.of_bound (expectedGenerator_measurable A b K hK hB x₀ σ φ hφ).aestronglyMeasurable
    (generatorBound K σ C₁ C₂) (Eventually.of_forall (expectedGenerator_bound A b K hK hB x₀ σ φ C₁ C₂ hb₁ hb₂))

include hC₁ hC₂
/-- Actual real expected test is the primitive of the SAME expected actual
generator, at every nonnegative read time under ONE fixed Q_A. -/
theorem expectedTest_eq_primitive (t : ℝ) (ht : 0≤t) :
    expectedTest A b x₀ σ φ t=φ x₀+∫ s in (0 : ℝ)..t, expectedGenerator A b K x₀ σ φ s := by
  have h := actual_controlled_expectation_at A b K hK hB (Real.toNNReal t) x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂
  rw [Real.coe_toNNReal _ ht] at h
  change expectedTest A b x₀ σ φ t=φ x₀+∫ s, expectedGenerator A b K x₀ σ φ s ∂timeLaw (Real.toNNReal t) at h
  rw [h]
  congr 1
  change (∫ s in Icc 0 (Real.toNNReal t : ℝ), expectedGenerator A b K x₀ σ φ s)=_
  rw [Real.coe_toNNReal _ ht,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht]

/-- ORIGINAL analytic certificate is now derived for the actual controlled
source. Control may be merely predictable/measurable in time; native
Lebesgue differentiation supplies the required ae derivative. -/
theorem actual_controlled_dynkin (R : ℝ) (hR : 0≤R) :
    UEOT.V3.RecoveryDynkin.DynkinExpectationCertificate (expectedTest A b x₀ σ φ)
      (expectedGenerator A b K x₀ σ φ) R := by
  let ell := expectedGenerator A b K x₀ σ φ
  let primitive := fun t => φ x₀+∫ s in (0 : ℝ)..t, ell s
  have hi := expectedGenerator_intervalIntegrable A b K hK hB x₀ σ φ hφ C₁ C₂ hb₁ hb₂ 0 R
  have hc : (0 : ℝ)∈uIcc 0 R := left_mem_uIcc
  have hpc : AbsolutelyContinuousOnInterval primitive 0 R :=
    ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => φ x₀)).contDiffOn.absolutelyContinuousOnInterval).add
      (hi.absolutelyContinuousOnInterval_intervalIntegral hc)
  have heq := expectedTest_eq_primitive A b K hK hB x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂
  constructor
  · apply ac_congr hpc
    intro t ht
    rw [uIcc_of_le hR] at ht
    exact (heq t ht.1).symm
  · filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hi.ae_hasDerivAt_integral,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht hd hne
    have hpos : 0<t := lt_of_le_of_ne ht.1 (Ne.symm hne)
    have hm : t∈uIcc 0 R := by rwa [uIcc_of_le hR]
    have hp : HasDerivAt primitive (ell t) t := (hd hm 0 hc).const_add (φ x₀)
    have hev : expectedTest A b x₀ σ φ=ᶠ[𝓝 t] primitive := by
      filter_upwards [Ioi_mem_nhds hpos] with s hs
      exact heq s hs.le
    exact ((hp.congr_of_eventuallyEq hev).deriv)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledDynkinSource
