import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledDynkinSource

/-!
Original commitment: original ItoRun needs actual DISCOUNTED generator expectation under the same controlled run.
Existing result: fixed ownQ_A actual expected test/generator owns a derived ORIGINAL Dynkin AC/ae derivative certificate at all finite read times.
Premise reduced: derive actual discounted expectation via native AC integration by parts, with actual pointwise generator-minus-discount integrand.
Model/witness: SAME fixed b/A/Q and actual real action, bounded C2 derivatives, arbitrary finite read horizon including zero; finite identity permits any real rho.
Consumer/boundary: actual discounted occupation and original ItoRun next; positive rho/infinite-reward/control-family obligations are not input fields here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledDiscountSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianTimeIntegrand BrownianPredictableInputs BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianBoundedC2DynkinSource BrownianControlledTestInput BrownianControlledC2Source BrownianControlledReadTimeSource BrownianControlledDynkinSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def discount (ρ t : ℝ) : ℝ := Real.exp (-ρ*t)
theorem discount_hasDerivAt (ρ t : ℝ) : HasDerivAt (discount ρ) (-ρ*discount ρ t) t := by
  change HasDerivAt (fun x : ℝ => Real.exp (-ρ*x)) (-ρ*Real.exp (-ρ*t)) t
  simpa only [id_eq,mul_one,mul_comm] using ((hasDerivAt_id t).const_mul (-ρ)).exp

variable (A : ℝ≥0) (b : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw A, |(b : Lp ℝ 2 (inputLaw A)) p|≤K)
    (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C₁ C₂ : ℝ) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (hb₁ : ∀ x, ‖deriv φ x‖≤C₁) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖≤C₂)
include hK hB hφ hC₁ hC₂ hb₁ hb₂

/-- Discounted expected-test identity is DERIVED from actual native AC,
using integration by parts; no desired discounted Ito field is supplied. -/
theorem actual_discounted_primitive (ρ R : ℝ) (hR : 0≤R) :
    discount ρ R*expectedTest A b x₀ σ φ R=φ x₀+
      ∫ t in (0 : ℝ)..R, discount ρ t*(expectedGenerator A b K x₀ σ φ t-ρ*expectedTest A b x₀ σ φ t) := by
  let m := expectedTest A b x₀ σ φ
  let ell := expectedGenerator A b K x₀ σ φ
  let e := discount ρ
  have hDyn := actual_controlled_dynkin A b K hK hB x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂ R hR
  have heAC : AbsolutelyContinuousOnInterval e 0 R :=
    (show ContDiff ℝ 1 e by unfold e discount; fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hprod := heAC.integral_deriv_mul_eq_sub hDyn.ac
  have hder : ∀ᵐ t ∂volume, t∈Icc 0 R → deriv m t=ell t :=
    (ae_restrict_iff' measurableSet_Icc).mp hDyn.deriv_eq
  have hInt : (∫ t in (0 : ℝ)..R, deriv e t*m t+e t*deriv m t)=
      ∫ t in (0 : ℝ)..R, e t*(ell t-ρ*m t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hder] with t hd ht
    have hm : t∈Icc 0 R := by simpa only [uIcc_of_le hR] using (uIoc_subset_uIcc ht)
    rw [(discount_hasDerivAt ρ t).deriv,hd hm]
    ring
  have hm0 : m 0=φ x₀ := by
    have h := expectedTest_eq_primitive A b K hK hB x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂ 0 le_rfl
    simpa only [intervalIntegral.integral_same,add_zero] using h
  change expectedTest A b x₀ σ φ 0=φ x₀ at hm0
  rw [hInt,show e 0=1 by simp [e,discount],hm0,one_mul] at hprod
  change (∫ t in (0 : ℝ)..R, e t*(ell t-ρ*m t))=e R*m R-φ x₀ at hprod
  change e R*m R=φ x₀+_
  linarith

omit hC₁ hC₂ in
/-- Actual generator is Q-integrable at every real read clock. -/
theorem generator_read_integrable (t : ℝ) :
    Integrable (fun ω => controlledGenerator σ φ (state x₀ σ t ω) (control A b K t ω)) (fullLaw A b) := by
  let _ := fullLaw_probability A b K hK hB
  have hm : Measurable (fun ω => controlledGenerator σ φ (state x₀ σ t ω) (control A b K t ω)) :=
    ((measurable_const.mul ((control_joint A b K).comp (measurable_const.prodMk measurable_id))).mul
      ((hφ.continuous_deriv (by norm_num : (1 : WithTop ℕ∞)≤2)).measurable.comp (state_measurable x₀ σ t))).add
      (measurable_const.mul ((hφ.continuous_iteratedDeriv' 2).measurable.comp (state_measurable x₀ σ t)))
  exact Integrable.of_bound hm.aestronglyMeasurable (generatorBound K σ C₁ C₂)
    (Eventually.of_forall (generator_point_bound A b K hK x₀ σ φ C₁ C₂ hb₁ hb₂ t))

theorem test_read_integrable (t : ℝ) : Integrable (fun ω => φ (state x₀ σ t ω)) (fullLaw A b) := by
  have h := state_test_integrable_at A b K hK hB (Real.toNNReal t) x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂
  simpa only [state,Real.toNNReal_coe] using h

/-- Native expectation algebra retains the actual joint state/action
readout; it is not an independently declared occupation drift. -/
theorem expected_discount_drift (ρ t : ℝ) :
    expectedGenerator A b K x₀ σ φ t-ρ*expectedTest A b x₀ σ φ t=
      ∫ ω, controlledGenerator σ φ (state x₀ σ t ω) (control A b K t ω)-ρ*φ (state x₀ σ t ω) ∂fullLaw A b := by
  rw [integral_sub (generator_read_integrable A b K hK hB x₀ σ φ hφ C₁ C₂ hb₁ hb₂ t)
    ((test_read_integrable A b K hK hB x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂ t).const_mul ρ),integral_const_mul]
  rfl

/-- Actual discounted Ito expectation in the original dt×SAME-Q form,
ready for the actual occupation pushforward consumer. -/
theorem actual_discounted_expectation (ρ : ℝ) (U : ℝ≥0) :
    discount ρ U*(∫ ω, φ (state x₀ σ U ω) ∂fullLaw A b)=φ x₀+
      ∫ t, discount ρ t*(∫ ω, controlledGenerator σ φ (state x₀ σ t ω) (control A b K t ω)-
        ρ*φ (state x₀ σ t ω) ∂fullLaw A b) ∂timeLaw U := by
  have h := actual_discounted_primitive A b K hK hB x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂ ρ U U.coe_nonneg
  change discount ρ U*expectedTest A b x₀ σ φ U=φ x₀+_
  rw [timeLaw,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le U.coe_nonneg]
  simp_rw [← expected_discount_drift A b K hK hB x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂]
  exact h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledDiscountSource
