import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledHorizonTestInput
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledC2Source

/-!
Original commitment: original ItoRun needs all-read-time analytic identities under ONE actual controlled law.
Existing result: original scalar Ito, actual C2 source and fixed ownQ_A target integration/cross drift for every U.
Premise reduced: derive controlled C2 expectation and integrability at every U while b/A/Q stay FIXED; no family of replacement normalized measures.
Model/witness: X=x0+σ originalB and SAME real progressive control masked at A, bounded first/second derivatives, A=0/U=0 independently.
Consumer/boundary: actual expected-generator AC, discounted occupation and infinite-reward/control-family source next; no desired ItoRun field or vector/general-filter closure.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledReadTimeSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralWeightedQV BrownianIntegralContinuousVersion BrownianScalarItoSource BrownianIntegralTimeEnergy
open BrownianBoundedControlSource BrownianBoundedExponentialLimitSource BrownianBoundedC2DynkinSource
open BrownianOwnQBoundedInput BrownianControlledTestInput BrownianControlledC2Source BrownianControlledHorizonTestInput
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (A : ℝ≥0) (b : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw A, |(b : Lp ℝ 2 (inputLaw A)) p|≤K) (U : ℝ≥0)
    (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C₁ C₂ : ℝ) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (hb₁ : ∀ x, ‖deriv φ x‖≤C₁) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖≤C₂)
include hK hB hφ hb₂

theorem secondRaw_integrable_at : Integrable (secondRaw x₀ σ φ) (BrownianOwnQTimeInput.inputLawQ A b U) := by
  let _ := fullLaw_probability A b K hK hB
  have : IsFiniteMeasure (BrownianOwnQTimeInput.inputLawQ A b U) := by unfold BrownianOwnQTimeInput.inputLawQ; infer_instance
  apply Integrable.of_bound
    (measurable_const.mul ((hφ.continuous_iteratedDeriv' 2).measurable.comp (state_joint x₀ σ))).aestronglyMeasurable (σ^2*C₂)
  exact Eventually.of_forall (fun p => by
    change ‖σ^2*iteratedDeriv 2 φ (state x₀ σ p.1 p.2)‖≤_
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg σ)]
    exact mul_le_mul_of_nonneg_left (hb₂ _) (sq_nonneg σ))

theorem secondEnergy_integrable_at : Integrable (itoSecondEnergy U (constantInput U σ) (shiftedTest x₀ φ)) (fullLaw A b) := by
  let _ := fullLaw_probability A b K hK hB
  have he : weightedTimeIntegrand U (fun u ω => iteratedDeriv 2 (shiftedTest x₀ φ)
      (continuousIntegralProcess U (constantInput U σ) u ω)) (constantInput U σ)=ᵐ[BrownianOwnQTimeInput.inputLawQ A b U]
      secondRaw x₀ σ φ :=
    (inputLawQ_absolutelyContinuous A b U).ae_le (constantInput_second_integrand U x₀ σ φ)
  have hi := (secondRaw_integrable_at A b K hK hB U x₀ σ φ hφ C₂ hb₂).congr he.symm
  exact hi.integral_prod_right

theorem secondEnergy_mean_at : (∫ ω, itoSecondEnergy U (constantInput U σ) (shiftedTest x₀ φ) ω ∂fullLaw A b)=
    ∫ t, ∫ ω, secondRaw x₀ σ φ (t,ω) ∂fullLaw A b ∂timeLaw U := by
  let _ := fullLaw_probability A b K hK hB
  have he : weightedTimeIntegrand U (fun u ω => iteratedDeriv 2 (shiftedTest x₀ φ)
      (continuousIntegralProcess U (constantInput U σ) u ω)) (constantInput U σ)=ᵐ[BrownianOwnQTimeInput.inputLawQ A b U]
      secondRaw x₀ σ φ :=
    (inputLawQ_absolutelyContinuous A b U).ae_le (constantInput_second_integrand U x₀ σ φ)
  have hi := (secondRaw_integrable_at A b K hK hB U x₀ σ φ hφ C₂ hb₂).congr he.symm
  unfold itoSecondEnergy weightedTimeEnergy
  exact (integral_prod_symm _ hi).symm.trans ((integral_congr_ae he).trans
    (integral_prod _ (secondRaw_integrable_at A b K hK hB U x₀ σ φ hφ C₂ hb₂)))

include hC₁ hC₂ hb₁
omit hK hB in
/-- Actual Ito path identity is inherited by Q absolute continuity and is
bound to the original returned test input, rather than a new noise field. -/
theorem actual_ito_identity_at : (fun ω => φ (state x₀ σ U ω))=ᵐ[fullLaw A b] fun ω => φ x₀+
    (predictableIntegral U (testInput U x₀ σ φ hφ C₁ hC₁ hb₁) : (ℝ≥0 → ℝ) → ℝ) ω+
      (1/2 : ℝ)*itoSecondEnergy U (constantInput U σ) (shiftedTest x₀ φ) ω := by
  have hψ : ContDiff ℝ 2 (shiftedTest x₀ φ) := hφ.comp (contDiff_const.add contDiff_id)
  have hbψ₁ : ∀ x, ‖deriv (shiftedTest x₀ φ) x‖≤C₁ := by
    intro x
    rw [show deriv (shiftedTest x₀ φ) x=deriv φ (x₀+x) from shift_deriv φ x₀ x]
    exact hb₁ _
  have hbψ₂ : ∀ x, ‖iteratedDeriv 2 (shiftedTest x₀ φ) x‖≤C₂ := by
    intro x
    rw [show iteratedDeriv 2 (shiftedTest x₀ φ) x=iteratedDeriv 2 φ (x₀+x) from shift_second φ x₀ x]
    exact hb₂ _
  have hito := actual_scalar_ito U (constantInput U σ) (shiftedTest x₀ φ) hψ C₁ C₂ hC₁ hC₂ hbψ₁ hbψ₂
  apply (fullLaw_absolutelyContinuous A b).ae_le
  filter_upwards [hito,constantInput_process U σ,continuousIntegralProcess_horizon U (testInput U x₀ σ φ hφ C₁ hC₁ hb₁)] with ω hi hp hg
  change shiftedTest x₀ φ (continuousIntegralProcess U (constantInput U σ) U ω)=
    shiftedTest x₀ φ 0+continuousIntegralProcess U (testInput U x₀ σ φ hφ C₁ hC₁ hb₁) U ω+
      (1/2 : ℝ)*itoSecondEnergy U (constantInput U σ) (shiftedTest x₀ φ) ω at hi
  rw [hp U le_rfl,hg] at hi
  simpa only [shiftedTest,state,Real.toNNReal_coe,add_zero] using hi

/-- Genuine expectation of the controlled diffusion source, with actual
generator and action readouts. It is not supplied as an ItoRun field. -/
theorem actual_controlled_expectation_at : (∫ ω, φ (state x₀ σ U ω) ∂fullLaw A b)=φ x₀+
    ∫ t, ∫ ω, controlledGenerator σ φ (state x₀ σ t ω) (control A b K t ω) ∂fullLaw A b ∂timeLaw U := by
  let _ := fullLaw_probability A b K hK hB
  let g := testInput U x₀ σ φ hφ C₁ hC₁ hb₁
  have hI := BrownianOwnQHorizonTargetShift.target_baseline_integrable A b K hK hB U g (C₁*|σ|) (mul_nonneg hC₁ (abs_nonneg _))
    (testInput_bound U x₀ σ φ hφ C₁ hC₁ hb₁)
  have hA := secondEnergy_integrable_at A b K hK hB U x₀ σ φ hφ C₂ hb₂
  dsimp only [g] at hI
  rw [integral_congr_ae (actual_ito_identity_at A b U x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂),
    integral_add (f := fun ω => φ x₀+(predictableIntegral U (testInput U x₀ σ φ hφ C₁ hC₁ hb₁) : (ℝ≥0 → ℝ) → ℝ) ω)
      (g := fun ω => (1/2 : ℝ)*itoSecondEnergy U (constantInput U σ) (shiftedTest x₀ φ) ω)
      ((integrable_const _).add hI) (hA.const_mul _),
    integral_add (f := fun _ => φ x₀) (integrable_const _) hI,
    integral_const,probReal_univ,one_smul,integral_const_mul,
    test_integral_mean_at A b K hK hB U x₀ σ φ hφ C₁ hC₁ hb₁,
    secondEnergy_mean_at A b K hK hB U x₀ σ φ hφ C₂ hb₂]
  have hiFirst := firstDrift_integrable_at A b K hK hB U x₀ σ φ hφ C₁ hb₁
  have hiSecond := secondRaw_integrable_at A b K hK hB U x₀ σ φ hφ C₂ hb₂
  rw [add_assoc,← integral_const_mul,← integral_add hiFirst.integral_prod_left (hiSecond.integral_prod_left.const_mul (1/2 : ℝ))]
  apply congrArg (fun z : ℝ => φ x₀+z)
  apply integral_congr_ae
  filter_upwards [hiFirst.prod_right_ae,hiSecond.prod_right_ae] with t ht₁ ht₂
  rw [← integral_const_mul,← integral_add ht₁ (ht₂.const_mul (1/2 : ℝ))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω => by unfold controlledGenerator firstDrift secondRaw; ring)

/-- Terminal test integrability is derived from actual Ito and the actual
Q-integrability of its constructed noise and correction terms. -/
theorem state_test_integrable_at : Integrable (fun ω => φ (state x₀ σ U ω)) (fullLaw A b) := by
  let _ := fullLaw_probability A b K hK hB
  have hI := BrownianOwnQHorizonTargetShift.target_baseline_integrable A b K hK hB U (testInput U x₀ σ φ hφ C₁ hC₁ hb₁)
    (C₁*|σ|) (mul_nonneg hC₁ (abs_nonneg _)) (testInput_bound U x₀ σ φ hφ C₁ hC₁ hb₁)
  exact (((integrable_const (φ x₀)).add hI).add
    ((secondEnergy_integrable_at A b K hK hB U x₀ σ φ hφ C₂ hb₂).const_mul (1/2 : ℝ))).congr
      (actual_ito_identity_at A b U x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂).symm

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledReadTimeSource
