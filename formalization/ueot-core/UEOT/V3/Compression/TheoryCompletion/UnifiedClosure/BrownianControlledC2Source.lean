import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledTestInput

/-!
Original commitment: original ItoRun's generator expectation must be derived from the actual controlled state and action experiment.
Existing result: actual scalar Ito, same-state original testInput, true ownQ target integration and actual control-drift expectation.
Premise reduced: derive actual controlled bounded-C2 expectation with generator σaφ' + σ²φ''/2; no desired Ito expectation is supplied.
Model/witness: X=x0+σ originalB under SAME ownQ_b, actual shifted Brownian W_b and real progressive control b/K, bounded first/second derivatives, T=0 included.
Consumer/boundary: original finite-horizon ItoRun occupation/terminal source next; all-horizon reward/control-family, vector and arbitrary-filter obligations remain.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledC2Source
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralWeightedQV BrownianIntegralContinuousVersion BrownianScalarItoSource BrownianIntegralTimeEnergy
open BrownianBoundedControlSource BrownianBoundedExponentialLimitSource BrownianBoundedC2DynkinSource
open BrownianOwnQBoundedInput BrownianOwnQTargetIntegral BrownianOwnQTargetShift BrownianControlledTestInput
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def controlledGenerator (σ : ℝ) (φ : ℝ → ℝ) (x a : ℝ) : ℝ :=
  σ*a*deriv φ x+(σ^2/2)*iteratedDeriv 2 φ x

def secondRaw (x₀ σ : ℝ) (φ : ℝ → ℝ) (p : ℝ × (ℝ≥0 → ℝ)) : ℝ :=
  σ^2*iteratedDeriv 2 φ (state x₀ σ p.1 p.2)

/-- Actual controlled state uses the SAME shifted noise and real primitive,
pointwise at every nonnegative clock; this is a derived source identity. -/
theorem state_controlled_primitive (T : ℝ≥0) (b : fullPredictableL2 T) (K x₀ σ : ℝ) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    state x₀ σ t ω=x₀+σ*shiftedProcess T b K t ω+
      σ*(∫ u in (0 : ℝ)..(min t T : ℝ≥0), BrownianBoundedPredictableApproximation.boundedRepresentative T b K (u,ω)) := by
  rw [← drift_primitive]
  simp only [state,Real.toNNReal_coe,shiftedProcess]
  ring

theorem state_initial (T : ℝ≥0) (b : fullPredictableL2 T) (x₀ σ : ℝ) :
    state x₀ σ 0=ᵐ[fullLaw T b] fun _ => x₀ := by
  filter_upwards [(fullLaw_absolutelyContinuous T b).ae_le process_zero] with ω hz
  simp only [state,Real.toNNReal_zero,hz,mul_zero,add_zero]

variable (T : ℝ≥0) (b : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw T, |(b : Lp ℝ 2 (inputLaw T)) p|≤K)
    (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C₁ C₂ : ℝ) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (hb₁ : ∀ x, ‖deriv φ x‖≤C₁) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖≤C₂)
include hK hB hφ hb₂

theorem secondRaw_integrable : Integrable (secondRaw x₀ σ φ) (BrownianOwnQTimeInput.inputLawQ T b T) := by
  let _ := fullLaw_probability T b K hK hB
  have : IsFiniteMeasure (BrownianOwnQTimeInput.inputLawQ T b T) := by unfold BrownianOwnQTimeInput.inputLawQ; infer_instance
  apply Integrable.of_bound
    (measurable_const.mul ((hφ.continuous_iteratedDeriv' 2).measurable.comp (state_joint x₀ σ))).aestronglyMeasurable (σ^2*C₂)
  exact Eventually.of_forall (fun p => by
    change ‖σ^2*iteratedDeriv 2 φ (state x₀ σ p.1 p.2)‖≤_
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg σ)]
    exact mul_le_mul_of_nonneg_left (hb₂ _) (sq_nonneg σ))

theorem secondEnergy_integrable : Integrable (itoSecondEnergy T (constantInput T σ) (shiftedTest x₀ φ)) (fullLaw T b) := by
  let _ := fullLaw_probability T b K hK hB
  have he : weightedTimeIntegrand T (fun u ω => iteratedDeriv 2 (shiftedTest x₀ φ)
      (continuousIntegralProcess T (constantInput T σ) u ω)) (constantInput T σ)=ᵐ[BrownianOwnQTimeInput.inputLawQ T b T]
      secondRaw x₀ σ φ :=
    (inputLawQ_absolutelyContinuous T b T).ae_le (constantInput_second_integrand T x₀ σ φ)
  have hi := (secondRaw_integrable T b K hK hB x₀ σ φ hφ C₂ hb₂).congr he.symm
  exact hi.integral_prod_right

theorem secondEnergy_mean : (∫ ω, itoSecondEnergy T (constantInput T σ) (shiftedTest x₀ φ) ω ∂fullLaw T b)=
    ∫ t, ∫ ω, secondRaw x₀ σ φ (t,ω) ∂fullLaw T b ∂timeLaw T := by
  let _ := fullLaw_probability T b K hK hB
  have he : weightedTimeIntegrand T (fun u ω => iteratedDeriv 2 (shiftedTest x₀ φ)
      (continuousIntegralProcess T (constantInput T σ) u ω)) (constantInput T σ)=ᵐ[BrownianOwnQTimeInput.inputLawQ T b T]
      secondRaw x₀ σ φ :=
    (inputLawQ_absolutelyContinuous T b T).ae_le (constantInput_second_integrand T x₀ σ φ)
  have hi := (secondRaw_integrable T b K hK hB x₀ σ φ hφ C₂ hb₂).congr he.symm
  unfold itoSecondEnergy weightedTimeEnergy
  exact (integral_prod_symm _ hi).symm.trans ((integral_congr_ae he).trans
    (integral_prod _ (secondRaw_integrable T b K hK hB x₀ σ φ hφ C₂ hb₂)))

include hC₁ hC₂ hb₁
omit hK hB in
/-- Actual Ito path identity is inherited by Q absolute continuity and is
bound to the original returned test input, rather than a new noise field. -/
theorem actual_ito_identity : (fun ω => φ (state x₀ σ T ω))=ᵐ[fullLaw T b] fun ω => φ x₀+
    (predictableIntegral T (testInput T x₀ σ φ hφ C₁ hC₁ hb₁) : (ℝ≥0 → ℝ) → ℝ) ω+
      (1/2 : ℝ)*itoSecondEnergy T (constantInput T σ) (shiftedTest x₀ φ) ω := by
  have hψ : ContDiff ℝ 2 (shiftedTest x₀ φ) := hφ.comp (contDiff_const.add contDiff_id)
  have hbψ₁ : ∀ x, ‖deriv (shiftedTest x₀ φ) x‖≤C₁ := by
    intro x
    rw [show deriv (shiftedTest x₀ φ) x=deriv φ (x₀+x) from shift_deriv φ x₀ x]
    exact hb₁ _
  have hbψ₂ : ∀ x, ‖iteratedDeriv 2 (shiftedTest x₀ φ) x‖≤C₂ := by
    intro x
    rw [show iteratedDeriv 2 (shiftedTest x₀ φ) x=iteratedDeriv 2 φ (x₀+x) from shift_second φ x₀ x]
    exact hb₂ _
  have hito := actual_scalar_ito T (constantInput T σ) (shiftedTest x₀ φ) hψ C₁ C₂ hC₁ hC₂ hbψ₁ hbψ₂
  apply (fullLaw_absolutelyContinuous T b).ae_le
  filter_upwards [hito,constantInput_process T σ,continuousIntegralProcess_horizon T (testInput T x₀ σ φ hφ C₁ hC₁ hb₁)] with ω hi hp hg
  change shiftedTest x₀ φ (continuousIntegralProcess T (constantInput T σ) T ω)=
    shiftedTest x₀ φ 0+continuousIntegralProcess T (testInput T x₀ σ φ hφ C₁ hC₁ hb₁) T ω+
      (1/2 : ℝ)*itoSecondEnergy T (constantInput T σ) (shiftedTest x₀ φ) ω at hi
  rw [hp T le_rfl,hg] at hi
  simpa only [shiftedTest,state,Real.toNNReal_coe,add_zero] using hi

/-- Genuine expectation of the controlled diffusion source, with actual
generator and action readouts. It is not supplied as an ItoRun field. -/
theorem actual_controlled_expectation : (∫ ω, φ (state x₀ σ T ω) ∂fullLaw T b)=φ x₀+
    ∫ t, ∫ ω, controlledGenerator σ φ (state x₀ σ t ω) (control T b K t ω) ∂fullLaw T b ∂timeLaw T := by
  let _ := fullLaw_probability T b K hK hB
  let g := testInput T x₀ σ φ hφ C₁ hC₁ hb₁
  have hI := target_baseline_integrable T b K hK hB g (C₁*|σ|) (mul_nonneg hC₁ (abs_nonneg _))
    (testInput_bound T x₀ σ φ hφ C₁ hC₁ hb₁)
  have hA := secondEnergy_integrable T b K hK hB x₀ σ φ hφ C₂ hb₂
  dsimp only [g] at hI
  rw [integral_congr_ae (actual_ito_identity T b x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂),
    integral_add (f := fun ω => φ x₀+(predictableIntegral T (testInput T x₀ σ φ hφ C₁ hC₁ hb₁) : (ℝ≥0 → ℝ) → ℝ) ω)
      (g := fun ω => (1/2 : ℝ)*itoSecondEnergy T (constantInput T σ) (shiftedTest x₀ φ) ω)
      ((integrable_const _).add hI) (hA.const_mul _),
    integral_add (f := fun _ => φ x₀) (integrable_const _) hI,
    integral_const,probReal_univ,one_smul,integral_const_mul,
    test_integral_mean_eq_control_drift T b K hK hB x₀ σ φ hφ C₁ hC₁ hb₁,
    secondEnergy_mean T b K hK hB x₀ σ φ hφ C₂ hb₂]
  have hiFirst := firstDrift_integrable T b K hK hB x₀ σ φ hφ C₁ hb₁
  have hiSecond := secondRaw_integrable T b K hK hB x₀ σ φ hφ C₂ hb₂
  rw [add_assoc,← integral_const_mul,← integral_add hiFirst.integral_prod_left (hiSecond.integral_prod_left.const_mul (1/2 : ℝ))]
  apply congrArg (fun z : ℝ => φ x₀+z)
  apply integral_congr_ae
  filter_upwards [hiFirst.prod_right_ae,hiSecond.prod_right_ae] with t ht₁ ht₂
  rw [← integral_const_mul,← integral_add ht₁ (ht₂.const_mul (1/2 : ℝ))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω => by unfold controlledGenerator firstDrift secondRaw; ring)

/-- Terminal test integrability is derived from actual Ito and the actual
Q-integrability of its constructed noise and correction terms. -/
theorem state_test_integrable : Integrable (fun ω => φ (state x₀ σ T ω)) (fullLaw T b) := by
  let _ := fullLaw_probability T b K hK hB
  have hI := target_baseline_integrable T b K hK hB (testInput T x₀ σ φ hφ C₁ hC₁ hb₁)
    (C₁*|σ|) (mul_nonneg hC₁ (abs_nonneg _)) (testInput_bound T x₀ σ φ hφ C₁ hC₁ hb₁)
  exact (((integrable_const (φ x₀)).add hI).add
    ((secondEnergy_integrable T b K hK hB x₀ σ φ hφ C₂ hb₂).const_mul (1/2 : ℝ))).congr
      (actual_ito_identity T b x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂).symm

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledC2Source
