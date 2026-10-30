import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTargetShift
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedC2DynkinSource

/-!
Original commitment: actual controlled ItoRun must derive the test's noise input and generator drift from the SAME state/control source.
Existing result: original scalar Ito and constant-input source; fixed ownQ_b integrates bounded target g with actual cross-drift expectation.
Premise reduced: construct g=σφ'(x0+σB), prove its original predictable bound, and identify its actual Q mean with actual control drift.
Model/witness: actual state x0+σ originalB under b's OWN Q, bounded original-predictable b/K, bounded C2 first derivative; σ may be nonzero.
Consumer/boundary: actual controlled C2 expectation/occupation next; no desired Ito/SDE identity, all-horizon family or vector source is assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledTestInput
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralTimeEnergy BrownianIntegralCrossVariation BrownianPredictableMultiplier BrownianScalarItoSource BrownianIntegralContinuousVersion
open BrownianBoundedPredictableApproximation BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianBoundedC2DynkinSource BrownianOwnQBoundedInput BrownianOwnQTargetIntegral BrownianOwnQTargetShift
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def shiftedTest (x₀ : ℝ) (φ : ℝ → ℝ) (y : ℝ) : ℝ := φ (x₀+y)
private theorem shiftedTest_contDiff (x₀ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 2 (shiftedTest x₀ φ) :=
  hφ.comp (contDiff_const.add contDiff_id)
private theorem shiftedTest_deriv_bound (x₀ : ℝ) (φ : ℝ → ℝ) (C : ℝ) (hb : ∀ x, ‖deriv φ x‖≤C) :
    ∀ x, ‖deriv (shiftedTest x₀ φ) x‖≤C := by
  intro x
  rw [show deriv (shiftedTest x₀ φ) x=deriv φ (x₀+x) from shift_deriv φ x₀ x]
  exact hb _

/-- The original returned Ito input, not a newly chosen g certificate. -/
def testInput (T : ℝ≥0) (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C : ℝ) (hC : 0≤C) (hb : ∀ x, ‖deriv φ x‖≤C) : fullPredictableL2 T :=
  itoInput T (constantInput T σ) (shiftedTest x₀ φ) (shiftedTest_contDiff x₀ φ hφ) C hC (shiftedTest_deriv_bound x₀ φ C hb)

theorem state_joint (x₀ σ : ℝ) : Measurable (fun p : ℝ × (ℝ≥0 → ℝ) => state x₀ σ p.1 p.2) :=
  measurable_const.add (measurable_const.mul (measurable_joint_process.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)))

/-- Actual same-state/readout identity for this original predictable input. -/
theorem testInput_coe (T : ℝ≥0) (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C : ℝ) (hC : 0≤C) (hb : ∀ x, ‖deriv φ x‖≤C) :
    (testInput T x₀ σ φ hφ C hC hb : Lp ℝ 2 (inputLaw T))=ᵐ[inputLaw T]
      fun p => deriv φ (state x₀ σ p.1 p.2)*σ := by
  have hp : ∀ᵐ p ∂inputLaw T, ∀ u : ℝ≥0, u≤T → continuousIntegralProcess T (constantInput T σ) u p.2=σ*process u p.2 :=
    Measure.quasiMeasurePreserving_snd.ae (constantInput_process T σ)
  have hψ := shiftedTest_contDiff x₀ φ hφ
  have hi := functionOfIntegralInput_coe T (constantInput T σ) (deriv (shiftedTest x₀ φ))
    (hψ.continuous_deriv (by norm_num : (1 : WithTop ℕ∞)≤2)) C hC (shiftedTest_deriv_bound x₀ φ C hb)
  filter_upwards [hi,hp,time_support_ae T,constantInput_coe T σ] with p hi hp ht hc
  change (testInput T x₀ σ φ hφ C hC hb : Lp ℝ 2 (inputLaw T)) p=_ at hi
  rw [hi,hc,hp _ ((Real.toNNReal_le_iff_le_coe).mpr ht.2)]
  rw [show deriv (shiftedTest x₀ φ) (σ*process (Real.toNNReal p.1) p.2)=
    deriv φ (x₀+σ*process (Real.toNNReal p.1) p.2) from shift_deriv φ x₀ _]
  rfl

theorem testInput_bound (T : ℝ≥0) (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C : ℝ) (hC : 0≤C) (hb : ∀ x, ‖deriv φ x‖≤C) :
    ∀ᵐ p ∂inputLaw T, |(testInput T x₀ σ φ hφ C hC hb : Lp ℝ 2 (inputLaw T)) p|≤C*|σ| := by
  filter_upwards [testInput_coe T x₀ σ φ hφ C hC hb] with p hp
  rw [hp,← Real.norm_eq_abs,norm_mul]
  exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg σ)

variable (T : ℝ≥0) (b : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw T, |(b : Lp ℝ 2 (inputLaw T)) p|≤K)
    (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C : ℝ) (hC : 0≤C) (hb : ∀ x, ‖deriv φ x‖≤C)

/-- Actual first-order control drift readout in the generator. -/
def firstDrift (t : ℝ) (ω : ℝ≥0 → ℝ) : ℝ :=
  σ*control T b K t ω*deriv φ (state x₀ σ t ω)

include hK hB hφ hC hb

omit hC in
theorem firstDrift_integrable : Integrable (fun p : ℝ × (ℝ≥0 → ℝ) => firstDrift T b K x₀ σ φ p.1 p.2) (BrownianOwnQTimeInput.inputLawQ T b T) := by
  let _ := fullLaw_probability T b K hK hB
  have : IsFiniteMeasure (BrownianOwnQTimeInput.inputLawQ T b T) := by unfold BrownianOwnQTimeInput.inputLawQ; infer_instance
  apply Integrable.of_bound
    ((measurable_const.mul (control_joint T b K)).mul ((hφ.continuous_deriv (by norm_num : (1 : WithTop ℕ∞)≤2)).measurable.comp (state_joint x₀ σ))).aestronglyMeasurable
    (|σ| * K * C)
  exact Eventually.of_forall (fun p => by
    change ‖σ*control T b K p.1 p.2*deriv φ (state x₀ σ p.1 p.2)‖≤_
    rw [norm_mul,norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (control_bound T b K hK _ _) (norm_nonneg σ)) (hb _) (norm_nonneg _) (by positivity))

/-- Actual Q expectation of the original Ito test integral is the true
control-drift term, from constructed Q integration and native Fubini. -/
theorem test_integral_mean_eq_control_drift :
    (∫ ω, (predictableIntegral T (testInput T x₀ σ φ hφ C hC hb) : (ℝ≥0 → ℝ) → ℝ) ω ∂fullLaw T b)=
      ∫ t, ∫ ω, firstDrift T b K x₀ σ φ t ω ∂fullLaw T b ∂timeLaw T := by
  let _ := fullLaw_probability T b K hK hB
  let g := testInput T x₀ σ φ hφ C hC hb
  have hG := testInput_bound T x₀ σ φ hφ C hC hb
  have hL : 0≤C*|σ| := mul_nonneg hC (abs_nonneg _)
  rw [target_baseline_mean_eq_cross T b K hK hB g (C*|σ|) hL hG]
  have heP : crossEnergyIntegrand T T g b=ᵐ[inputLaw T]
      fun p => firstDrift T b K x₀ σ φ p.1 p.2 := by
    filter_upwards [time_support_ae T,representative_ae T g,representative_ae T b,
      testInput_coe T x₀ σ φ hφ C hC hb,control_input_ae T b K hB] with p ht hrg hrb hg hc
    have hp : p∈timeSet T T := by simpa only [timeSet,min_self,Set.mem_prod,Set.mem_univ,and_true] using ht
    rw [crossEnergyIntegrand,Set.indicator_of_mem hp,← hrg,← hrb,hg,← hc]
    unfold firstDrift
    ring
  have hs : ∀ᵐ ω ∂sourceLaw, (fun t => crossEnergyIntegrand T T g b (t,ω))=ᵐ[timeLaw T]
      fun t => firstDrift T b K x₀ σ φ t ω :=
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := sourceLaw) (ν := timeLaw T)).quasiMeasurePreserving.ae heP)
  have hsQ : crossTimeEnergy T g b T=ᵐ[fullLaw T b] fun ω => ∫ t, firstDrift T b K x₀ σ φ t ω ∂timeLaw T :=
    (fullLaw_absolutelyContinuous T b).ae_le (hs.mono (fun _ h => integral_congr_ae h))
  rw [integral_congr_ae hsQ]
  exact (integral_prod_symm _ (firstDrift_integrable T b K hK hB x₀ σ φ hφ C hb)).symm.trans
    (integral_prod _ (firstDrift_integrable T b K hK hB x₀ σ φ hφ C hb))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledTestInput
