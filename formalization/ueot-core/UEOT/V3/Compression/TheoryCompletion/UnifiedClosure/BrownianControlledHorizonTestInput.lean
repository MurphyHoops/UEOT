import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQHorizonTargetShift
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledTestInput

/-!
Original commitment: one original ItoRun needs actual test-noise means at every read horizon under ONE controlled law.
Existing result: original testInput g=σφ'(X), fixed ownQ_A target integrals on U, and actual same-global-control cross shift/integrability.
Premise reduced: derive actual test integral mean = dtU expectation of the SAME control drift under fixed Q_A, independently of A,U.
Model/witness: same original state x0+σB, original Fs b on A/K and target on U; bounded derivative and both zero boundaries, no new policy/measure.
Consumer/boundary: all-read controlled C2 expectation/AC/discounted occupation; no desired generator/Dynkin/ItoRun/infinite-reward field supplied.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledHorizonTestInput
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralTimeEnergy BrownianIntegralCrossVariation
open BrownianBoundedControlSource BrownianBoundedControlReadout BrownianBoundedExponentialLimitSource
open BrownianOwnQBoundedInput BrownianOwnQHorizonTargetShift BrownianControlledTestInput
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (A : ℝ≥0) (b : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw A, |(b : Lp ℝ 2 (inputLaw A)) p|≤K) (U : ℝ≥0)
    (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C : ℝ) (hC : 0≤C) (hb : ∀ x, ‖deriv φ x‖≤C)
include hK hB hφ hb

theorem firstDrift_integrable_at : Integrable (fun p : ℝ × (ℝ≥0 → ℝ) => firstDrift A b K x₀ σ φ p.1 p.2)
    (BrownianOwnQTimeInput.inputLawQ A b U) := by
  let _ := fullLaw_probability A b K hK hB
  have : IsFiniteMeasure (BrownianOwnQTimeInput.inputLawQ A b U) := by unfold BrownianOwnQTimeInput.inputLawQ; infer_instance
  apply Integrable.of_bound
    ((measurable_const.mul (control_joint A b K)).mul ((hφ.continuous_deriv (by norm_num : (1 : WithTop ℕ∞)≤2)).measurable.comp (state_joint x₀ σ))).aestronglyMeasurable
    (|σ| * K * C)
  exact Eventually.of_forall (fun p => by
    change ‖σ*control A b K p.1 p.2*deriv φ (BrownianBoundedC2DynkinSource.state x₀ σ p.1 p.2)‖≤_
    rw [norm_mul,norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (control_bound A b K hK _ _) (norm_nonneg σ)) (hb _) (norm_nonneg _) (by positivity))

include hC
/-- All read horizons use SAME Q_A. The target's noise input and actual
real control drift are linked by original source classes and Q-AC/Fubini. -/
theorem test_integral_mean_at :
    (∫ ω, (predictableIntegral U (testInput U x₀ σ φ hφ C hC hb) : (ℝ≥0 → ℝ) → ℝ) ω ∂fullLaw A b)=
      ∫ t, ∫ ω, firstDrift A b K x₀ σ φ t ω ∂fullLaw A b ∂timeLaw U := by
  let _ := fullLaw_probability A b K hK hB
  let g := testInput U x₀ σ φ hφ C hC hb
  let c := actualControlInput A b K hK U
  have hG := testInput_bound U x₀ σ φ hφ C hC hb
  have hL : 0≤C*|σ| := mul_nonneg hC (abs_nonneg _)
  rw [target_baseline_mean_eq_cross A b K hK hB U g (C*|σ|) hL hG]
  have heP : crossEnergyIntegrand U U g c=ᵐ[inputLaw U]
      fun p => firstDrift A b K x₀ σ φ p.1 p.2 := by
    filter_upwards [time_support_ae U,representative_ae U g,representative_ae U c,
      testInput_coe U x₀ σ φ hφ C hC hb,actualControlInput_coe A b K hK U] with p ht hrg hrc hg hc
    have hp : p∈timeSet U U := by simpa only [timeSet,min_self,Set.mem_prod,Set.mem_univ,and_true] using ht
    change (c : Lp ℝ 2 (inputLaw U)) p=control A b K p.1 p.2 at hc
    rw [crossEnergyIntegrand,Set.indicator_of_mem hp,← hrg,← hrc,hg,hc]
    unfold firstDrift
    ring
  have hs : ∀ᵐ ω ∂sourceLaw, (fun t => crossEnergyIntegrand U U g c (t,ω))=ᵐ[timeLaw U]
      fun t => firstDrift A b K x₀ σ φ t ω :=
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := sourceLaw) (ν := timeLaw U)).quasiMeasurePreserving.ae heP)
  have hsQ : crossTimeEnergy U g c U=ᵐ[fullLaw A b] fun ω => ∫ t, firstDrift A b K x₀ σ φ t ω ∂timeLaw U :=
    (fullLaw_absolutelyContinuous A b).ae_le (hs.mono (fun _ h => integral_congr_ae h))
  rw [integral_congr_ae hsQ]
  exact (integral_prod_symm _ (firstDrift_integrable_at A b K hK hB U x₀ σ φ hφ C hb)).symm.trans
    (integral_prod _ (firstDrift_integrable_at A b K hK hB U x₀ σ φ hφ C hb))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledHorizonTestInput
