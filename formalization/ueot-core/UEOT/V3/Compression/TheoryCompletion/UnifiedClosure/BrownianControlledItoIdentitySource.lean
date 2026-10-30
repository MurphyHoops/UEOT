import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledReadTimeSource

/-!
Original commitment: actual controlled Ito must return its genuinely constructed Q stochastic integral, not merely the old P term's expectation.
Existing result: native ownQ target integral is constructed by literal W sums/isometry/closure, and actual QI=PI−cross is proved at every independent read horizon.
Premise reduced: derive the actual C2 path identity with THAT SAME Q integral and actual state/action generator time integral.
Model/witness: fixed bounded original predictable b on deployment A, SAME Q_A/W/original Fs, X=x0+σB and C2 tests with bounded first/second derivatives, all U including U>A/zero.
Consumer/boundary: actual scalar controlled Ito stochastic-term source, preparing true Q conditional martingale; no general vector/filtered/state-dependent diffusion or unbounded-control claim.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledItoIdentitySource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralTimeEnergy BrownianIntegralCrossVariation BrownianIntegralWeightedQV BrownianScalarItoSource
open BrownianBoundedControlSource BrownianBoundedControlReadout BrownianBoundedExponentialLimitSource BrownianBoundedC2DynkinSource
open BrownianOwnQTimeInput BrownianOwnQBoundedInput BrownianOwnQHorizonTargetIntegral BrownianOwnQHorizonTargetShift
open BrownianControlledTestInput BrownianControlledC2Source BrownianControlledHorizonTestInput BrownianControlledReadTimeSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (A : ℝ≥0) (b : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw A, |(b : Lp ℝ 2 (inputLaw A)) p|≤K) (U : ℝ≥0)
    (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C₁ C₂ : ℝ) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (hb₁ : ∀ x, ‖deriv φ x‖≤C₁) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖≤C₂)

/-- The genuinely constructed ownQ integral of the SAME source test input. -/
def testNoise : Lp ℝ 2 (fullLaw A b) :=
  targetIntegralQ A b K hK hB U (testInput U x₀ σ φ hφ C₁ hC₁ hb₁)
    (C₁*|σ|) (mul_nonneg hC₁ (abs_nonneg _)) (testInput_bound U x₀ σ φ hφ C₁ hC₁ hb₁)

/-- Mean zero is inherited from the constructed Q isometry and original
finite-table martingale source, not postulated as the Ito remainder's law. -/
theorem testNoise_mean_zero : (∫ ω, testNoise A b K hK hB U x₀ σ φ hφ C₁ hC₁ hb₁ ω ∂fullLaw A b)=0 :=
  targetIntegralQ_mean_zero A b K hK hB U (testInput U x₀ σ φ hφ C₁ hC₁ hb₁)
    (C₁*|σ|) (mul_nonneg hC₁ (abs_nonneg _)) (testInput_bound U x₀ σ φ hφ C₁ hC₁ hb₁)

include hK hφ hC₁ hb₁
/-- Path-level real drift readout, stronger than an equality only after expectation. -/
theorem test_cross_eq_firstDrift :
    crossTimeEnergy U (testInput U x₀ σ φ hφ C₁ hC₁ hb₁) (actualControlInput A b K hK U) U=ᵐ[fullLaw A b]
      fun ω => ∫ t, firstDrift A b K x₀ σ φ t ω ∂timeLaw U := by
  let g := testInput U x₀ σ φ hφ C₁ hC₁ hb₁
  let c := actualControlInput A b K hK U
  have he : crossEnergyIntegrand U U g c=ᵐ[inputLaw U] fun p => firstDrift A b K x₀ σ φ p.1 p.2 := by
    filter_upwards [time_support_ae U,representative_ae U g,representative_ae U c,
      testInput_coe U x₀ σ φ hφ C₁ hC₁ hb₁,actualControlInput_coe A b K hK U] with p ht hrg hrc hg hc
    have hp : p∈timeSet U U := by simpa only [timeSet,min_self,Set.mem_prod,Set.mem_univ,and_true] using ht
    change (c : Lp ℝ 2 (inputLaw U)) p=control A b K p.1 p.2 at hc
    rw [crossEnergyIntegrand,Set.indicator_of_mem hp,← hrg,← hrc,hg,hc]
    unfold firstDrift
    ring
  have hs : ∀ᵐ ω ∂sourceLaw, (fun t => crossEnergyIntegrand U U g c (t,ω))=ᵐ[timeLaw U]
      fun t => firstDrift A b K x₀ σ φ t ω :=
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := sourceLaw) (ν := timeLaw U)).quasiMeasurePreserving.ae he)
  exact (fullLaw_absolutelyContinuous A b).ae_le (hs.mono (fun _ h => integral_congr_ae h))

omit hK hφ hC₁ hb₁ in
/-- SAME actual second-order time integral, with no assumed energy identity. -/
theorem secondEnergy_eq_raw : itoSecondEnergy U (constantInput U σ) (shiftedTest x₀ φ)=ᵐ[fullLaw A b]
    fun ω => ∫ t, secondRaw x₀ σ φ (t,ω) ∂timeLaw U := by
  have he := constantInput_second_integrand U x₀ σ φ
  have hs : ∀ᵐ ω ∂sourceLaw,
      (fun t => weightedTimeIntegrand U (fun u ω => iteratedDeriv 2 (shiftedTest x₀ φ)
        (BrownianIntegralContinuousVersion.continuousIntegralProcess U (constantInput U σ) u ω)) (constantInput U σ) (t,ω))=ᵐ[timeLaw U]
        fun t => secondRaw x₀ σ φ (t,ω) :=
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := sourceLaw) (ν := timeLaw U)).quasiMeasurePreserving.ae he)
  exact (fullLaw_absolutelyContinuous A b).ae_le (hs.mono (fun _ h => integral_congr_ae h))

include hB hC₂ hb₂
/-- Actual pathwise controlled Ito, with the stochastic term returned by the
independently constructed own-Q integrator on its actual source test input.
Each U equality is Q-AE; no uncountable AE intersection is taken. -/
theorem actual_ownQ_ito_at : (fun ω => φ (state x₀ σ U ω))=ᵐ[fullLaw A b] fun ω => φ x₀+
    testNoise A b K hK hB U x₀ σ φ hφ C₁ hC₁ hb₁ ω+
      ∫ t, controlledGenerator σ φ (state x₀ σ t ω) (control A b K t ω) ∂timeLaw U := by
  let _ := fullLaw_probability A b K hK hB
  let g := testInput U x₀ σ φ hφ C₁ hC₁ hb₁
  have hq := targetIntegralQ_eq_actual A b K hK hB U g (C₁*|σ|)
    (mul_nonneg hC₁ (abs_nonneg _)) (testInput_bound U x₀ σ φ hφ C₁ hC₁ hb₁)
  have hiF := (firstDrift_integrable_at A b K hK hB U x₀ σ φ hφ C₁ hb₁).prod_left_ae
  have hiS := (secondRaw_integrable_at A b K hK hB U x₀ σ φ hφ C₂ hb₂).prod_left_ae
  filter_upwards [actual_ito_identity_at A b U x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂,hq,
    test_cross_eq_firstDrift A b K hK U x₀ σ φ hφ C₁ hC₁ hb₁,
    secondEnergy_eq_raw A b U x₀ σ φ,hiF,hiS] with ω hi hq hf hs hiF hiS
  have hg : (∫ t, controlledGenerator σ φ (state x₀ σ t ω) (control A b K t ω) ∂timeLaw U)=
      (∫ t, firstDrift A b K x₀ σ φ t ω ∂timeLaw U)+(1/2 : ℝ)*(∫ t, secondRaw x₀ σ φ (t,ω) ∂timeLaw U) := by
    rw [← integral_const_mul,← integral_add hiF (hiS.const_mul (1/2 : ℝ))]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by unfold controlledGenerator firstDrift secondRaw; ring)
  change testNoise A b K hK hB U x₀ σ φ hφ C₁ hC₁ hb₁ ω=
    (predictableIntegral U g : (ℝ≥0 → ℝ) → ℝ) ω-crossTimeEnergy U g (actualControlInput A b K hK U) U ω at hq
  rw [hf] at hq
  rw [hs] at hi
  rw [hg]
  dsimp only [g] at hq
  linarith

/-- The actual analytic Ito remainder equals the SAME returned Q integral. -/
theorem actual_ito_remainder :
    (fun ω => φ (state x₀ σ U ω)-φ x₀-
      ∫ t, controlledGenerator σ φ (state x₀ σ t ω) (control A b K t ω) ∂timeLaw U)=ᵐ[fullLaw A b]
        testNoise A b K hK hB U x₀ σ φ hφ C₁ hC₁ hb₁ := by
  filter_upwards [actual_ownQ_ito_at A b K hK hB U x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂] with ω h
  linarith

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledItoIdentitySource
