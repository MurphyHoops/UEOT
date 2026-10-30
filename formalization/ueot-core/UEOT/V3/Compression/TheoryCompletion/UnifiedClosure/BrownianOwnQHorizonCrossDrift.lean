import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedControlReadout
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCrossVariation

/-!
Original commitment: one fixed ownQ_A run must retain its actual control/drift when integrating at an independent read horizon U.
Existing result: actual global masked control has an original predictable input class on U and the SAME literal primitive at all times.
Premise reduced: derive actual finite W_A table shift with native cross on U and original global control readout, without changing Q or normalizing a new U control.
Model/witness: original b on A/K; original permitted r on U, collapsed/zero cells and A=0/U=0, no ordering A,U.
Consumer/boundary: actual all-read target shift/controlled C2 in one measure; no desired ItoRun, cross-horizon Lp transport or new policy is supplied.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQHorizonCrossDrift
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralTimeTruncation BrownianIntegralTimeEnergy BrownianIntegralEnergyL1 BrownianIntegralCrossVariation
open BrownianBoundedPredictableApproximation BrownianBoundedControlSource BrownianBoundedControlReadout
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (A : ℝ≥0) (b : fullPredictableL2 A) (K : ℝ) (hK : 0≤K) (U : ℝ≥0)
include hK

private theorem section_intervalIntegrable (ω : ℝ≥0 → ℝ) (a c : ℝ) :
    IntervalIntegrable (fun t => control A b K t ω) volume a c := by
  have hm : Measurable (fun t => control A b K t ω) := (control_joint A b K).comp (measurable_id.prodMk measurable_const)
  let _ : IsFiniteMeasure (volume.restrict (uIoc a c)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min a c) (max a c)))
    infer_instance
  rw [intervalIntegrable_iff]
  exact Integrable.of_bound hm.aestronglyMeasurable K (Eventually.of_forall (fun t => control_bound A b K hK t ω))

private theorem section_integrable (ω : ℝ≥0 → ℝ) : Integrable (fun t => control A b K t ω) (timeLaw U) :=
  Integrable.of_bound ((control_joint A b K).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable K
    (Eventually.of_forall (fun t => control_bound A b K hK t ω))

private theorem block_integral (H : (ℝ≥0 → ℝ) → ℝ) (a c : ℝ≥0) (hac : a≤c) (hcU : c≤U) (ω : ℝ≥0 → ℝ) :
    (∫ t, intervalIntegrand H a c (t,ω)*control A b K t ω ∂timeLaw U)=H ω*(drift A b K c ω-drift A b K a ω) := by
  have he : (fun t => intervalIntegrand H a c (t,ω)*control A b K t ω)=
      (Ioc (a : ℝ) (c : ℝ)).indicator (fun t => H ω*control A b K t ω) := by
    funext t
    by_cases ht : t∈Ioc (a : ℝ) (c : ℝ) <;> simp [intervalIntegrand,ht]
  have hs : Ioc (a : ℝ) (c : ℝ)⊆Icc 0 (U : ℝ) := by
    intro t ht
    exact ⟨a.coe_nonneg.trans ht.1.le,ht.2.trans (by exact_mod_cast hcU)⟩
  rw [he,integral_indicator measurableSet_Ioc,timeLaw,Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr hs,integral_const_mul,← intervalIntegral.integral_of_le (show (a : ℝ)≤(c : ℝ) by exact_mod_cast hac),
    ← actualControl_primitive A b K c ω,← actualControl_primitive A b K a ω]
  have h := intervalIntegral.integral_add_adjacent_intervals
    (section_intervalIntegrable A b K hK ω 0 a) (section_intervalIntegrable A b K hK ω a c)
  congr 1
  linarith

/-- Actual dt_U cross integral consumes the SAME deployed real control. -/
theorem literal_cross_integral (r : ElementaryInput U) (ω : ℝ≥0 → ℝ) :
    (∫ t, integrand r.clock r.coefficient (t,ω)*control A b K t ω ∂timeLaw U)=
      ∑ i : Fin r.n, r.coefficient i ω*(drift A b K (r.clock i.succ) ω-drift A b K (r.clock i.castSucc) ω) := by
  simp only [integrand,Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    apply block_integral A b K hK U
    · exact r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
    · simpa only [r.clock_end] using r.clock_mono (Fin.le_last i.succ)
  · intro i _
    have he : (fun t => intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) (t,ω)*control A b K t ω)=
        (Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ)).indicator (fun t => r.coefficient i ω*control A b K t ω) := by
      funext t
      by_cases ht : t∈Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ) <;> simp [intervalIntegrand,ht]
    rw [he]
    exact ((section_integrable A b K hK U ω).const_mul _).indicator measurableSet_Ioc

/-- Native cross uses the actual original control's U-class; no new U-law
or replacement primitive is substituted. -/
theorem crossEnergyClass_literal (r : ElementaryInput U) :
    crossEnergyClass U U (literalPredictableInput r) (actualControlInput A b K hK U)=ᵐ[sourceLaw]
      fun ω => ∑ i : Fin r.n, r.coefficient i ω*(drift A b K (r.clock i.succ) ω-drift A b K (r.clock i.castSucc) ω) := by
  have hp : productClass (inputLaw U) (literalPredictableInput r : Lp ℝ 2 (inputLaw U)) (actualControlInput A b K hK U : Lp ℝ 2 (inputLaw U))=ᵐ[inputLaw U]
      fun p => integrand r.clock r.coefficient p*control A b K p.1 p.2 := by
    filter_upwards [productClass_coe (inputLaw U) (literalPredictableInput r) (actualControlInput A b K hK U),
      (BrownianTimeIntegrand.integrand_memLp_two U r.clock r.coefficient r.coefficient_bounded).coeFn_toLp,
      actualControlInput_coe A b K hK U] with p hp hr hc
    change (literalPredictableInput r : Lp ℝ 2 (inputLaw U)) p=integrand r.clock r.coefficient p at hr
    change (actualControlInput A b K hK U : Lp ℝ 2 (inputLaw U)) p=control A b K p.1 p.2 at hc
    rw [hp,hr,hc]
  have hs : ∀ᵐ ω ∂sourceLaw, (fun t => productClass (inputLaw U) (literalPredictableInput r) (actualControlInput A b K hK U) (t,ω))=ᵐ[timeLaw U]
      fun t => integrand r.clock r.coefficient (t,ω)*control A b K t ω :=
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := sourceLaw) (ν := timeLaw U)).quasiMeasurePreserving.ae hp)
  simp only [crossEnergyClass,truncate_horizon]
  filter_upwards [timeMarginal_coe U (productClass (inputLaw U) (literalPredictableInput r) (actualControlInput A b K hK U)),hs] with ω hm hs
  exact hm.trans ((integral_congr_ae hs).trans (literal_cross_integral A b K hK U r ω))

/-- Literal actual W_A integral at U has the actual original P output and
actual deployed-control cross correction, independently of density horizon A. -/
theorem literal_integral_shift (r : ElementaryInput U) :
    BrownianOwnQSimpleIntegral.simpleIntegral A b K r=ᵐ[sourceLaw]
      fun ω => outputValue r ω-crossEnergyClass U U (literalPredictableInput r) (actualControlInput A b K hK U) ω := by
  filter_upwards [(BrownianSimplePredictableIntegral.simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp,
    crossEnergyClass_literal A b K hK U r] with ω hi hc
  change outputValue r ω=BrownianSimplePredictableIntegral.simpleIntegral r.clock r.coefficient ω at hi
  rw [hi,hc]
  simp only [BrownianOwnQSimpleIntegral.simpleIntegral,BrownianSimplePredictableIntegral.simpleIntegral,
    BrownianOwnQOneStepIntegral.oneStep,BrownianOneStepIntegral.oneStep,Pi.mul_apply,
    BrownianBoundedGirsanovSource.fullIncrement,BrownianMartingaleSource.increment,shiftedProcess,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Actual target tables' native cross limit, with the deployed control's
U-class fixed rather than changed with table or observation horizon. -/
theorem target_crossEnergy_tendsto (g : fullPredictableL2 U) (L : ℝ) (hL : 0≤L)
    (hG : ∀ᵐ p ∂inputLaw U, |(g : Lp ℝ 2 (inputLaw U)) p|≤L) :
    Tendsto (fun n => crossEnergyClass U U (literalPredictableInput (approximation U g L hL hG n)) (actualControlInput A b K hK U))
      atTop (𝓝 (crossEnergyClass U U g (actualControlInput A b K hK U))) := by
  simp only [crossEnergyClass,truncate_horizon]
  have hp := (((ContinuousLinearMap.mul ℝ ℝ).holderL (inputLaw U) 2 2 1).continuous₂.tendsto
    ((g : Lp ℝ 2 (inputLaw U)),(actualControlInput A b K hK U : Lp ℝ 2 (inputLaw U)))).comp
      ((approximation_tendsto U g L hL hG).prodMk_nhds tendsto_const_nhds)
  exact ((timeMarginal U).continuous.tendsto _).comp hp

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQHorizonCrossDrift
