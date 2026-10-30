import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQBoundedInput
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCrossVariation

/-!
Original commitment: the actual Q integral of the SAME control must equal the P integral minus its actual time energy.
Existing result: actual Q integral is constructed from SAME bounded tables; native original Holder/cross-energy/time-marginal maps exist.
Premise reduced: identify each literal Q table output with its original P output minus the actual cross-drift, and derive cross-energy convergence.
Model/witness: actual shifted W_f, ownQ, same original permitted table and original f, real dt primitive; T=0 without division.
Consumer/boundary: limits identify the actual Q integral next; no change-of-integrator or desired Ito identity is an input field.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQCrossDrift
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralTimeTruncation BrownianIntegralTimeEnergy BrownianIntegralEnergyL1
open BrownianIntegralCrossVariation BrownianBoundedPredictableApproximation BrownianBoundedControlSource
open BrownianBoundedExponentialLimitSource BrownianOwnQOneStepIntegral BrownianOwnQSimpleIntegral
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K)
include hK

private theorem section_intervalIntegrable (ω : ℝ≥0 → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t => boundedRepresentative T f K (t,ω)) volume a b := by
  have hm : Measurable (fun t => boundedRepresentative T f K (t,ω)) :=
    ((boundedRepresentative_predictable T f K).mono predictableSigma_le).measurable.comp (measurable_id.prodMk measurable_const)
  let _ : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min a b) (max a b)))
    infer_instance
  rw [intervalIntegrable_iff]
  exact Integrable.of_bound hm.aestronglyMeasurable K (Eventually.of_forall (fun _ => boundedRepresentative_bound T f K hK _))

private theorem section_integrable (ω : ℝ≥0 → ℝ) :
    Integrable (fun t => boundedRepresentative T f K (t,ω)) (timeLaw T) := by
  exact Integrable.of_bound
    (((boundedRepresentative_predictable T f K).mono predictableSigma_le).measurable.comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable K
      (Eventually.of_forall (fun _ => boundedRepresentative_bound T f K hK _))

private theorem block_integral (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a≤b) (hbT : b≤T) (ω : ℝ≥0 → ℝ) :
    (∫ t, intervalIntegrand H a b (t,ω)*boundedRepresentative T f K (t,ω) ∂timeLaw T)=
      H ω*(drift T f K b ω-drift T f K a ω) := by
  have he : (fun t => intervalIntegrand H a b (t,ω)*boundedRepresentative T f K (t,ω))=
      (Ioc (a : ℝ) (b : ℝ)).indicator (fun t => H ω*boundedRepresentative T f K (t,ω)) := by
    funext t
    by_cases ht : t∈Ioc (a : ℝ) (b : ℝ) <;> simp [intervalIntegrand,ht]
  have hs : Ioc (a : ℝ) (b : ℝ)⊆Icc 0 (T : ℝ) := by
    intro t ht
    exact ⟨a.coe_nonneg.trans ht.1.le,ht.2.trans (by exact_mod_cast hbT)⟩
  rw [he,integral_indicator measurableSet_Ioc,timeLaw,Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr hs,integral_const_mul,← intervalIntegral.integral_of_le (show (a : ℝ)≤(b : ℝ) by exact_mod_cast hab)]
  have haT := hab.trans hbT
  rw [drift_primitive,drift_primitive,min_eq_left hbT,min_eq_left haT]
  have h := intervalIntegral.integral_add_adjacent_intervals
    (section_intervalIntegrable T f K hK ω 0 a) (section_intervalIntegrable T f K hK ω a b)
  congr 1
  linarith

/-- Literal actual time-product integral equals the actual coefficient
weighted real drift increments, for every sample, even on collapsed cells. -/
theorem literal_cross_integral (r : ElementaryInput T) (ω : ℝ≥0 → ℝ) :
    (∫ t, integrand r.clock r.coefficient (t,ω)*boundedRepresentative T f K (t,ω) ∂timeLaw T)=
      ∑ i : Fin r.n, r.coefficient i ω*(drift T f K (r.clock i.succ) ω-drift T f K (r.clock i.castSucc) ω) := by
  simp only [integrand,Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    apply block_integral T f K hK
    · exact r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
    · simpa only [r.clock_end] using r.clock_mono (Fin.le_last i.succ)
  · intro i _
    have he : (fun t => intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) (t,ω)*boundedRepresentative T f K (t,ω))=
        (Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ)).indicator (fun t => r.coefficient i ω*boundedRepresentative T f K (t,ω)) := by
      funext t
      by_cases ht : t∈Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ) <;> simp [intervalIntegrand,ht]
    rw [he]
    exact ((section_integrable T f K hK ω).const_mul _).indicator measurableSet_Ioc

include hK hbound
/-- Native original cross energy is bound to THESE literal drift increments
by actual Holder products and Fubini, not a supplied shift certificate. -/
theorem crossEnergyClass_literal (r : ElementaryInput T) : crossEnergyClass T T (literalPredictableInput r) f=ᵐ[sourceLaw]
    fun ω => ∑ i : Fin r.n, r.coefficient i ω*(drift T f K (r.clock i.succ) ω-drift T f K (r.clock i.castSucc) ω) := by
  have hp : productClass (inputLaw T) (literalPredictableInput r : Lp ℝ 2 (inputLaw T)) (f : Lp ℝ 2 (inputLaw T))=ᵐ[inputLaw T]
      fun p => integrand r.clock r.coefficient p*boundedRepresentative T f K p := by
    filter_upwards [productClass_coe (inputLaw T) (literalPredictableInput r) f,
      (BrownianTimeIntegrand.integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp,
      boundedRepresentative_ae T f K hbound] with p hp hr hf
    change (literalPredictableInput r : Lp ℝ 2 (inputLaw T)) p=integrand r.clock r.coefficient p at hr
    rw [hp,hr,hf]
  have hs : ∀ᵐ ω ∂sourceLaw, (fun t => productClass (inputLaw T) (literalPredictableInput r) f (t,ω))=ᵐ[timeLaw T]
      fun t => integrand r.clock r.coefficient (t,ω)*boundedRepresentative T f K (t,ω) :=
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := sourceLaw) (ν := timeLaw T)).quasiMeasurePreserving.ae hp)
  simp only [crossEnergyClass,truncate_horizon]
  filter_upwards [timeMarginal_coe T (productClass (inputLaw T) (literalPredictableInput r) f),hs] with ω hm hs
  exact hm.trans ((integral_congr_ae hs).trans (literal_cross_integral T f K hK r ω))

/-- Actual Q table integral = original actual P table integral minus the
native cross-drift. No old P integral is renamed a Q integral. -/
theorem literal_integral_shift (r : ElementaryInput T) :
    BrownianOwnQSimpleIntegral.simpleIntegral T f K r=ᵐ[sourceLaw]
      fun ω => outputValue r ω-crossEnergyClass T T (literalPredictableInput r) f ω := by
  filter_upwards [(BrownianSimplePredictableIntegral.simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp,
    crossEnergyClass_literal T f K hK hbound r] with ω hi hc
  change outputValue r ω=BrownianSimplePredictableIntegral.simpleIntegral r.clock r.coefficient ω at hi
  rw [hi,hc]
  simp only [BrownianOwnQSimpleIntegral.simpleIntegral,BrownianSimplePredictableIntegral.simpleIntegral,
    BrownianOwnQOneStepIntegral.oneStep,BrownianOneStepIntegral.oneStep,Pi.mul_apply,
    BrownianBoundedGirsanovSource.fullIncrement,BrownianMartingaleSource.increment,shiftedProcess,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- SAME actual table cross-drifts converge at their natural source-L1
scale to SAME f's actual time energy, using native Holder/time-marginal continuity. -/
theorem actual_crossEnergy_tendsto : Tendsto (fun n => crossEnergyClass T T
      (literalPredictableInput (approximation T f K hK hbound n)) f) atTop (𝓝 (energyClass T T f)) := by
  simp only [crossEnergyClass,truncate_horizon]
  rw [energyClass_eq_marginal_square,truncate_horizon]
  have hp := (((ContinuousLinearMap.mul ℝ ℝ).holderL (inputLaw T) 2 2 1).continuous₂.tendsto
    ((f : Lp ℝ 2 (inputLaw T)),(f : Lp ℝ 2 (inputLaw T)))).comp
      ((approximation_tendsto T f K hK hbound).prodMk_nhds tendsto_const_nhds)
  exact ((timeMarginal T).continuous.tendsto _).comp hp

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQCrossDrift
