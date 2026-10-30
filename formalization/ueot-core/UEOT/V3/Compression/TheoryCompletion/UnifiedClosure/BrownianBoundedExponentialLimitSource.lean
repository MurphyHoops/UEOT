import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedPredictableApproximation

/-!
Original commitment: the actual native full-predictable exponential must be normalized by source mathematics, never by division after selection.
Existing result: SAME bounded f yields actual SAME-K tables, native integral/actual energy convergence and native computed-density UI.
Premise reduced: derive in-measure/L1 convergence to f's OWN exponential, its integrability/mean one and actual changed probability measure.
Model/witness: true fullPredictableL2 f on SAME dt×P, explicit sufficient source-AE |f|<=K, T=0 included; no arbitrary-L2 normalization claim.
Consumer/boundary: original-Fs full limit-Q Brownian source and P-KL follow next; exact finite natural-filtration equality is NOT passed to the limit.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedExponentialLimitSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralTimeEnergy BrownianIntegralEnergyL1
open BrownianBoundedPredictableApproximation BrownianFiniteDensityL2Source BrownianFiniteStepExponentialSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual terminal exponential of SAME native returned integral and actual
SAME-input time energy. No normalization constant is inserted. -/
def fullDensity (T : ℝ≥0) (f : fullPredictableL2 T) (ω : ℝ≥0 → ℝ) : ℝ :=
  Real.exp ((predictableIntegral T f : (ℝ≥0 → ℝ) → ℝ) ω-(1/2 : ℝ)*timeEnergy T f T ω)

theorem fullDensity_pos (T : ℝ≥0) (f : fullPredictableL2 T) (ω : ℝ≥0 → ℝ) : 0<fullDensity T f ω := Real.exp_pos _
theorem fullDensity_measurable (T : ℝ≥0) (f : fullPredictableL2 T) : Measurable (fullDensity T f) :=
  (Real.continuous_exp.comp_stronglyMeasurable
    ((Lp.stronglyMeasurable (predictableIntegral T f)).sub
      (stronglyMeasurable_const.mul ((timeEnergy_stronglyAdapted T f T).mono (naturalFiltration.le T))))).measurable

/-- The native subsequence criterion gives this needed continuous binary
readout rule, without assuming unavailable in-measure composition APIs. -/
private theorem binary_inMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (U V : ℕ → Ω → ℝ) (u v : Ω → ℝ) (F : ℝ × ℝ → ℝ) (hF : Continuous F)
    (hM : ∀ n, AEStronglyMeasurable (fun ω => F (U n ω,V n ω)) P)
    (hU : TendstoInMeasure P U atTop u) (hV : TendstoInMeasure P V atTop v) :
    TendstoInMeasure P (fun n ω => F (U n ω,V n ω)) atTop (fun ω => F (u ω,v ω)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff hM).mpr
  intro ns hns
  obtain ⟨ms,hms,hUa⟩ := (hU.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ls,hls,hVa⟩ := (hV.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨ms ∘ ls,hms.comp hls,?_⟩
  filter_upwards [hUa,hVa] with ω hu hv
  exact (hF.tendsto (u ω,v ω)).comp ((hu.comp hls.tendsto_atTop).prodMk_nhds hv)

/-- These are the actual finite-table densities, and the target is f's
OWN actual native exponential, not an externally chosen limit density. -/
theorem actual_densities_tendstoInMeasure (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    TendstoInMeasure sourceLaw (fun n => terminalDensity (approximation T f K hK hbound n)) atTop (fullDensity T f) := by
  let r := approximation T f K hK hbound
  let U := fun n => (outputValue (r n) : (ℝ≥0 → ℝ) → ℝ)
  let V := fun n => (energyClass T T (literalPredictableInput (r n)) : (ℝ≥0 → ℝ) → ℝ)
  let u := (predictableIntegral T f : (ℝ≥0 → ℝ) → ℝ)
  let v := (energyClass T T f : (ℝ≥0 → ℝ) → ℝ)
  let F : ℝ × ℝ → ℝ := fun p => Real.exp (p.1-(1/2 : ℝ)*p.2)
  have hM (n : ℕ) : AEStronglyMeasurable (fun ω => F (U n ω,V n ω)) sourceLaw :=
    Real.continuous_exp.comp_aestronglyMeasurable ((Lp.aestronglyMeasurable (outputValue (r n))).sub
      (aestronglyMeasurable_const.mul (Lp.aestronglyMeasurable (energyClass T T (literalPredictableInput (r n))))))
  have h := binary_inMeasure sourceLaw U V u v F (by fun_prop) hM
    (tendstoInMeasure_of_tendsto_Lp (approximation_outputs_tendsto T f K hK hbound))
    (tendstoInMeasure_of_tendsto_Lp (approximation_energy_tendsto T f K hK hbound T))
  apply TendstoInMeasure.congr (f := fun n ω => F (U n ω,V n ω)) ?_ ?_ h
  · intro n
    have hd : terminalDensity (r n) =ᵐ[sourceLaw] fun ω =>
        Real.exp ((outputValue (r n) : (ℝ≥0 → ℝ) → ℝ) ω-(1/2 : ℝ)*timeEnergy T (literalPredictableInput (r n)) T ω) := by
      simpa only [terminalDensity,predictableIntegral_returns_literal] using table_exponential_actual_integral (r n)
    filter_upwards [hd,energyClass_coe T T (literalPredictableInput (r n))] with ω hd he
    change Real.exp (_-(1/2 : ℝ)*energyClass T T (literalPredictableInput (r n)) ω)=_
    rw [he]
    exact hd.symm
  · filter_upwards [energyClass_coe T T f] with ω he
    change Real.exp (_-(1/2 : ℝ)*energyClass T T f ω)=Real.exp (_-(1/2 : ℝ)*timeEnergy T f T ω)
    rw [he]

/-- Actual integrability is DERIVED by native UI and actual in-measure
convergence; it is not an input certificate or an assumed Novikov conclusion. -/
theorem fullDensity_integrable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) : Integrable (fullDensity T f) sourceLaw :=
  (approximation_densities_uniformIntegrable T f K hK hbound).integrable_of_tendstoInMeasure
    (actual_densities_tendstoInMeasure T f K hK hbound)

/-- Native Vitali L1 convergence of the actual returned finite-table
densities to the OWN actual full-input exponential. -/
theorem actual_densities_tendsto_L1 (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    Tendsto (fun n => eLpNorm (terminalDensity (approximation T f K hK hbound n)-fullDensity T f) 1 sourceLaw)
      atTop (𝓝 0) := by
  have hu := approximation_densities_uniformIntegrable T f K hK hbound
  exact tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by norm_num) hu.aestronglyMeasurable
    (hu.memLp_of_tendstoInMeasure (actual_densities_tendstoInMeasure T f K hK hbound)) hu.unifIntegrable
    (actual_densities_tendstoInMeasure T f K hK hbound)

/-- True mean one comes from the actual finite normalization and L1
passage. The expression is NEVER divided by a computed mean. -/
theorem fullDensity_mean_one (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    (∫ ω, fullDensity T f ω ∂sourceLaw)=1 := by
  have h := tendsto_integral_of_L1' (fullDensity T f) (fullDensity_measurable T f).aestronglyMeasurable
    (Eventually.of_forall (fun n => (prefix_integrable_mean (approximation T f K hK hbound n) _).1))
    (actual_densities_tendsto_L1 T f K hK hbound)
  have hm (n : ℕ) : (∫ ω, terminalDensity (approximation T f K hK hbound n) ω ∂sourceLaw)=1 :=
    (prefix_integrable_mean (approximation T f K hK hbound n) _).2
  have hconst : Tendsto (fun n => ∫ ω, terminalDensity (approximation T f K hK hbound n) ω ∂sourceLaw) atTop (𝓝 (1 : ℝ)) :=
    (tendsto_congr' (Eventually.of_forall hm)).mpr tendsto_const_nhds
  exact tendsto_nhds_unique h hconst

/-- SAME actual exponential change of measure; the sufficient bounded
source condition is needed for the probability theorem, not hidden in this definition. -/
def fullLaw (T : ℝ≥0) (f : fullPredictableL2 T) : Measure (ℝ≥0 → ℝ) :=
  sourceLaw.withDensity (fun ω => ENNReal.ofReal (fullDensity T f ω))

theorem fullLaw_probability (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) : IsProbabilityMeasure (fullLaw T f) where
  measure_univ := by
    rw [fullLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (fullDensity_integrable T f K hK hbound)
        (Eventually.of_forall (fun ω => (fullDensity_pos T f ω).le)),fullDensity_mean_one T f K hK hbound]
    norm_num

theorem fullLaw_absolutelyContinuous (T : ℝ≥0) (f : fullPredictableL2 T) : fullLaw T f ≪ sourceLaw :=
  withDensity_absolutelyContinuous sourceLaw _

theorem fullLaw_rnDeriv (T : ℝ≥0) (f : fullPredictableL2 T) :
    (fullLaw T f).rnDeriv sourceLaw =ᵐ[sourceLaw] fun ω => ENNReal.ofReal (fullDensity T f ω) :=
  Measure.rnDeriv_withDensity sourceLaw (fullDensity_measurable T f).ennreal_ofReal

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedExponentialLimitSource
