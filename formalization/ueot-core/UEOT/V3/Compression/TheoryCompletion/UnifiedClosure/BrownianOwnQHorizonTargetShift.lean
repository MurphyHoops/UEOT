import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQHorizonCrossDrift

/-!
Original commitment: one fixed ownQ_A experiment must supply actual target integrals/drift expectations at EVERY independent read horizon U.
Existing result: actual U-target Q integrals and same-global-control literal cross-shifts on U, with source b/A/Q unchanged.
Premise reduced: identify constructed targetQ(g_U) with nativeP I_U(g) minus actual U cross of SAME globalcontrol, derive actual Q integrability/mean shift.
Model/witness: fixed b,K on A and bounded original predictable g,L on U; original Fs throughout, no ordering of A,U and both zero boundaries.
Consumer/boundary: same-Q all-read controlled C2/discounted occupation source; no new normalized U law, Lp horizon transport or desired ItoRun field.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQHorizonTargetShift
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianTimeIntegrand BrownianIntegralClosure BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralTimeEnergy BrownianIntegralEnergyL1 BrownianIntegralCrossVariation
open BrownianBoundedPredictableApproximation BrownianBoundedControlSource BrownianBoundedControlReadout BrownianBoundedExponentialLimitSource
open BrownianOwnQTimeInput BrownianOwnQBoundedInput BrownianOwnQHorizonTargetIntegral BrownianOwnQHorizonCrossDrift
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
private theorem sub_inMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (U V : ℕ → Ω → ℝ) (u v : Ω → ℝ)
    (hM : ∀ n, AEStronglyMeasurable (fun ω => U n ω-V n ω) P)
    (hU : TendstoInMeasure P U atTop u) (hV : TendstoInMeasure P V atTop v) :
    TendstoInMeasure P (fun n ω => U n ω-V n ω) atTop (fun ω => u ω-v ω) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff hM).mpr
  intro ns hns
  obtain ⟨ms,hms,hUa⟩ := (hU.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ls,hls,hVa⟩ := (hV.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨ms ∘ ls,hms.comp hls,?_⟩
  filter_upwards [hUa,hVa] with ω hu hv
  exact (hu.comp hls.tendsto_atTop).sub hv

variable (A : ℝ≥0) (b : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw A, |(b : Lp ℝ 2 (inputLaw A)) p|≤K)
    (U : ℝ≥0) (g : fullPredictableL2 U) (L : ℝ) (hL : 0≤L)
    (hG : ∀ᵐ p ∂inputLaw U, |(g : Lp ℝ 2 (inputLaw U)) p|≤L)
include hK hB

private theorem ownQ_inMeasure_of_source (X : ℕ → (ℝ≥0 → ℝ) → ℝ) (x : (ℝ≥0 → ℝ) → ℝ)
    (hM : ∀ n, AEStronglyMeasurable (X n) (fullLaw A b)) (hX : TendstoInMeasure sourceLaw X atTop x) :
    TendstoInMeasure (fullLaw A b) X atTop x := by
  let _ := fullLaw_probability A b K hK hB
  apply (exists_seq_tendstoInMeasure_atTop_iff hM).mpr
  intro ns hns
  obtain ⟨ms,hms,hAE⟩ := (hX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  exact ⟨ms,hms,(fullLaw_absolutelyContinuous A b).ae_le hAE⟩

include hL hG

theorem targetIntegralQ_eq_crossClass : targetIntegralQ A b K hK hB U g L hL hG=ᵐ[fullLaw A b]
    fun ω => (predictableIntegral U g : (ℝ≥0 → ℝ) → ℝ) ω-crossEnergyClass U U g (actualControlInput A b K hK U) ω := by
  let r := approximation U g L hL hG
  let c := actualControlInput A b K hK U
  let X := fun n ω => outputValue (r n) ω-crossEnergyClass U U (literalPredictableInput (r n)) c ω
  have hM_P (n : ℕ) : AEStronglyMeasurable (X n) sourceLaw :=
    (Lp.aestronglyMeasurable (outputValue (r n))).sub (Lp.aestronglyMeasurable (crossEnergyClass U U (literalPredictableInput (r n)) c))
  have hM_Q (n : ℕ) : AEStronglyMeasurable (X n) (fullLaw A b) :=
    (hM_P n).mono_ac (fullLaw_absolutelyContinuous A b)
  have hX_P : TendstoInMeasure sourceLaw X atTop
      (fun ω => (predictableIntegral U g : (ℝ≥0 → ℝ) → ℝ) ω-crossEnergyClass U U g c ω) :=
    sub_inMeasure sourceLaw _ _ _ _ hM_P
      (tendstoInMeasure_of_tendsto_Lp (approximation_outputs_tendsto U g L hL hG))
      (tendstoInMeasure_of_tendsto_Lp (target_crossEnergy_tendsto A b K hK U g L hL hG))
  have hX_Q := ownQ_inMeasure_of_source A b K hK hB X _ hM_Q hX_P
  have hEq (n : ℕ) : outputValueQ A b K hK hB (r n)=ᵐ[fullLaw A b] X n :=
    (BrownianOwnQSimpleIntegral.simpleIntegral_memLp_two A b K hK hB (r n)).coeFn_toLp.trans
      ((fullLaw_absolutelyContinuous A b).ae_le (literal_integral_shift A b K hK U (r n)))
  have hActual := tendstoInMeasure_of_tendsto_Lp (target_outputs_tendsto A b K hK hB U g L hL hG)
  exact tendstoInMeasure_ae_unique hActual (hX_Q.congr_left (fun n => (hEq n).symm))

theorem targetIntegralQ_eq_actual : targetIntegralQ A b K hK hB U g L hL hG=ᵐ[fullLaw A b]
    fun ω => (predictableIntegral U g : (ℝ≥0 → ℝ) → ℝ) ω-crossTimeEnergy U g (actualControlInput A b K hK U) U ω := by
  apply (targetIntegralQ_eq_crossClass A b K hK hB U g L hL hG).trans
  filter_upwards [(fullLaw_absolutelyContinuous A b).ae_le (crossEnergyClass_coe U U g (actualControlInput A b K hK U))] with ω hc
  rw [hc]

/-- Actual U cross term remains integrable under the SAME fixed Q_A,
from native dtU×Q_A products and the original actual-control readout class. -/
theorem actual_cross_integrable : Integrable (crossTimeEnergy U g (actualControlInput A b K hK U) U) (fullLaw A b) := by
  let _ := fullLaw_probability A b K hK hB
  let c := actualControlInput A b K hK U
  have hc := actualControlInput_bound A b K hK U
  have heP : crossEnergyIntegrand U U g c=ᵐ[inputLaw U]
      fun p => boundedRepresentative U g L p*boundedRepresentative U c K p := by
    filter_upwards [time_support_ae U,representative_ae U g,representative_ae U c,
      boundedRepresentative_ae U g L hG,boundedRepresentative_ae U c K hc] with p ht hrg hrc hcg hcc
    have hp : p∈timeSet U U := by simpa only [timeSet,min_self,Set.mem_prod,Set.mem_univ,and_true] using ht
    rw [crossEnergyIntegrand,Set.indicator_of_mem hp,← hrg,← hrc,hcg,hcc]
  have heQ : crossEnergyIntegrand U U g c=ᵐ[inputLawQ A b U]
      fun p => boundedRepresentative U g L p*boundedRepresentative U c K p :=
    (inputLawQ_absolutelyContinuous A b U).ae_le heP
  have hi : Integrable (crossEnergyIntegrand U U g c) (inputLawQ A b U) :=
    ((targetInput_memLp_two A b K hK hB U g L hL).integrable_mul
      (targetInput_memLp_two A b K hK hB U c K hK)).congr heQ.symm
  exact hi.integral_prod_right

theorem target_baseline_integrable : Integrable (predictableIntegral U g : (ℝ≥0 → ℝ) → ℝ) (fullLaw A b) := by
  have he : (predictableIntegral U g : (ℝ≥0 → ℝ) → ℝ)=ᵐ[fullLaw A b]
      fun ω => targetIntegralQ A b K hK hB U g L hL hG ω+crossTimeEnergy U g (actualControlInput A b K hK U) U ω := by
    filter_upwards [targetIntegralQ_eq_actual A b K hK hB U g L hL hG] with ω h
    rw [h]
    ring
  exact ((targetIntegralQ_integrable A b K hK hB U g L hL hG).add
    (actual_cross_integrable A b K hK hB U g L hL hG)).congr he.symm

/-- Actual baseline test-noise mean at arbitrary U, evaluated under SAME
fixed Q_A; no horizon-dependent normalized law is substituted. -/
theorem target_baseline_mean_eq_cross : (∫ ω, (predictableIntegral U g : (ℝ≥0 → ℝ) → ℝ) ω ∂fullLaw A b)=
    ∫ ω, crossTimeEnergy U g (actualControlInput A b K hK U) U ω ∂fullLaw A b := by
  have he : (predictableIntegral U g : (ℝ≥0 → ℝ) → ℝ)=ᵐ[fullLaw A b]
      fun ω => targetIntegralQ A b K hK hB U g L hL hG ω+crossTimeEnergy U g (actualControlInput A b K hK U) U ω := by
    filter_upwards [targetIntegralQ_eq_actual A b K hK hB U g L hL hG] with ω h
    rw [h]
    ring
  rw [integral_congr_ae he,integral_add (targetIntegralQ_integrable A b K hK hB U g L hL hG)
    (actual_cross_integrable A b K hK hB U g L hL hG),targetIntegralQ_mean_zero A b K hK hB U g L hL hG,zero_add]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQHorizonTargetShift
