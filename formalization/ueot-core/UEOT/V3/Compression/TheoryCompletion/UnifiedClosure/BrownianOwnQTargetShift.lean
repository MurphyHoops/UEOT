import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTargetIntegral
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQCrossDrift

/-!
Original commitment: controlled Ito tests need the actual integral of target g against W_b, with control b defining Q kept fixed.
Existing result: fixed b owns genuine Q/W and target g owns a constructed native Q integral from its SAME bounded finite tables.
Premise reduced: derive I_Qb(g)=I_P(g) minus actual dt cross(g,b), using finite literal shifts and same-source limits.
Model/witness: canonical scalar source, bounded original predictable b,K and g,L on SAME T/original Fs; g may differ from b.
Consumer/boundary: real drift term for actual controlled C2 tests/occupation; no desired Ito/SDE certificate, full-Q density or vector closure assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTargetShift
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianTimeIntegrand BrownianIntegralClosure BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralTimeEnergy BrownianIntegralEnergyL1 BrownianIntegralCrossVariation
open BrownianBoundedPredictableApproximation BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianOwnQTimeInput BrownianOwnQBoundedInput BrownianOwnQTargetIntegral BrownianOwnQCrossDrift
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

variable (T : ℝ≥0) (b : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw T, |(b : Lp ℝ 2 (inputLaw T)) p|≤K)
    (g : fullPredictableL2 T) (L : ℝ) (hL : 0≤L)
    (hG : ∀ᵐ p ∂inputLaw T, |(g : Lp ℝ 2 (inputLaw T)) p|≤L)
include hK hB
/-- Finite actual own-Q absolute continuity transports in-measure limits;
no inverse process or natural-filtration equality is inserted. -/
private theorem ownQ_inMeasure_of_source (X : ℕ → (ℝ≥0 → ℝ) → ℝ) (x : (ℝ≥0 → ℝ) → ℝ)
    (hM : ∀ n, AEStronglyMeasurable (X n) (fullLaw T b)) (hX : TendstoInMeasure sourceLaw X atTop x) :
    TendstoInMeasure (fullLaw T b) X atTop x := by
  let _ := fullLaw_probability T b K hK hB
  apply (exists_seq_tendstoInMeasure_atTop_iff hM).mpr
  intro ns hns
  obtain ⟨ms,hms,hAE⟩ := (hX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  exact ⟨ms,hms,(fullLaw_absolutelyContinuous T b).ae_le hAE⟩


include hL hG
omit hK hB in
/-- Native cross-energy limit is DERIVED for target g's own actual tables,
while b and its actual Q remain fixed. -/
theorem target_crossEnergy_tendsto : Tendsto (fun n => crossEnergyClass T T
      (literalPredictableInput (approximation T g L hL hG n)) b) atTop (𝓝 (crossEnergyClass T T g b)) := by
  simp only [crossEnergyClass,truncate_horizon]
  have hp := (((ContinuousLinearMap.mul ℝ ℝ).holderL (inputLaw T) 2 2 1).continuous₂.tendsto
    ((g : Lp ℝ 2 (inputLaw T)),(b : Lp ℝ 2 (inputLaw T)))).comp
      ((approximation_tendsto T g L hL hG).prodMk_nhds tendsto_const_nhds)
  exact ((timeMarginal T).continuous.tendsto _).comp hp

/-- The actual target Q integral is linked to native P integral and SAME
cross-drift class by two actual limits, not by declaring the target identity. -/
theorem targetIntegralQ_eq_crossClass : targetIntegralQ T b K hK hB g L hL hG=ᵐ[fullLaw T b]
    fun ω => (predictableIntegral T g : (ℝ≥0 → ℝ) → ℝ) ω-crossEnergyClass T T g b ω := by
  let r := approximation T g L hL hG
  let X := fun n ω => outputValue (r n) ω-crossEnergyClass T T (literalPredictableInput (r n)) b ω
  have hM_P (n : ℕ) : AEStronglyMeasurable (X n) sourceLaw :=
    (Lp.aestronglyMeasurable (outputValue (r n))).sub (Lp.aestronglyMeasurable (crossEnergyClass T T (literalPredictableInput (r n)) b))
  have hM_Q (n : ℕ) : AEStronglyMeasurable (X n) (fullLaw T b) :=
    (hM_P n).mono_ac (fullLaw_absolutelyContinuous T b)
  have hX_P : TendstoInMeasure sourceLaw X atTop
      (fun ω => (predictableIntegral T g : (ℝ≥0 → ℝ) → ℝ) ω-crossEnergyClass T T g b ω) :=
    sub_inMeasure sourceLaw _ _ _ _ hM_P
      (tendstoInMeasure_of_tendsto_Lp (approximation_outputs_tendsto T g L hL hG))
      (tendstoInMeasure_of_tendsto_Lp (target_crossEnergy_tendsto T b g L hL hG))
  have hX_Q := ownQ_inMeasure_of_source T b K hK hB X _ hM_Q hX_P
  have hEq (n : ℕ) : outputValueQ T b K hK hB (r n)=ᵐ[fullLaw T b] X n :=
    (BrownianOwnQSimpleIntegral.simpleIntegral_memLp_two T b K hK hB (r n)).coeFn_toLp.trans
      ((fullLaw_absolutelyContinuous T b).ae_le (literal_integral_shift T b K hK hB (r n)))
  have hActual := tendstoInMeasure_of_tendsto_Lp (target_outputs_tendsto T b K hK hB g L hL hG)
  exact tendstoInMeasure_ae_unique hActual (hX_Q.congr_left (fun n => (hEq n).symm))

/-- Actual change-of-integrator formula for bounded target g, with true
same-source dt product of g and deployed b. Q is still b's measure. -/
theorem targetIntegralQ_eq_actual : targetIntegralQ T b K hK hB g L hL hG=ᵐ[fullLaw T b]
    fun ω => (predictableIntegral T g : (ℝ≥0 → ℝ) → ℝ) ω-crossTimeEnergy T g b T ω := by
  apply (targetIntegralQ_eq_crossClass T b K hK hB g L hL hG).trans
  filter_upwards [(fullLaw_absolutelyContinuous T b).ae_le (crossEnergyClass_coe T T g b)] with ω hc
  rw [hc]

/-- Actual dt cross term is integrable under b's OWN Q. This is proved by
the actual dt×Q target/base L2 classes and native Fubini, without a cost field. -/
theorem actual_cross_integrable : Integrable (crossTimeEnergy T g b T) (fullLaw T b) := by
  let _ := fullLaw_probability T b K hK hB
  have heP : crossEnergyIntegrand T T g b=ᵐ[inputLaw T]
      fun p => boundedRepresentative T g L p*boundedRepresentative T b K p := by
    filter_upwards [time_support_ae T,representative_ae T g,representative_ae T b,
      boundedRepresentative_ae T g L hG,boundedRepresentative_ae T b K hB] with p ht hrg hrb hcg hcb
    have hp : p∈timeSet T T := by
      simp only [timeSet,min_self,Set.mem_prod,Set.mem_univ,and_true]
      exact ht
    rw [crossEnergyIntegrand,Set.indicator_of_mem hp,← hrg,← hrb,hcg,hcb]
  have heQ : crossEnergyIntegrand T T g b=ᵐ[inputLawQ T b T]
      fun p => boundedRepresentative T g L p*boundedRepresentative T b K p :=
    (inputLawQ_absolutelyContinuous T b T).ae_le heP
  have hi : Integrable (crossEnergyIntegrand T T g b) (inputLawQ T b T) :=
    ((targetInput_memLp_two T b K hK hB g L hL).integrable_mul
      (boundedInput_memLp_two T b K hK hB)).congr heQ.symm
  exact hi.integral_prod_right

/-- SAME native P baseline integral is genuinely Q-integrable, derived
from the constructed true Q integral and actual cross-drift. -/
theorem target_baseline_integrable : Integrable (predictableIntegral T g : (ℝ≥0 → ℝ) → ℝ) (fullLaw T b) := by
  have he : (predictableIntegral T g : (ℝ≥0 → ℝ) → ℝ)=ᵐ[fullLaw T b]
      fun ω => targetIntegralQ T b K hK hB g L hL hG ω+crossTimeEnergy T g b T ω := by
    filter_upwards [targetIntegralQ_eq_actual T b K hK hB g L hL hG] with ω h
    rw [h]
    ring
  exact ((targetIntegralQ_integrable T b K hK hB g L hL hG).add
    (actual_cross_integrable T b K hK hB g L hL hG)).congr he.symm

/-- Source-derived expectation shift for actual controlled Ito tests.
The drift is evaluated under b's actual final Q, not under P or target g's Q. -/
theorem target_baseline_mean_eq_cross : (∫ ω, (predictableIntegral T g : (ℝ≥0 → ℝ) → ℝ) ω ∂fullLaw T b)=
    ∫ ω, crossTimeEnergy T g b T ω ∂fullLaw T b := by
  have he : (predictableIntegral T g : (ℝ≥0 → ℝ) → ℝ)=ᵐ[fullLaw T b]
      fun ω => targetIntegralQ T b K hK hB g L hL hG ω+crossTimeEnergy T g b T ω := by
    filter_upwards [targetIntegralQ_eq_actual T b K hK hB g L hL hG] with ω h
    rw [h]
    ring
  rw [integral_congr_ae he,integral_add (targetIntegralQ_integrable T b K hK hB g L hL hG)
    (actual_cross_integrable T b K hK hB g L hL hG),targetIntegralQ_mean_zero T b K hK hB g L hL hG,zero_add]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTargetShift
