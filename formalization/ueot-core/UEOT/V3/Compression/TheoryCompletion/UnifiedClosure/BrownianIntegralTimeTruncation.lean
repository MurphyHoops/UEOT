import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPredictableDensity
import Mathlib.MeasureTheory.Function.Holder

/-!
Original commitment: the actual stochastic integral needs a same-source time-indexed consumer, not only a terminal map.
Existing result: actual native continuous linear isometry on full predictable L2 at one fixed horizon T.
Premise reduced: construct genuine predictable cutoff inputs and their literal integral classes on that SAME time measure.
Model/witness: original inputLaw T, original natural filtration and sourceLaw; all times including horizon zero.
Consumer: actual conditional-expectation/martingale bridge; continuity of paths and general Ito remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralTimeTruncation
open MeasureTheory ProbabilityTheory Set
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Fixed-horizon time cutoff; there is no new horizon measure or new noise. -/
def timeSet (T s : ℝ≥0) : Set (ℝ × (ℝ≥0 → ℝ)) := Ioc (0 : ℝ) (min s T : ℝ≥0) ×ˢ univ

theorem timeSet_predictable (T s : ℝ≥0) : MeasurableSet[predictableSigma] (timeSet T s) :=
  predictable_interval_rectangle 0 (min s T) MeasurableSet.univ

theorem timeSet_measurable (T s : ℝ≥0) : MeasurableSet (timeSet T s) :=
  predictableSigma_le _ (timeSet_predictable T s)

private def cutoffClass (T s : ℝ≥0) : Lp ℝ ∞ (inputLaw T) :=
  ((memLp_top_const (μ := inputLaw T) (1 : ℝ)).indicator (timeSet_measurable T s)).toLp
    ((timeSet T s).indicator (fun _ => (1 : ℝ)))

/-- Native Holder multiplication by the actual L-infinity indicator. -/
def truncateAmbient (T s : ℝ≥0) : Lp ℝ 2 (inputLaw T) →L[ℝ] Lp ℝ 2 (inputLaw T) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (inputLaw T) ∞ 2 2 (cutoffClass T s)

theorem truncateAmbient_coe (T s : ℝ≥0) (f : Lp ℝ 2 (inputLaw T)) :
    truncateAmbient T s f =ᵐ[inputLaw T] (timeSet T s).indicator f := by
  have hc := ((memLp_top_const (μ := inputLaw T) (1 : ℝ)).indicator (timeSet_measurable T s)).coeFn_toLp
  have hh := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (cutoffClass T s) f
  apply hh.trans
  filter_upwards [hc] with p hp
  change cutoffClass T s p * f p = (timeSet T s).indicator f p
  change cutoffClass T s p = _ at hp
  rw [hp]
  by_cases ht : p ∈ timeSet T s <;> simp [ht]

theorem truncateAmbient_predictable (T s : ℝ≥0) (f : fullPredictableL2 T) :
    truncateAmbient T s f ∈ fullPredictableL2 T := by
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  have hf : AEStronglyMeasurable[predictableSigma] (f : Lp ℝ 2 (inputLaw T)) (inputLaw T) :=
    mem_lpMeas_iff_aestronglyMeasurable.mp f.property
  refine ⟨(timeSet T s).indicator (hf.mk (f : Lp ℝ 2 (inputLaw T))),
    hf.stronglyMeasurable_mk.indicator (timeSet_predictable T s),?_⟩
  filter_upwards [truncateAmbient_coe T s f,hf.ae_eq_mk] with p hp hfp
  rw [hp]
  by_cases ht : p ∈ timeSet T s <;> simp [ht,hfp]

/-- Actual cutoff operator on the independently defined full predictable L2. -/
def truncate (T s : ℝ≥0) : fullPredictableL2 T →L[ℝ] fullPredictableL2 T :=
  ((truncateAmbient T s).comp (fullPredictableL2 T).subtypeL).codRestrict
    (fullPredictableL2 T) (truncateAmbient_predictable T s)

theorem truncate_coe (T s : ℝ≥0) (f : fullPredictableL2 T) :
    (truncate T s f : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T] (timeSet T s).indicator (f : Lp ℝ 2 (inputLaw T)) :=
  truncateAmbient_coe T s f

/-- The actual cutoff is a contraction in the original product-measure L2. -/
theorem truncate_norm_le (T s : ℝ≥0) (f : fullPredictableL2 T) : ‖truncate T s f‖ ≤ ‖f‖ := by
  change ‖(truncate T s f : Lp ℝ 2 (inputLaw T))‖ ≤ ‖(f : Lp ℝ 2 (inputLaw T))‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [truncate_coe T s f] with p hp
  rw [hp]
  by_cases ht : p ∈ timeSet T s <;> simp [ht]

theorem truncate_zero (T : ℝ≥0) (f : fullPredictableL2 T) : truncate T 0 f = 0 := by
  apply Subtype.ext
  change (truncate T 0 f : Lp ℝ 2 (inputLaw T)) = 0
  apply Lp.ext
  filter_upwards [truncate_coe T 0 f,Lp.coeFn_zero ℝ 2 (inputLaw T)] with p hp hz
  rw [hp,hz]
  simp [timeSet]

theorem truncate_horizon (T : ℝ≥0) (f : fullPredictableL2 T) : truncate T T f = f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [truncate_coe T T f,time_support_ae T] with p hp ht
  rw [hp]
  exact Set.indicator_of_mem (by simpa only [timeSet,min_self,mem_prod,mem_univ,and_true] using ht) _

/-- Actual time-indexed integral CLASS, defined by the existing full integral
of the literal cutoff input. Exact adapted representatives are a later bridge. -/
def integralClassProcess (T : ℝ≥0) (f : fullPredictableL2 T) (s : ℝ≥0) : Lp ℝ 2 sourceLaw :=
  predictableIntegral T (truncate T s f)

theorem integralClassProcess_zero (T : ℝ≥0) (f : fullPredictableL2 T) : integralClassProcess T f 0 = 0 := by
  rw [integralClassProcess,truncate_zero,map_zero]

theorem integralClassProcess_horizon (T : ℝ≥0) (f : fullPredictableL2 T) :
    integralClassProcess T f T = predictableIntegral T f := by
  rw [integralClassProcess,truncate_horizon]

theorem integralClassProcess_norm_le (T s : ℝ≥0) (f : fullPredictableL2 T) :
    ‖integralClassProcess T f s‖ ≤ ‖f‖ := by
  rw [integralClassProcess,predictableIntegral_norm]
  exact truncate_norm_le T s f

private theorem lp_norm_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ a, f a ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

/-- Exact second energy of the actual truncated integral, under the SAME
fixed inputLaw. No quadratic-variation or continuous-path premise is inserted. -/
theorem integralClassProcess_energy (T s : ℝ≥0) (f : fullPredictableL2 T) :
    (∫ ω, integralClassProcess T f s ω ^ 2 ∂sourceLaw) =
      ∫ p in timeSet T s, (f : Lp ℝ 2 (inputLaw T)) p ^ 2 ∂inputLaw T := by
  rw [← lp_norm_sq sourceLaw (integralClassProcess T f s)]
  rw [integralClassProcess,predictableIntegral_norm]
  change ‖(truncate T s f : Lp ℝ 2 (inputLaw T))‖ ^ 2 = _
  rw [lp_norm_sq (inputLaw T) (truncate T s f)]
  have he : (fun p => (truncate T s f : Lp ℝ 2 (inputLaw T)) p ^ 2) =ᵐ[inputLaw T]
      (timeSet T s).indicator (fun p => (f : Lp ℝ 2 (inputLaw T)) p ^ 2) := by
    filter_upwards [truncate_coe T s f] with p hp
    rw [hp]
    by_cases ht : p ∈ timeSet T s <;> simp [ht]
  rw [integral_congr_ae he,integral_indicator (timeSet_measurable T s)]

/-- Each time evaluation is itself the ACTUAL native continuous linear map,
feeding the conditional-expectation/dense-extension bridge. -/
def integralAt (T s : ℝ≥0) : fullPredictableL2 T →L[ℝ] Lp ℝ 2 sourceLaw :=
  (predictableIntegral T).comp (truncate T s)

theorem integralAt_apply (T s : ℝ≥0) (f : fullPredictableL2 T) :
    integralAt T s f = integralClassProcess T f s := rfl

theorem integralAt_norm_le_one (T s : ℝ≥0) : ‖integralAt T s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  rw [one_mul]
  exact integralClassProcess_norm_le T s f

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralTimeTruncation
